import V185TrunkScan23Chunk0573

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3393892 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_3393892 : Nat := 118140960795 + 3393892 * 2 ^ 59
def prefixEnd_3393892 : Nat := 4983230072969 + 3 ^ 40 * 3393892 * 2
def baseEnd_3393892 : Nat := 1742697885449140615641781

theorem tailTrace_3393892 : CollatzResearch.WordTrace tailWord_3393892 prefixEnd_3393892 1742697885449140615641781 := by
  unfold tailWord_3393892
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892705310258194725979965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82523607080344259634639953 61892705310258194725979965)
  ·
    refine ⟨23209764491346823022242487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61892705310258194725979965 23209764491346823022242487)
    ·
      refine ⟨34814646737020234533363731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23209764491346823022242487 34814646737020234533363731)
      ·
        refine ⟨52221970105530351800045597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34814646737020234533363731 52221970105530351800045597)
        ·
          refine ⟨19583238789573881925017099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52221970105530351800045597 19583238789573881925017099)
          ·
            refine ⟨29374858184360822887525649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19583238789573881925017099 29374858184360822887525649)
            ·
              refine ⟨22031143638270617165644237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29374858184360822887525649 22031143638270617165644237)
              ·
                refine ⟨8261678864351481437116589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22031143638270617165644237 8261678864351481437116589)
                ·
                  refine ⟨3098129574131805538918721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8261678864351481437116589 3098129574131805538918721)
                  ·
                    refine ⟨2323597180598854154189041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3098129574131805538918721 2323597180598854154189041)
                    ·
                      refine ⟨1742697885449140615641781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323597180598854154189041 1742697885449140615641781)
                      ·
                        rfl

theorem cell23_3393892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_3393892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393892 prefixEnd_3393892 := by exact prefixLift 3393892
  have htrace : WordTrace (prefixWord ++ tailWord_3393892) baseStart_3393892 baseEnd_3393892 := by
    simpa [prefixWord, tailWord_3393892, baseEnd_3393892] using wordTrace_append hprefix tailTrace_3393892
  have hstable : (prefixWord ++ tailWord_3393892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393892).length < 2 ^ (prefixWord ++ tailWord_3393892).sum := by decide
  have hdescent : baseEnd_3393892 < baseStart_3393892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393895 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3393895 : Nat := 118140960795 + 3393895 * 2 ^ 59
def prefixEnd_3393895 : Nat := 4983230072969 + 3 ^ 40 * 3393895 * 2
def baseEnd_3393895 : Nat := 1742699425891104103904267

theorem tailTrace_3393895 : CollatzResearch.WordTrace tailWord_3393895 prefixEnd_3393895 1742699425891104103904267 := by
  unfold tailWord_3393895
  simp only [CollatzResearch.WordTrace]
  refine ⟨123785520039505520964319139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82523680026337013976212759 123785520039505520964319139)
  ·
    refine ⟨185678280059258281446478709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123785520039505520964319139 185678280059258281446478709)
    ·
      refine ⟨17407338755555463885607379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185678280059258281446478709 17407338755555463885607379)
      ·
        refine ⟨26111008133333195828411069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17407338755555463885607379 26111008133333195828411069)
        ·
          refine ⟨9791628049999948435654151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26111008133333195828411069 9791628049999948435654151)
          ·
            refine ⟨14687442074999922653481227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791628049999948435654151 14687442074999922653481227)
            ·
              refine ⟨22031163112499883980221841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687442074999922653481227 22031163112499883980221841)
              ·
                refine ⟨16523372334374912985166381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22031163112499883980221841 16523372334374912985166381)
                ·
                  refine ⟨6196264625390592369437393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16523372334374912985166381 6196264625390592369437393)
                  ·
                    refine ⟨4647198469042944277078045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196264625390592369437393 4647198469042944277078045)
                    ·
                      refine ⟨1742699425891104103904267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647198469042944277078045 1742699425891104103904267)
                      ·
                        rfl

theorem cell23_3393895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3393895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393895 prefixEnd_3393895 := by exact prefixLift 3393895
  have htrace : WordTrace (prefixWord ++ tailWord_3393895) baseStart_3393895 baseEnd_3393895 := by
    simpa [prefixWord, tailWord_3393895, baseEnd_3393895] using wordTrace_append hprefix tailTrace_3393895
  have hstable : (prefixWord ++ tailWord_3393895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393895).length < 2 ^ (prefixWord ++ tailWord_3393895).sum := by decide
  have hdescent : baseEnd_3393895 < baseStart_3393895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393909 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3393909 : Nat := 118140960795 + 3393909 * 2 ^ 59
def prefixEnd_3393909 : Nat := 4983230072969 + 3 ^ 40 * 3393909 * 2
def baseEnd_3393909 : Nat := 1742706614620267049129203

theorem tailTrace_3393909 : CollatzResearch.WordTrace tailWord_3393909 prefixEnd_3393909 1742706614620267049129203 := by
  unfold tailWord_3393909
  simp only [CollatzResearch.WordTrace]
  refine ⟨123786030661454801355328781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82524020440969867570219187 123786030661454801355328781)
  ·
    refine ⟨46419761498045550508248293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123786030661454801355328781 46419761498045550508248293)
    ·
      refine ⟨8703705280883540720296555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46419761498045550508248293 8703705280883540720296555)
      ·
        refine ⟨13055557921325311080444833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703705280883540720296555 13055557921325311080444833)
        ·
          refine ⟨9791668440993983310333625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13055557921325311080444833 9791668440993983310333625)
          ·
            refine ⟨7343751330745487482750219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791668440993983310333625 7343751330745487482750219)
            ·
              refine ⟨11015626996118231224125329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343751330745487482750219 11015626996118231224125329)
              ·
                refine ⟨8261720247088673418093997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11015626996118231224125329 8261720247088673418093997)
                ·
                  refine ⟨3098145092658252531785249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8261720247088673418093997 3098145092658252531785249)
                  ·
                    refine ⟨2323608819493689398838937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3098145092658252531785249 2323608819493689398838937)
                    ·
                      refine ⟨1742706614620267049129203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323608819493689398838937 1742706614620267049129203)
                      ·
                        rfl

theorem cell23_3393909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3393909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393909 prefixEnd_3393909 := by exact prefixLift 3393909
  have htrace : WordTrace (prefixWord ++ tailWord_3393909) baseStart_3393909 baseEnd_3393909 := by
    simpa [prefixWord, tailWord_3393909, baseEnd_3393909] using wordTrace_append hprefix tailTrace_3393909
  have hstable : (prefixWord ++ tailWord_3393909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393909).length < 2 ^ (prefixWord ++ tailWord_3393909).sum := by decide
  have hdescent : baseEnd_3393909 < baseStart_3393909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393925 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_3393925 : Nat := 118140960795 + 3393925 * 2 ^ 59
def prefixEnd_3393925 : Nat := 4983230072969 + 3 ^ 40 * 3393925 * 2
def baseEnd_3393925 : Nat := 1742714830310738986529129

theorem tailTrace_3393925 : CollatzResearch.WordTrace tailWord_3393925 prefixEnd_3393925 1742714830310738986529129 := by
  unfold tailWord_3393925
  simp only [CollatzResearch.WordTrace]
  refine ⟨123786614229396836087911229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82524409486264557391940819 123786614229396836087911229)
  ·
    refine ⟨46419980336023813532966711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123786614229396836087911229 46419980336023813532966711)
    ·
      refine ⟨69629970504035720299450067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46419980336023813532966711 69629970504035720299450067)
      ·
        refine ⟨104444955756053580449175101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69629970504035720299450067 104444955756053580449175101)
        ·
          refine ⟨39166858408520092668440663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104444955756053580449175101 39166858408520092668440663)
          ·
            refine ⟨58750287612780139002660995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39166858408520092668440663 58750287612780139002660995)
            ·
              refine ⟨88125431419170208503991493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58750287612780139002660995 88125431419170208503991493)
              ·
                refine ⟨16523518391094414094498405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88125431419170208503991493 16523518391094414094498405)
                ·
                  refine ⟨3098159698330202642718451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16523518391094414094498405 3098159698330202642718451)
                  ·
                    refine ⟨4647239547495303964077677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098159698330202642718451 4647239547495303964077677)
                    ·
                      refine ⟨1742714830310738986529129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647239547495303964077677 1742714830310738986529129)
                      ·
                        rfl

theorem cell23_3393925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_3393925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393925 prefixEnd_3393925 := by exact prefixLift 3393925
  have htrace : WordTrace (prefixWord ++ tailWord_3393925) baseStart_3393925 baseEnd_3393925 := by
    simpa [prefixWord, tailWord_3393925, baseEnd_3393925] using wordTrace_append hprefix tailTrace_3393925
  have hstable : (prefixWord ++ tailWord_3393925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393925).length < 2 ^ (prefixWord ++ tailWord_3393925).sum := by decide
  have hdescent : baseEnd_3393925 < baseStart_3393925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393929 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 1, 2, 3]
def baseStart_3393929 : Nat := 118140960795 + 3393929 * 2 ^ 59
def prefixEnd_3393929 : Nat := 4983230072969 + 3 ^ 40 * 3393929 * 2
def baseEnd_3393929 : Nat := 1742716884233356970879111

theorem tailTrace_3393929 : CollatzResearch.WordTrace tailWord_3393929 prefixEnd_3393929 1742716884233356970879111 := by
  unfold tailWord_3393929
  simp only [CollatzResearch.WordTrace]
  refine ⟨123786760121382344771056841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82524506747588229847371227 123786760121382344771056841)
  ·
    refine ⟨92840070091036758578292631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123786760121382344771056841 92840070091036758578292631)
    ·
      refine ⟨139260105136555137867438947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92840070091036758578292631 139260105136555137867438947)
      ·
        refine ⟨208890157704832706801158421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139260105136555137867438947 208890157704832706801158421)
        ·
          refine ⟨9791726142414033131304301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208890157704832706801158421 9791726142414033131304301)
          ·
            refine ⟨3671897303405262424239113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9791726142414033131304301 3671897303405262424239113)
            ·
              refine ⟨2753922977553946818179335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671897303405262424239113 2753922977553946818179335)
              ·
                refine ⟨4130884466330920227269003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753922977553946818179335 4130884466330920227269003)
                ·
                  refine ⟨6196326699496380340903505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130884466330920227269003 6196326699496380340903505)
                  ·
                    refine ⟨4647245024622285255677629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196326699496380340903505 4647245024622285255677629)
                    ·
                      refine ⟨1742716884233356970879111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647245024622285255677629 1742716884233356970879111)
                      ·
                        rfl

theorem cell23_3393929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 2, 3].length) (baseStart_3393929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393929 prefixEnd_3393929 := by exact prefixLift 3393929
  have htrace : WordTrace (prefixWord ++ tailWord_3393929) baseStart_3393929 baseEnd_3393929 := by
    simpa [prefixWord, tailWord_3393929, baseEnd_3393929] using wordTrace_append hprefix tailTrace_3393929
  have hstable : (prefixWord ++ tailWord_3393929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393929).length < 2 ^ (prefixWord ++ tailWord_3393929).sum := by decide
  have hdescent : baseEnd_3393929 < baseStart_3393929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393968 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_3393968 : Nat := 118140960795 + 3393968 * 2 ^ 59
def prefixEnd_3393968 : Nat := 4983230072969 + 3 ^ 40 * 3393968 * 2
def baseEnd_3393968 : Nat := 1742736909978882318291431

theorem tailTrace_3393968 : CollatzResearch.WordTrace tailWord_3393968 prefixEnd_3393968 1742736909978882318291431 := by
  unfold tailWord_3393968
  simp only [CollatzResearch.WordTrace]
  refine ⟨61894091284120527215863279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82525455045494036287817705 61894091284120527215863279)
  ·
    refine ⟨92841136926180790823794919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61894091284120527215863279 92841136926180790823794919)
    ·
      refine ⟨139261705389271186235692379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92841136926180790823794919 139261705389271186235692379)
      ·
        refine ⟨208892558083906779353538569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139261705389271186235692379 208892558083906779353538569)
        ·
          refine ⟨156669418562930084515153927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208892558083906779353538569 156669418562930084515153927)
          ·
            refine ⟨235004127844395126772730891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156669418562930084515153927 235004127844395126772730891)
            ·
              refine ⟨352506191766592690159096337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235004127844395126772730891 352506191766592690159096337)
              ·
                refine ⟨264379643824944517619322253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352506191766592690159096337 264379643824944517619322253)
                ·
                  refine ⟨99142366434354194107245845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264379643824944517619322253 99142366434354194107245845)
                  ·
                    refine ⟨4647298426610352848777149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99142366434354194107245845 4647298426610352848777149)
                    ·
                      refine ⟨1742736909978882318291431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647298426610352848777149 1742736909978882318291431)
                      ·
                        rfl

theorem cell23_3393968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_3393968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393968 prefixEnd_3393968 := by exact prefixLift 3393968
  have htrace : WordTrace (prefixWord ++ tailWord_3393968) baseStart_3393968 baseEnd_3393968 := by
    simpa [prefixWord, tailWord_3393968, baseEnd_3393968] using wordTrace_append hprefix tailTrace_3393968
  have hstable : (prefixWord ++ tailWord_3393968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393968).length < 2 ^ (prefixWord ++ tailWord_3393968).sum := by decide
  have hdescent : baseEnd_3393968 < baseStart_3393968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393969 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3393969 : Nat := 118140960795 + 3393969 * 2 ^ 59
def prefixEnd_3393969 : Nat := 4983230072969 + 3 ^ 40 * 3393969 * 2
def baseEnd_3393969 : Nat := 1742737423459536814378927

theorem tailTrace_3393969 : CollatzResearch.WordTrace tailWord_3393969 prefixEnd_3393969 1742737423459536814378927 := by
  unfold tailWord_3393969
  simp only [CollatzResearch.WordTrace]
  refine ⟨123788219041237431602512961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82525479360824954401675307 123788219041237431602512961)
  ·
    refine ⟨92841164280928073701884721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123788219041237431602512961 92841164280928073701884721)
    ·
      refine ⟨69630873210696055276413541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92841164280928073701884721 69630873210696055276413541)
      ·
        refine ⟨13055788727005510364327539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69630873210696055276413541 13055788727005510364327539)
        ·
          refine ⟨19583683090508265546491309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055788727005510364327539 19583683090508265546491309)
          ·
            refine ⟨7343881158940599579934241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19583683090508265546491309 7343881158940599579934241)
            ·
              refine ⟨5507910869205449684950681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343881158940599579934241 5507910869205449684950681)
              ·
                refine ⟨4130933151904087263713011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507910869205449684950681 4130933151904087263713011)
                ·
                  refine ⟨6196399727856130895569517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130933151904087263713011 6196399727856130895569517)
                  ·
                    refine ⟨2323649897946049085838569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6196399727856130895569517 2323649897946049085838569)
                    ·
                      refine ⟨1742737423459536814378927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323649897946049085838569 1742737423459536814378927)
                      ·
                        rfl

theorem cell23_3393969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3393969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393969 prefixEnd_3393969 := by exact prefixLift 3393969
  have htrace : WordTrace (prefixWord ++ tailWord_3393969) baseStart_3393969 baseEnd_3393969 := by
    simpa [prefixWord, tailWord_3393969, baseEnd_3393969] using wordTrace_append hprefix tailTrace_3393969
  have hstable : (prefixWord ++ tailWord_3393969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393969).length < 2 ^ (prefixWord ++ tailWord_3393969).sum := by decide
  have hdescent : baseEnd_3393969 < baseStart_3393969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393978 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3393978 : Nat := 118140960795 + 3393978 * 2 ^ 59
def prefixEnd_3393978 : Nat := 4983230072969 + 3 ^ 40 * 3393978 * 2
def baseEnd_3393978 : Nat := 1742742044785427279166385

theorem tailTrace_3393978 : CollatzResearch.WordTrace tailWord_3393978 prefixEnd_3393978 1742742044785427279166385 := by
  unfold tailWord_3393978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30947136824551206534897647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82525698198803217426393725 30947136824551206534897647)
  ·
    refine ⟨46420705236826809802346471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30947136824551206534897647 46420705236826809802346471)
    ·
      refine ⟨69631057855240214703519707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46420705236826809802346471 69631057855240214703519707)
      ·
        refine ⟨104446586782860322055279561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69631057855240214703519707 104446586782860322055279561)
        ·
          refine ⟨78334940087145241541459671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104446586782860322055279561 78334940087145241541459671)
          ·
            refine ⟨117502410130717862312189507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78334940087145241541459671 117502410130717862312189507)
            ·
              refine ⟨176253615196076793468284261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117502410130717862312189507 176253615196076793468284261)
              ·
                refine ⟨33047552849264398775303299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176253615196076793468284261 33047552849264398775303299)
                ·
                  refine ⟨49571329273896598162954949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33047552849264398775303299 49571329273896598162954949)
                  ·
                    refine ⟨9294624238855612155554053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49571329273896598162954949 9294624238855612155554053)
                    ·
                      refine ⟨1742742044785427279166385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9294624238855612155554053 1742742044785427279166385)
                      ·
                        rfl

theorem cell23_3393978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3393978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393978 prefixEnd_3393978 := by exact prefixLift 3393978
  have htrace : WordTrace (prefixWord ++ tailWord_3393978) baseStart_3393978 baseEnd_3393978 := by
    simpa [prefixWord, tailWord_3393978, baseEnd_3393978] using wordTrace_append hprefix tailTrace_3393978
  have hstable : (prefixWord ++ tailWord_3393978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393978).length < 2 ^ (prefixWord ++ tailWord_3393978).sum := by decide
  have hdescent : baseEnd_3393978 < baseStart_3393978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393982 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_3393982 : Nat := 118140960795 + 3393982 * 2 ^ 59
def prefixEnd_3393982 : Nat := 4983230072969 + 3 ^ 40 * 3393982 * 2
def baseEnd_3393982 : Nat := 1742744098708045263516367

theorem tailTrace_3393982 : CollatzResearch.WordTrace tailWord_3393982 prefixEnd_3393982 1742744098708045263516367 := by
  unfold tailWord_3393982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473586648773791852842025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82525795460126889881824133 15473586648773791852842025)
  ·
    refine ⟨11605189986580343889631519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15473586648773791852842025 11605189986580343889631519)
    ·
      refine ⟨17407784979870515834447279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11605189986580343889631519 17407784979870515834447279)
      ·
        refine ⟨26111677469805773751670919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17407784979870515834447279 26111677469805773751670919)
        ·
          refine ⟨39167516204708660627506379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26111677469805773751670919 39167516204708660627506379)
          ·
            refine ⟨58751274307062990941259569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39167516204708660627506379 58751274307062990941259569)
            ·
              refine ⟨44063455730297243205944677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58751274307062990941259569 44063455730297243205944677)
              ·
                refine ⟨8261897949430733101114627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44063455730297243205944677 8261897949430733101114627)
                ·
                  refine ⟨12392846924146099651671941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261897949430733101114627 12392846924146099651671941)
                  ·
                    refine ⟨2323658798277393684688489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12392846924146099651671941 2323658798277393684688489)
                    ·
                      refine ⟨1742744098708045263516367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323658798277393684688489 1742744098708045263516367)
                      ·
                        rfl

theorem cell23_3393982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_3393982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393982 prefixEnd_3393982 := by exact prefixLift 3393982
  have htrace : WordTrace (prefixWord ++ tailWord_3393982) baseStart_3393982 baseEnd_3393982 := by
    simpa [prefixWord, tailWord_3393982, baseEnd_3393982] using wordTrace_append hprefix tailTrace_3393982
  have hstable : (prefixWord ++ tailWord_3393982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393982).length < 2 ^ (prefixWord ++ tailWord_3393982).sum := by decide
  have hdescent : baseEnd_3393982 < baseStart_3393982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393998 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3393998 : Nat := 118140960795 + 3393998 * 2 ^ 59
def prefixEnd_3393998 : Nat := 4983230072969 + 3 ^ 40 * 3393998 * 2
def baseEnd_3393998 : Nat := 1742752314398517200916293

theorem tailTrace_3393998 : CollatzResearch.WordTrace tailWord_3393998 prefixEnd_3393998 1742752314398517200916293 := by
  unfold tailWord_3393998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473659594766546194414831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82526184505421579703545765 15473659594766546194414831)
  ·
    refine ⟨23210489392149819291622247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15473659594766546194414831 23210489392149819291622247)
    ·
      refine ⟨34815734088224728937433371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23210489392149819291622247 34815734088224728937433371)
      ·
        refine ⟨52223601132337093406150057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34815734088224728937433371 52223601132337093406150057)
        ·
          refine ⟨39167700849252820054612543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52223601132337093406150057 39167700849252820054612543)
          ·
            refine ⟨58751551273879230081918815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39167700849252820054612543 58751551273879230081918815)
            ·
              refine ⟨88127326910818845122878223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58751551273879230081918815 88127326910818845122878223)
              ·
                refine ⟨132190990366228267684317335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88127326910818845122878223 132190990366228267684317335)
                ·
                  refine ⟨198286485549342401526476003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132190990366228267684317335 198286485549342401526476003)
                  ·
                    refine ⟨297429728324013602289714005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198286485549342401526476003 297429728324013602289714005)
                    ·
                      refine ⟨1742752314398517200916293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 297429728324013602289714005 1742752314398517200916293)
                      ·
                        rfl

theorem cell23_3393998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3393998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393998 prefixEnd_3393998 := by exact prefixLift 3393998
  have htrace : WordTrace (prefixWord ++ tailWord_3393998) baseStart_3393998 baseEnd_3393998 := by
    simpa [prefixWord, tailWord_3393998, baseEnd_3393998] using wordTrace_append hprefix tailTrace_3393998
  have hstable : (prefixWord ++ tailWord_3393998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393998).length < 2 ^ (prefixWord ++ tailWord_3393998).sum := by decide
  have hdescent : baseEnd_3393998 < baseStart_3393998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394005 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 7]
def baseStart_3394005 : Nat := 118140960795 + 3394005 * 2 ^ 59
def prefixEnd_3394005 : Nat := 4983230072969 + 3 ^ 40 * 3394005 * 2
def baseEnd_3394005 : Nat := 193639545418122074836529

theorem tailTrace_3394005 : CollatzResearch.WordTrace tailWord_3394005 prefixEnd_3394005 193639545418122074836529 := by
  unfold tailWord_3394005
  simp only [CollatzResearch.WordTrace]
  refine ⟨123789532069107009750823469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82526354712738006500548979 123789532069107009750823469)
  ·
    refine ⟨46421074525915128656558801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123789532069107009750823469 46421074525915128656558801)
    ·
      refine ⟨34815805894436346492419101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46421074525915128656558801 34815805894436346492419101)
      ·
        refine ⟨13055927210413629934657163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34815805894436346492419101 13055927210413629934657163)
        ·
          refine ⟨19583890815620444901985745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055927210413629934657163 19583890815620444901985745)
          ·
            refine ⟨14687918111715333676489309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19583890815620444901985745 14687918111715333676489309)
            ·
              refine ⟨5507969291893250128683491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14687918111715333676489309 5507969291893250128683491)
              ·
                refine ⟨8261953937839875193025237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507969291893250128683491 8261953937839875193025237)
                ·
                  refine ⟨193639545418122074836529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8261953937839875193025237 193639545418122074836529)
                  ·
                    rfl

theorem cell23_3394005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_3394005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394005 prefixEnd_3394005 := by exact prefixLift 3394005
  have htrace : WordTrace (prefixWord ++ tailWord_3394005) baseStart_3394005 baseEnd_3394005 := by
    simpa [prefixWord, tailWord_3394005, baseEnd_3394005] using wordTrace_append hprefix tailTrace_3394005
  have hstable : (prefixWord ++ tailWord_3394005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394005).length < 2 ^ (prefixWord ++ tailWord_3394005).sum := by decide
  have hdescent : baseEnd_3394005 < baseStart_3394005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394025 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 5, 2]
def baseStart_3394025 : Nat := 118140960795 + 3394025 * 2 ^ 59
def prefixEnd_3394025 : Nat := 4983230072969 + 3 ^ 40 * 3394025 * 2
def baseEnd_3394025 : Nat := 1742766178376188595278669

theorem tailTrace_3394025 : CollatzResearch.WordTrace tailWord_3394025 prefixEnd_3394025 1742766178376188595278669 := by
  unfold tailWord_3394025
  simp only [CollatzResearch.WordTrace]
  refine ⟨123790261529034553166551529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82526841019356368777701019 123790261529034553166551529)
  ·
    refine ⟨92842696146775914874913647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123790261529034553166551529 92842696146775914874913647)
    ·
      refine ⟨139264044220163872312370471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92842696146775914874913647 139264044220163872312370471)
      ·
        refine ⟨208896066330245808468555707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139264044220163872312370471 208896066330245808468555707)
        ·
          refine ⟨313344099495368712702833561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208896066330245808468555707 313344099495368712702833561)
          ·
            refine ⟨235008074621526534527125171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313344099495368712702833561 235008074621526534527125171)
            ·
              refine ⟨352512111932289801790687757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235008074621526534527125171 352512111932289801790687757)
              ·
                refine ⟨132192041974608675671507909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352512111932289801790687757 132192041974608675671507909)
                ·
                  refine ⟨24786007870239126688407733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132192041974608675671507909 24786007870239126688407733)
                  ·
                    refine ⟨2323688237834918127038225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24786007870239126688407733 2323688237834918127038225)
                    ·
                      refine ⟨1742766178376188595278669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323688237834918127038225 1742766178376188595278669)
                      ·
                        rfl

theorem cell23_3394025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5, 2].length) (baseStart_3394025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394025 prefixEnd_3394025 := by exact prefixLift 3394025
  have htrace : WordTrace (prefixWord ++ tailWord_3394025) baseStart_3394025 baseEnd_3394025 := by
    simpa [prefixWord, tailWord_3394025, baseEnd_3394025] using wordTrace_append hprefix tailTrace_3394025
  have hstable : (prefixWord ++ tailWord_3394025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394025).length < 2 ^ (prefixWord ++ tailWord_3394025).sum := by decide
  have hdescent : baseEnd_3394025 < baseStart_3394025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394028 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3394028 : Nat := 118140960795 + 3394028 * 2 ^ 59
def prefixEnd_3394028 : Nat := 4983230072969 + 3 ^ 40 * 3394028 * 2
def baseEnd_3394028 : Nat := 1742767718818152083541155

theorem tailTrace_3394028 : CollatzResearch.WordTrace tailWord_3394028 prefixEnd_3394028 1742767718818152083541155 := by
  unfold tailWord_3394028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61895185474011842339455369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82526913965349123119273825 61895185474011842339455369)
  ·
    refine ⟨46421389105508881754591527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61895185474011842339455369 46421389105508881754591527)
    ·
      refine ⟨69632083658263322631887291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46421389105508881754591527 69632083658263322631887291)
      ·
        refine ⟨104448125487394983947830937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69632083658263322631887291 104448125487394983947830937)
        ·
          refine ⟨78336094115546237960873203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104448125487394983947830937 78336094115546237960873203)
          ·
            refine ⟨117504141173319356941309805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78336094115546237960873203 117504141173319356941309805)
            ·
              refine ⟨44064052939994758852991177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117504141173319356941309805 44064052939994758852991177)
              ·
                refine ⟨33048039704996069139743383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44064052939994758852991177 33048039704996069139743383)
                ·
                  refine ⟨49572059557494103709615075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33048039704996069139743383 49572059557494103709615075)
                  ·
                    refine ⟨74358089336241155564422613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49572059557494103709615075 74358089336241155564422613)
                    ·
                      refine ⟨1742767718818152083541155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74358089336241155564422613 1742767718818152083541155)
                      ·
                        rfl

theorem cell23_3394028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3394028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394028 prefixEnd_3394028 := by exact prefixLift 3394028
  have htrace : WordTrace (prefixWord ++ tailWord_3394028) baseStart_3394028 baseEnd_3394028 := by
    simpa [prefixWord, tailWord_3394028, baseEnd_3394028] using wordTrace_append hprefix tailTrace_3394028
  have hstable : (prefixWord ++ tailWord_3394028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394028).length < 2 ^ (prefixWord ++ tailWord_3394028).sum := by decide
  have hdescent : baseEnd_3394028 < baseStart_3394028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394035 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 2, 5]
def baseStart_3394035 : Nat := 118140960795 + 3394035 * 2 ^ 59
def prefixEnd_3394035 : Nat := 4983230072969 + 3 ^ 40 * 3394035 * 2
def baseEnd_3394035 : Nat := 580923771060911185384541

theorem tailTrace_3394035 : CollatzResearch.WordTrace tailWord_3394035 prefixEnd_3394035 580923771060911185384541 := by
  unfold tailWord_3394035
  simp only [CollatzResearch.WordTrace]
  refine ⟨123790626258998324874415559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82527084172665549916277039 123790626258998324874415559)
  ·
    refine ⟨185685939388497487311623339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123790626258998324874415559 185685939388497487311623339)
    ·
      refine ⟨278528909082746230967435009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185685939388497487311623339 278528909082746230967435009)
      ·
        refine ⟨208896681812059673225576257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278528909082746230967435009 208896681812059673225576257)
        ·
          refine ⟨156672511359044754919182193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208896681812059673225576257 156672511359044754919182193)
          ·
            refine ⟨117504383519283566189386645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156672511359044754919182193 117504383519283566189386645)
            ·
              refine ⟨5508017977466417165127499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117504383519283566189386645 5508017977466417165127499)
              ·
                refine ⟨8262026966199625747691249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508017977466417165127499 8262026966199625747691249)
                ·
                  refine ⟨6196520224649719310768437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262026966199625747691249 6196520224649719310768437)
                  ·
                    refine ⟨580923771060911185384541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6196520224649719310768437 580923771060911185384541)
                    ·
                      rfl

theorem cell23_3394035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 5].length) (baseStart_3394035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394035 prefixEnd_3394035 := by exact prefixLift 3394035
  have htrace : WordTrace (prefixWord ++ tailWord_3394035) baseStart_3394035 baseEnd_3394035 := by
    simpa [prefixWord, tailWord_3394035, baseEnd_3394035] using wordTrace_append hprefix tailTrace_3394035
  have hstable : (prefixWord ++ tailWord_3394035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394035).length < 2 ^ (prefixWord ++ tailWord_3394035).sum := by decide
  have hdescent : baseEnd_3394035 < baseStart_3394035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394052 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_3394052 : Nat := 118140960795 + 3394052 * 2 ^ 59
def prefixEnd_3394052 : Nat := 4983230072969 + 3 ^ 40 * 3394052 * 2
def baseEnd_3394052 : Nat := 580926680784619996547015

theorem tailTrace_3394052 : CollatzResearch.WordTrace tailWord_3394052 prefixEnd_3394052 580926680784619996547015 := by
  unfold tailWord_3394052
  simp only [CollatzResearch.WordTrace]
  refine ⟨61895623149968368388892205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82527497533291157851856273 61895623149968368388892205)
  ·
    refine ⟨23210858681238138145834577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61895623149968368388892205 23210858681238138145834577)
    ·
      refine ⟨17408144010928603609375933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23210858681238138145834577 17408144010928603609375933)
      ·
        refine ⟨6528054004098226353515975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17408144010928603609375933 6528054004098226353515975)
        ·
          refine ⟨9792081006147339530273963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528054004098226353515975 9792081006147339530273963)
          ·
            refine ⟨14688121509221009295410945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792081006147339530273963 14688121509221009295410945)
            ·
              refine ⟨11016091131915756971558209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14688121509221009295410945 11016091131915756971558209)
              ·
                refine ⟨8262068348936817728668657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11016091131915756971558209 8262068348936817728668657)
                ·
                  refine ⟨6196551261702613296501493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262068348936817728668657 6196551261702613296501493)
                  ·
                    refine ⟨580926680784619996547015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6196551261702613296501493 580926680784619996547015)
                    ·
                      rfl

theorem cell23_3394052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_3394052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394052 prefixEnd_3394052 := by exact prefixLift 3394052
  have htrace : WordTrace (prefixWord ++ tailWord_3394052) baseStart_3394052 baseEnd_3394052 := by
    simpa [prefixWord, tailWord_3394052, baseEnd_3394052] using wordTrace_append hprefix tailTrace_3394052
  have hstable : (prefixWord ++ tailWord_3394052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394052).length < 2 ^ (prefixWord ++ tailWord_3394052).sum := by decide
  have hdescent : baseEnd_3394052 < baseStart_3394052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394072 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3394072 : Nat := 118140960795 + 3394072 * 2 ^ 59
def prefixEnd_3394072 : Nat := 4983230072969 + 3 ^ 40 * 3394072 * 2
def baseEnd_3394072 : Nat := 1742790311966949911390953

theorem tailTrace_3394072 : CollatzResearch.WordTrace tailWord_3394072 prefixEnd_3394072 1742790311966949911390953 := by
  unfold tailWord_3394072
  simp only [CollatzResearch.WordTrace]
  refine ⟨61895987879932140096756235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82527983839909520129008313 61895987879932140096756235)
  ·
    refine ⟨92843981819898210145134353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61895987879932140096756235 92843981819898210145134353)
    ·
      refine ⟨69632986364923657608850765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92843981819898210145134353 69632986364923657608850765)
      ·
        refine ⟨26112369886846371603319037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69632986364923657608850765 26112369886846371603319037)
        ·
          refine ⟨9792138707567389351244639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26112369886846371603319037 9792138707567389351244639)
          ·
            refine ⟨14688208061351084026866959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792138707567389351244639 14688208061351084026866959)
            ·
              refine ⟨22032312092026626040300439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688208061351084026866959 22032312092026626040300439)
              ·
                refine ⟨33048468138039939060450659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22032312092026626040300439 33048468138039939060450659)
                ·
                  refine ⟨49572702207059908590675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33048468138039939060450659 49572702207059908590675989)
                  ·
                    refine ⟨2323720415955933215187937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49572702207059908590675989 2323720415955933215187937)
                    ·
                      refine ⟨1742790311966949911390953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323720415955933215187937 1742790311966949911390953)
                      ·
                        rfl

theorem cell23_3394072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3394072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394072 prefixEnd_3394072 := by exact prefixLift 3394072
  have htrace : WordTrace (prefixWord ++ tailWord_3394072) baseStart_3394072 baseEnd_3394072 := by
    simpa [prefixWord, tailWord_3394072, baseEnd_3394072] using wordTrace_append hprefix tailTrace_3394072
  have hstable : (prefixWord ++ tailWord_3394072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394072).length < 2 ^ (prefixWord ++ tailWord_3394072).sum := by decide
  have hdescent : baseEnd_3394072 < baseStart_3394072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394099 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 1, 4]
def baseStart_3394099 : Nat := 118140960795 + 3394099 * 2 ^ 59
def prefixEnd_3394099 : Nat := 4983230072969 + 3 ^ 40 * 3394099 * 2
def baseEnd_3394099 : Nat := 580934725314873768584443

theorem tailTrace_3394099 : CollatzResearch.WordTrace tailWord_3394099 prefixEnd_3394099 580934725314873768584443 := by
  unfold tailWord_3394099
  simp only [CollatzResearch.WordTrace]
  refine ⟨123792960530766463804745351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82528640353844309203163567 123792960530766463804745351)
  ·
    refine ⟨185689440796149695707118027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123792960530766463804745351 185689440796149695707118027)
    ·
      refine ⟨278534161194224543560677041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185689440796149695707118027 278534161194224543560677041)
      ·
        refine ⟨208900620895668407670507781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278534161194224543560677041 208900620895668407670507781)
        ·
          refine ⟨39168866417937826438220209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208900620895668407670507781 39168866417937826438220209)
          ·
            refine ⟨29376649813453369828665157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39168866417937826438220209 29376649813453369828665157)
            ·
              refine ⟨5508121840022506842874717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29376649813453369828665157 5508121840022506842874717)
              ·
                refine ⟨2065545690008440066078019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5508121840022506842874717 2065545690008440066078019)
                ·
                  refine ⟨3098318535012660099117029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065545690008440066078019 3098318535012660099117029)
                  ·
                    refine ⟨580934725314873768584443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098318535012660099117029 580934725314873768584443)
                    ·
                      rfl

theorem cell23_3394099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 4].length) (baseStart_3394099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394099 prefixEnd_3394099 := by exact prefixLift 3394099
  have htrace : WordTrace (prefixWord ++ tailWord_3394099) baseStart_3394099 baseEnd_3394099 := by
    simpa [prefixWord, tailWord_3394099, baseEnd_3394099] using wordTrace_append hprefix tailTrace_3394099
  have hstable : (prefixWord ++ tailWord_3394099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394099).length < 2 ^ (prefixWord ++ tailWord_3394099).sum := by decide
  have hdescent : baseEnd_3394099 < baseStart_3394099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394102 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3394102 : Nat := 118140960795 + 3394102 * 2 ^ 59
def prefixEnd_3394102 : Nat := 4983230072969 + 3 ^ 40 * 3394102 * 2
def baseEnd_3394102 : Nat := 1742805716386584794015815

theorem tailTrace_3394102 : CollatzResearch.WordTrace tailWord_3394102 prefixEnd_3394102 1742805716386584794015815 := by
  unfold tailWord_3394102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7737066871859724707319035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82528713299837063544736373 7737066871859724707319035)
  ·
    refine ⟨11605600307789587060978553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7737066871859724707319035 11605600307789587060978553)
    ·
      refine ⟨8704200230842190295733915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11605600307789587060978553 8704200230842190295733915)
      ·
        refine ⟨13056300346263285443600873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8704200230842190295733915 13056300346263285443600873)
        ·
          refine ⟨9792225259697464082700655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13056300346263285443600873 9792225259697464082700655)
          ·
            refine ⟨14688337889546196124050983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792225259697464082700655 14688337889546196124050983)
            ·
              refine ⟨22032506834319294186076475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688337889546196124050983 22032506834319294186076475)
              ·
                refine ⟨33048760251478941279114713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22032506834319294186076475 33048760251478941279114713)
                ·
                  refine ⟨24786570188609205959336035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33048760251478941279114713 24786570188609205959336035)
                  ·
                    refine ⟨37179855282913808939004053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24786570188609205959336035 37179855282913808939004053)
                    ·
                      refine ⟨1742805716386584794015815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37179855282913808939004053 1742805716386584794015815)
                      ·
                        rfl

theorem cell23_3394102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3394102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394102 prefixEnd_3394102 := by exact prefixLift 3394102
  have htrace : WordTrace (prefixWord ++ tailWord_3394102) baseStart_3394102 baseEnd_3394102 := by
    simpa [prefixWord, tailWord_3394102, baseEnd_3394102] using wordTrace_append hprefix tailTrace_3394102
  have hstable : (prefixWord ++ tailWord_3394102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394102).length < 2 ^ (prefixWord ++ tailWord_3394102).sum := by decide
  have hdescent : baseEnd_3394102 < baseStart_3394102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394156 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 1, 1, 3]
def baseStart_3394156 : Nat := 118140960795 + 3394156 * 2 ^ 59
def prefixEnd_3394156 : Nat := 4983230072969 + 3 ^ 40 * 3394156 * 2
def baseEnd_3394156 : Nat := 1742833444341927582740567

theorem tailTrace_3394156 : CollatzResearch.WordTrace tailWord_3394156 prefixEnd_3394156 1742833444341927582740567 := by
  unfold tailWord_3394156
  simp only [CollatzResearch.WordTrace]
  refine ⟨61897519745779981269785161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82530026327706641693046881 61897519745779981269785161)
  ·
    refine ⟨46423139809334985952338871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61897519745779981269785161 46423139809334985952338871)
    ·
      refine ⟨69634709714002478928508307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46423139809334985952338871 69634709714002478928508307)
      ·
        refine ⟨104452064571003718392762461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69634709714002478928508307 104452064571003718392762461)
        ·
          refine ⟨39169524214126394397285923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104452064571003718392762461 39169524214126394397285923)
          ·
            refine ⟨58754286321189591595928885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39169524214126394397285923 58754286321189591595928885)
            ·
              refine ⟨5508214342611524212118333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58754286321189591595928885 5508214342611524212118333)
              ·
                refine ⟨2065580378479321579544375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5508214342611524212118333 2065580378479321579544375)
                ·
                  refine ⟨3098370567718982369316563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065580378479321579544375 3098370567718982369316563)
                  ·
                    refine ⟨4647555851578473553974845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098370567718982369316563 4647555851578473553974845)
                    ·
                      refine ⟨1742833444341927582740567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647555851578473553974845 1742833444341927582740567)
                      ·
                        rfl

theorem cell23_3394156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_3394156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394156 prefixEnd_3394156 := by exact prefixLift 3394156
  have htrace : WordTrace (prefixWord ++ tailWord_3394156) baseStart_3394156 baseEnd_3394156 := by
    simpa [prefixWord, tailWord_3394156, baseEnd_3394156] using wordTrace_append hprefix tailTrace_3394156
  have hstable : (prefixWord ++ tailWord_3394156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394156).length < 2 ^ (prefixWord ++ tailWord_3394156).sum := by decide
  have hdescent : baseEnd_3394156 < baseStart_3394156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394172 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_3394172 : Nat := 118140960795 + 3394172 * 2 ^ 59
def prefixEnd_3394172 : Nat := 4983230072969 + 3 ^ 40 * 3394172 * 2
def baseEnd_3394172 : Nat := 580947220010799840046831

theorem tailTrace_3394172 : CollatzResearch.WordTrace tailWord_3394172 prefixEnd_3394172 580947220010799840046831 := by
  unfold tailWord_3394172
  simp only [CollatzResearch.WordTrace]
  refine ⟨61897811529750998636076385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82530415373001331514768513 61897811529750998636076385)
  ·
    refine ⟨46423358647313248977057289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61897811529750998636076385 46423358647313248977057289)
    ·
      refine ⟨34817518985484936732792967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46423358647313248977057289 34817518985484936732792967)
      ·
        refine ⟨52226278478227405099189451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34817518985484936732792967 52226278478227405099189451)
        ·
          refine ⟨78339417717341107648784177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52226278478227405099189451 78339417717341107648784177)
          ·
            refine ⟨58754563288005830736588133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78339417717341107648784177 58754563288005830736588133)
            ·
              refine ⟨11016480616501093263110275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58754563288005830736588133 11016480616501093263110275)
              ·
                refine ⟨16524720924751639894665413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11016480616501093263110275 16524720924751639894665413)
                ·
                  refine ⟨3098385173390932480249765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16524720924751639894665413 3098385173390932480249765)
                  ·
                    refine ⟨580947220010799840046831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098385173390932480249765 580947220010799840046831)
                    ·
                      rfl

theorem cell23_3394172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_3394172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394172 prefixEnd_3394172 := by exact prefixLift 3394172
  have htrace : WordTrace (prefixWord ++ tailWord_3394172) baseStart_3394172 baseEnd_3394172 := by
    simpa [prefixWord, tailWord_3394172, baseEnd_3394172] using wordTrace_append hprefix tailTrace_3394172
  have hstable : (prefixWord ++ tailWord_3394172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394172).length < 2 ^ (prefixWord ++ tailWord_3394172).sum := by decide
  have hdescent : baseEnd_3394172 < baseStart_3394172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394173 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_3394173 : Nat := 118140960795 + 3394173 * 2 ^ 59
def prefixEnd_3394173 : Nat := 4983230072969 + 3 ^ 40 * 3394173 * 2
def baseEnd_3394173 : Nat := 1742842173513054016227989

theorem tailTrace_3394173 : CollatzResearch.WordTrace tailWord_3394173 prefixEnd_3394173 1742842173513054016227989 := by
  unfold tailWord_3394173
  simp only [CollatzResearch.WordTrace]
  refine ⟨123795659532498374442939173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82530439688332249628626115 123795659532498374442939173)
  ·
    refine ⟨23211686162343445208051095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123795659532498374442939173 23211686162343445208051095)
    ·
      refine ⟨34817529243515167812076643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23211686162343445208051095 34817529243515167812076643)
      ·
        refine ⟨52226293865272751718114965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34817529243515167812076643 52226293865272751718114965)
        ·
          refine ⟨2448107524934660236786639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52226293865272751718114965 2448107524934660236786639)
          ·
            refine ⟨3672161287401990355179959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448107524934660236786639 3672161287401990355179959)
            ·
              refine ⟨5508241931102985532769939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672161287401990355179959 5508241931102985532769939)
              ·
                refine ⟨8262362896654478299154909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508241931102985532769939 8262362896654478299154909)
                ·
                  refine ⟨3098386086245429362183091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8262362896654478299154909 3098386086245429362183091)
                  ·
                    refine ⟨4647579129368144043274637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098386086245429362183091 4647579129368144043274637)
                    ·
                      refine ⟨1742842173513054016227989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647579129368144043274637 1742842173513054016227989)
                      ·
                        rfl

theorem cell23_3394173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_3394173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394173 prefixEnd_3394173 := by exact prefixLift 3394173
  have htrace : WordTrace (prefixWord ++ tailWord_3394173) baseStart_3394173 baseEnd_3394173 := by
    simpa [prefixWord, tailWord_3394173, baseEnd_3394173] using wordTrace_append hprefix tailTrace_3394173
  have hstable : (prefixWord ++ tailWord_3394173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394173).length < 2 ^ (prefixWord ++ tailWord_3394173).sum := by decide
  have hdescent : baseEnd_3394173 < baseStart_3394173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394175 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_3394175 : Nat := 118140960795 + 3394175 * 2 ^ 59
def prefixEnd_3394175 : Nat := 4983230072969 + 3 ^ 40 * 3394175 * 2
def baseEnd_3394175 : Nat := 1742843200474363008402979

theorem tailTrace_3394175 : CollatzResearch.WordTrace tailWord_3394175 prefixEnd_3394175 1742843200474363008402979 := by
  unfold tailWord_3394175
  simp only [CollatzResearch.WordTrace]
  refine ⟨123795732478491128784511979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82530488318994085856341319 123795732478491128784511979)
  ·
    refine ⟨185693598717736693176767969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123795732478491128784511979 185693598717736693176767969)
    ·
      refine ⟨139270199038302519882575977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185693598717736693176767969 139270199038302519882575977)
      ·
        refine ⟨104452649278726889911931983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139270199038302519882575977 104452649278726889911931983)
        ·
          refine ⟨156678973918090334867897975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104452649278726889911931983 156678973918090334867897975)
          ·
            refine ⟨235018460877135502301846963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156678973918090334867897975 235018460877135502301846963)
            ·
              refine ⟨352527691315703253452770445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235018460877135502301846963 352527691315703253452770445)
              ·
                refine ⟨132197884243388720044788917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352527691315703253452770445 132197884243388720044788917)
                ·
                  refine ⟨12393551647817692504198961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132197884243388720044788917 12393551647817692504198961)
                  ·
                    refine ⟨9295163735863269378149221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12393551647817692504198961 9295163735863269378149221)
                    ·
                      refine ⟨1742843200474363008402979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9295163735863269378149221 1742843200474363008402979)
                      ·
                        rfl

theorem cell23_3394175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_3394175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394175 prefixEnd_3394175 := by exact prefixLift 3394175
  have htrace : WordTrace (prefixWord ++ tailWord_3394175) baseStart_3394175 baseEnd_3394175 := by
    simpa [prefixWord, tailWord_3394175, baseEnd_3394175] using wordTrace_append hprefix tailTrace_3394175
  have hstable : (prefixWord ++ tailWord_3394175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394175).length < 2 ^ (prefixWord ++ tailWord_3394175).sum := by decide
  have hdescent : baseEnd_3394175 < baseStart_3394175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394196 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3394196 : Nat := 118140960795 + 3394196 * 2 ^ 59
def prefixEnd_3394196 : Nat := 4983230072969 + 3 ^ 40 * 3394196 * 2
def baseEnd_3394196 : Nat := 1742853983568107426240383

theorem tailTrace_3394196 : CollatzResearch.WordTrace tailWord_3394196 prefixEnd_3394196 1742853983568107426240383 := by
  unfold tailWord_3394196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61898249205707524685513221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82530998940943366247350961 61898249205707524685513221)
  ·
    refine ⟨11605921726070160878533729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61898249205707524685513221 11605921726070160878533729)
    ·
      refine ⟨8704441294552620658900297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11605921726070160878533729 8704441294552620658900297)
      ·
        refine ⟨6528330970914465494175223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8704441294552620658900297 6528330970914465494175223)
        ·
          refine ⟨9792496456371698241262835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528330970914465494175223 9792496456371698241262835)
          ·
            refine ⟨14688744684557547361894253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792496456371698241262835 14688744684557547361894253)
            ·
              refine ⟨5508279256709080260710345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14688744684557547361894253 5508279256709080260710345)
              ·
                refine ⟨4131209442531810195532759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508279256709080260710345 4131209442531810195532759)
                ·
                  refine ⟨6196814163797715293299139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131209442531810195532759 6196814163797715293299139)
                  ·
                    refine ⟨9295221245696572939948709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6196814163797715293299139 9295221245696572939948709)
                    ·
                      refine ⟨1742853983568107426240383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9295221245696572939948709 1742853983568107426240383)
                      ·
                        rfl

theorem cell23_3394196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3394196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394196 prefixEnd_3394196 := by exact prefixLift 3394196
  have htrace : WordTrace (prefixWord ++ tailWord_3394196) baseStart_3394196 baseEnd_3394196 := by
    simpa [prefixWord, tailWord_3394196, baseEnd_3394196] using wordTrace_append hprefix tailTrace_3394196
  have hstable : (prefixWord ++ tailWord_3394196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394196).length < 2 ^ (prefixWord ++ tailWord_3394196).sum := by decide
  have hdescent : baseEnd_3394196 < baseStart_3394196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394209 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3394209 : Nat := 118140960795 + 3394209 * 2 ^ 59
def prefixEnd_3394209 : Nat := 4983230072969 + 3 ^ 40 * 3394209 * 2
def baseEnd_3394209 : Nat := 1742860658816615875377823

theorem tailTrace_3394209 : CollatzResearch.WordTrace tailWord_3394209 prefixEnd_3394209 1742860658816615875377823 := by
  unfold tailWord_3394209
  simp only [CollatzResearch.WordTrace]
  refine ⟨123796972560367952591249681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82531315040245301727499787 123796972560367952591249681)
  ·
    refine ⟨92847729420275964443437261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123796972560367952591249681 92847729420275964443437261)
    ·
      refine ⟨34817898532603486666288973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92847729420275964443437261 34817898532603486666288973)
      ·
        refine ⟨13056711949726307499858365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34817898532603486666288973 13056711949726307499858365)
        ·
          refine ⟨4896266981147365312446887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13056711949726307499858365 4896266981147365312446887)
          ·
            refine ⟨7344400471721047968670331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896266981147365312446887 7344400471721047968670331)
            ·
              refine ⟨11016600707581571953005497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344400471721047968670331 11016600707581571953005497)
              ·
                refine ⟨8262450530686178964754123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11016600707581571953005497 8262450530686178964754123)
                ·
                  refine ⟨12393675796029268447131185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262450530686178964754123 12393675796029268447131185)
                  ·
                    refine ⟨9295256847021951335348389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12393675796029268447131185 9295256847021951335348389)
                    ·
                      refine ⟨1742860658816615875377823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9295256847021951335348389 1742860658816615875377823)
                      ·
                        rfl

theorem cell23_3394209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3394209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394209 prefixEnd_3394209 := by exact prefixLift 3394209
  have htrace : WordTrace (prefixWord ++ tailWord_3394209) baseStart_3394209 baseEnd_3394209 := by
    simpa [prefixWord, tailWord_3394209, baseEnd_3394209] using wordTrace_append hprefix tailTrace_3394209
  have hstable : (prefixWord ++ tailWord_3394209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394209).length < 2 ^ (prefixWord ++ tailWord_3394209).sum := by decide
  have hdescent : baseEnd_3394209 < baseStart_3394209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394239 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 3, 3, 2]
def baseStart_3394239 : Nat := 118140960795 + 3394239 * 2 ^ 59
def prefixEnd_3394239 : Nat := 4983230072969 + 3 ^ 40 * 3394239 * 2
def baseEnd_3394239 : Nat := 1742876063236250758002685

theorem tailTrace_3394239 : CollatzResearch.WordTrace tailWord_3394239 prefixEnd_3394239 1742876063236250758002685 := by
  unfold tailWord_3394239
  simp only [CollatzResearch.WordTrace]
  refine ⟨123798066750259267714841771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82532044500172845143227847 123798066750259267714841771)
  ·
    refine ⟨185697100125388901572262657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123798066750259267714841771 185697100125388901572262657)
    ·
      refine ⟨139272825094041676179196993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185697100125388901572262657 139272825094041676179196993)
      ·
        refine ⟨104454618820531257134397745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139272825094041676179196993 104454618820531257134397745)
        ·
          refine ⟨78340964115398442850798309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104454618820531257134397745 78340964115398442850798309)
          ·
            refine ⟨14688930771637208034524683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78340964115398442850798309 14688930771637208034524683)
            ·
              refine ⟨22033396157455812051787025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14688930771637208034524683 22033396157455812051787025)
              ·
                refine ⟨16525047118091859038840269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22033396157455812051787025 16525047118091859038840269)
                ·
                  refine ⟨6196892669284447139565101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16525047118091859038840269 6196892669284447139565101)
                  ·
                    refine ⟨2323834750981667677336913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6196892669284447139565101 2323834750981667677336913)
                    ·
                      refine ⟨1742876063236250758002685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323834750981667677336913 1742876063236250758002685)
                      ·
                        rfl

theorem cell23_3394239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_3394239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394239 prefixEnd_3394239 := by exact prefixLift 3394239
  have htrace : WordTrace (prefixWord ++ tailWord_3394239) baseStart_3394239 baseEnd_3394239 := by
    simpa [prefixWord, tailWord_3394239, baseEnd_3394239] using wordTrace_append hprefix tailTrace_3394239
  have hstable : (prefixWord ++ tailWord_3394239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394239).length < 2 ^ (prefixWord ++ tailWord_3394239).sum := by decide
  have hdescent : baseEnd_3394239 < baseStart_3394239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394273 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_3394273 : Nat := 118140960795 + 3394273 * 2 ^ 59
def prefixEnd_3394273 : Nat := 4983230072969 + 3 ^ 40 * 3394273 * 2
def baseEnd_3394273 : Nat := 1742893521578503624977529

theorem tailTrace_3394273 : CollatzResearch.WordTrace tailWord_3394273 prefixEnd_3394273 1742893521578503624977529 := by
  unfold tailWord_3394273
  simp only [CollatzResearch.WordTrace]
  refine ⟨123799306832136091521579473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82532871221424061014386315 123799306832136091521579473)
  ·
    refine ⟨92849480124102068641184605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123799306832136091521579473 92849480124102068641184605)
    ·
      refine ⟨34818555046538275740444227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92849480124102068641184605 34818555046538275740444227)
      ·
        refine ⟨52227832569807413610666341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34818555046538275740444227 52227832569807413610666341)
        ·
          refine ⟨9792718606838890051999939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52227832569807413610666341 9792718606838890051999939)
          ·
            refine ⟨14689077910258335077999909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792718606838890051999939 14689077910258335077999909)
            ·
              refine ⟨2754202108173437827124983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14689077910258335077999909 2754202108173437827124983)
              ·
                refine ⟨4131303162260156740687475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754202108173437827124983 4131303162260156740687475)
                ·
                  refine ⟨6196954743390235111031213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131303162260156740687475 6196954743390235111031213)
                  ·
                    refine ⟨2323858028771338166636705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6196954743390235111031213 2323858028771338166636705)
                    ·
                      refine ⟨1742893521578503624977529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323858028771338166636705 1742893521578503624977529)
                      ·
                        rfl

theorem cell23_3394273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_3394273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394273 prefixEnd_3394273 := by exact prefixLift 3394273
  have htrace : WordTrace (prefixWord ++ tailWord_3394273) baseStart_3394273 baseEnd_3394273 := by
    simpa [prefixWord, tailWord_3394273, baseEnd_3394273] using wordTrace_append hprefix tailTrace_3394273
  have hstable : (prefixWord ++ tailWord_3394273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394273).length < 2 ^ (prefixWord ++ tailWord_3394273).sum := by decide
  have hdescent : baseEnd_3394273 < baseStart_3394273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394280 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_3394280 : Nat := 118140960795 + 3394280 * 2 ^ 59
def prefixEnd_3394280 : Nat := 4983230072969 + 3 ^ 40 * 3394280 * 2
def baseEnd_3394280 : Nat := 1742897115943085097589997

theorem tailTrace_3394280 : CollatzResearch.WordTrace tailWord_3394280 prefixEnd_3394280 1742897115943085097589997 := by
  unfold tailWord_3394280
  simp only [CollatzResearch.WordTrace]
  refine ⟨61899781071555365858542147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82533041428740487811389529 61899781071555365858542147)
  ·
    refine ⟨92849671607333048787813221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61899781071555365858542147 92849671607333048787813221)
    ·
      refine ⟨17409313426374946647714979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92849671607333048787813221 17409313426374946647714979)
      ·
        refine ⟨26113970139562419971572469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17409313426374946647714979 26113970139562419971572469)
        ·
          refine ⟨2448184700583976872334919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26113970139562419971572469 2448184700583976872334919)
          ·
            refine ⟨3672277050875965308502379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448184700583976872334919 3672277050875965308502379)
            ·
              refine ⟨5508415576313947962753569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672277050875965308502379 5508415576313947962753569)
              ·
                refine ⟨4131311682235460972065177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508415576313947962753569 4131311682235460972065177)
                ·
                  refine ⟨3098483761676595729048883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131311682235460972065177 3098483761676595729048883)
                  ·
                    refine ⟨4647725642514893593573325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098483761676595729048883 4647725642514893593573325)
                    ·
                      refine ⟨1742897115943085097589997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647725642514893593573325 1742897115943085097589997)
                      ·
                        rfl

theorem cell23_3394280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_3394280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394280 prefixEnd_3394280 := by exact prefixLift 3394280
  have htrace : WordTrace (prefixWord ++ tailWord_3394280) baseStart_3394280 baseEnd_3394280 := by
    simpa [prefixWord, tailWord_3394280, baseEnd_3394280] using wordTrace_append hprefix tailTrace_3394280
  have hstable : (prefixWord ++ tailWord_3394280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394280).length < 2 ^ (prefixWord ++ tailWord_3394280).sum := by decide
  have hdescent : baseEnd_3394280 < baseStart_3394280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394359 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_3394359 : Nat := 118140960795 + 3394359 * 2 ^ 59
def prefixEnd_3394359 : Nat := 4983230072969 + 3 ^ 40 * 3394359 * 2
def baseEnd_3394359 : Nat := 1742937680914790288502133

theorem tailTrace_3394359 : CollatzResearch.WordTrace tailWord_3394359 prefixEnd_3394359 1742937680914790288502133 := by
  unfold tailWord_3394359
  simp only [CollatzResearch.WordTrace]
  refine ⟨123802443509824528209210131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82534962339883018806140087 123802443509824528209210131)
  ·
    refine ⟨185703665264736792313815197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123802443509824528209210131 185703665264736792313815197)
    ·
      refine ⟨69638874474276297117680699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185703665264736792313815197 69638874474276297117680699)
      ·
        refine ⟨104458311711414445676521049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69638874474276297117680699 104458311711414445676521049)
        ·
          refine ⟨78343733783560834257390787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104458311711414445676521049 78343733783560834257390787)
          ·
            refine ⟨117515600675341251386086181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78343733783560834257390787 117515600675341251386086181)
            ·
              refine ⟨22034175126626484634891159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117515600675341251386086181 22034175126626484634891159)
              ·
                refine ⟨33051262689939726952336739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22034175126626484634891159 33051262689939726952336739)
                ·
                  refine ⟨49576894034909590428505109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33051262689939726952336739 49576894034909590428505109)
                  ·
                    refine ⟨2323916907886387051336177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49576894034909590428505109 2323916907886387051336177)
                    ·
                      refine ⟨1742937680914790288502133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323916907886387051336177 1742937680914790288502133)
                      ·
                        rfl

theorem cell23_3394359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_3394359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394359 prefixEnd_3394359 := by exact prefixLift 3394359
  have htrace : WordTrace (prefixWord ++ tailWord_3394359) baseStart_3394359 baseEnd_3394359 := by
    simpa [prefixWord, tailWord_3394359, baseEnd_3394359] using wordTrace_append hprefix tailTrace_3394359
  have hstable : (prefixWord ++ tailWord_3394359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394359).length < 2 ^ (prefixWord ++ tailWord_3394359).sum := by decide
  have hdescent : baseEnd_3394359 < baseStart_3394359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394382 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_3394382 : Nat := 118140960795 + 3394382 * 2 ^ 59
def prefixEnd_3394382 : Nat := 4983230072969 + 3 ^ 40 * 3394382 * 2
def baseEnd_3394382 : Nat := 193661054552204855390503

theorem tailTrace_3394382 : CollatzResearch.WordTrace tailWord_3394382 prefixEnd_3394382 193661054552204855390503 := by
  unfold tailWord_3394382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475410298592650392162175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82535521592494135424864933 15475410298592650392162175)
  ·
    refine ⟨23213115447888975588243263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15475410298592650392162175 23213115447888975588243263)
    ·
      refine ⟨34819673171833463382364895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23213115447888975588243263 34819673171833463382364895)
      ·
        refine ⟨52229509757750195073547343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34819673171833463382364895 52229509757750195073547343)
        ·
          refine ⟨78344264636625292610321015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52229509757750195073547343 78344264636625292610321015)
          ·
            refine ⟨117516396954937938915481523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78344264636625292610321015 117516396954937938915481523)
            ·
              refine ⟨176274595432406908373222285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117516396954937938915481523 176274595432406908373222285)
              ·
                refine ⟨66102973287152590639958357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176274595432406908373222285 66102973287152590639958357)
                ·
                  refine ⟨193661054552204855390503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66102973287152590639958357 193661054552204855390503)
                  ·
                    rfl

theorem cell23_3394382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_3394382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394382 prefixEnd_3394382 := by exact prefixLift 3394382
  have htrace : WordTrace (prefixWord ++ tailWord_3394382) baseStart_3394382 baseEnd_3394382 := by
    simpa [prefixWord, tailWord_3394382, baseEnd_3394382] using wordTrace_append hprefix tailTrace_3394382
  have hstable : (prefixWord ++ tailWord_3394382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394382).length < 2 ^ (prefixWord ++ tailWord_3394382).sum := by decide
  have hdescent : baseEnd_3394382 < baseStart_3394382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394399 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 6]
def baseStart_3394399 : Nat := 118140960795 + 3394399 * 2 ^ 59
def prefixEnd_3394399 : Nat := 4983230072969 + 3 ^ 40 * 3394399 * 2
def baseEnd_3394399 : Nat := 193662024460107792444661

theorem tailTrace_3394399 : CollatzResearch.WordTrace tailWord_3394399 prefixEnd_3394399 193662024460107792444661 := by
  unfold tailWord_3394399
  simp only [CollatzResearch.WordTrace]
  refine ⟨123803902429679615040666251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82535934953119743360444167 123803902429679615040666251)
  ·
    refine ⟨185705853644519422560999377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123803902429679615040666251 185705853644519422560999377)
    ·
      refine ⟨139279390233389566920749533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185705853644519422560999377 139279390233389566920749533)
      ·
        refine ⟨52229771337521087595281075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139279390233389566920749533 52229771337521087595281075)
        ·
          refine ⟨78344657006281631392921613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52229771337521087595281075 78344657006281631392921613)
          ·
            refine ⟨29379246377355611772345605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78344657006281631392921613 29379246377355611772345605)
            ·
              refine ⟨5508608695754177207314801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29379246377355611772345605 5508608695754177207314801)
              ·
                refine ⟨4131456521815632905486101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508608695754177207314801 4131456521815632905486101)
                ·
                  refine ⟨193662024460107792444661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4131456521815632905486101 193662024460107792444661)
                  ·
                    rfl

theorem cell23_3394399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 6].length) (baseStart_3394399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394399 prefixEnd_3394399 := by exact prefixLift 3394399
  have htrace : WordTrace (prefixWord ++ tailWord_3394399) baseStart_3394399 baseEnd_3394399 := by
    simpa [prefixWord, tailWord_3394399, baseEnd_3394399] using wordTrace_append hprefix tailTrace_3394399
  have hstable : (prefixWord ++ tailWord_3394399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394399).length < 2 ^ (prefixWord ++ tailWord_3394399).sum := by decide
  have hdescent : baseEnd_3394399 < baseStart_3394399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394403 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 1, 4]
def baseStart_3394403 : Nat := 118140960795 + 3394403 * 2 ^ 59
def prefixEnd_3394403 : Nat := 4983230072969 + 3 ^ 40 * 3394403 * 2
def baseEnd_3394403 : Nat := 580986758021196038783977

theorem tailTrace_3394403 : CollatzResearch.WordTrace tailWord_3394403 prefixEnd_3394403 580986758021196038783977 := by
  unfold tailWord_3394403
  simp only [CollatzResearch.WordTrace]
  refine ⟨123804048321665123723811863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82536032214443415815874575 123804048321665123723811863)
  ·
    refine ⟨185706072482497685585717795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123804048321665123723811863 185706072482497685585717795)
    ·
      refine ⟨278559108723746528378576693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185706072482497685585717795 278559108723746528378576693)
      ·
        refine ⟨26114916442851237035491565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278559108723746528378576693 26114916442851237035491565)
        ·
          refine ⟨9793093666069213888309337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26114916442851237035491565 9793093666069213888309337)
          ·
            refine ⟨7344820249551910416232003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793093666069213888309337 7344820249551910416232003)
            ·
              refine ⟨11017230374327865624348005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344820249551910416232003 11017230374327865624348005)
              ·
                refine ⟨2065730695186474804565251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11017230374327865624348005 2065730695186474804565251)
                ·
                  refine ⟨3098596042779712206847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065730695186474804565251 3098596042779712206847877)
                  ·
                    refine ⟨580986758021196038783977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098596042779712206847877 580986758021196038783977)
                    ·
                      rfl

theorem cell23_3394403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 4].length) (baseStart_3394403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394403 prefixEnd_3394403 := by exact prefixLift 3394403
  have htrace : WordTrace (prefixWord ++ tailWord_3394403) baseStart_3394403 baseEnd_3394403 := by
    simpa [prefixWord, tailWord_3394403, baseEnd_3394403] using wordTrace_append hprefix tailTrace_3394403
  have hstable : (prefixWord ++ tailWord_3394403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394403).length < 2 ^ (prefixWord ++ tailWord_3394403).sum := by decide
  have hdescent : baseEnd_3394403 < baseStart_3394403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394429 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_3394429 : Nat := 118140960795 + 3394429 * 2 ^ 59
def prefixEnd_3394429 : Nat := 4983230072969 + 3 ^ 40 * 3394429 * 2
def baseEnd_3394429 : Nat := 580991208186868338208937

theorem tailTrace_3394429 : CollatzResearch.WordTrace tailWord_3394429 prefixEnd_3394429 580991208186868338208937 := by
  unfold tailWord_3394429
  simp only [CollatzResearch.WordTrace]
  refine ⟨123804996619570930164258341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82536664413047286776172227 123804996619570930164258341)
  ·
    refine ⟨23213436866169549405798439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123804996619570930164258341 23213436866169549405798439)
    ·
      refine ⟨34820155299254324108697659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23213436866169549405798439 34820155299254324108697659)
      ·
        refine ⟨52230232948881486163046489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34820155299254324108697659 52230232948881486163046489)
        ·
          refine ⟨39172674711661114622284867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52230232948881486163046489 39172674711661114622284867)
          ·
            refine ⟨58759012067491671933427301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39172674711661114622284867 58759012067491671933427301)
            ·
              refine ⟨11017314762654688487517619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58759012067491671933427301 11017314762654688487517619)
              ·
                refine ⟨16525972143982032731276429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017314762654688487517619 16525972143982032731276429)
                ·
                  refine ⟨6197239553993262274228661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16525972143982032731276429 6197239553993262274228661)
                  ·
                    refine ⟨580991208186868338208937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6197239553993262274228661 580991208186868338208937)
                    ·
                      rfl

theorem cell23_3394429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_3394429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394429 prefixEnd_3394429 := by exact prefixLift 3394429
  have htrace : WordTrace (prefixWord ++ tailWord_3394429) baseStart_3394429 baseEnd_3394429 := by
    simpa [prefixWord, tailWord_3394429, baseEnd_3394429] using wordTrace_append hprefix tailTrace_3394429
  have hstable : (prefixWord ++ tailWord_3394429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394429).length < 2 ^ (prefixWord ++ tailWord_3394429).sum := by decide
  have hdescent : baseEnd_3394429 < baseStart_3394429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394443 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 1, 1, 3]
def baseStart_3394443 : Nat := 118140960795 + 3394443 * 2 ^ 59
def prefixEnd_3394443 : Nat := 4983230072969 + 3 ^ 40 * 3394443 * 2
def baseEnd_3394443 : Nat := 1742980813289767959851747

theorem tailTrace_3394443 : CollatzResearch.WordTrace tailWord_3394443 prefixEnd_3394443 1742980813289767959851747 := by
  unfold tailWord_3394443
  simp only [CollatzResearch.WordTrace]
  refine ⟨123805507241520210555267983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82537004827680140370178655 123805507241520210555267983)
  ·
    refine ⟨185708260862280315832901975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123805507241520210555267983 185708260862280315832901975)
    ·
      refine ⟨278562391293420473749352963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185708260862280315832901975 278562391293420473749352963)
      ·
        refine ⟨417843586940130710624029445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278562391293420473749352963 417843586940130710624029445)
        ·
          refine ⟨78345672551274508242005521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417843586940130710624029445 78345672551274508242005521)
          ·
            refine ⟨58759254413455881181504141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78345672551274508242005521 58759254413455881181504141)
            ·
              refine ⟨22034720405045955443064053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58759254413455881181504141 22034720405045955443064053)
              ·
                refine ⟨2065755037973058322787255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22034720405045955443064053 2065755037973058322787255)
                ·
                  refine ⟨3098632556959587484180883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065755037973058322787255 3098632556959587484180883)
                  ·
                    refine ⟨4647948835439381226271325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098632556959587484180883 4647948835439381226271325)
                    ·
                      refine ⟨1742980813289767959851747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647948835439381226271325 1742980813289767959851747)
                      ·
                        rfl

theorem cell23_3394443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 1, 3].length) (baseStart_3394443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394443 prefixEnd_3394443 := by exact prefixLift 3394443
  have htrace : WordTrace (prefixWord ++ tailWord_3394443) baseStart_3394443 baseEnd_3394443 := by
    simpa [prefixWord, tailWord_3394443, baseEnd_3394443] using wordTrace_append hprefix tailTrace_3394443
  have hstable : (prefixWord ++ tailWord_3394443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394443).length < 2 ^ (prefixWord ++ tailWord_3394443).sum := by decide
  have hdescent : baseEnd_3394443 < baseStart_3394443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394450 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_3394450 : Nat := 118140960795 + 3394450 * 2 ^ 59
def prefixEnd_3394450 : Nat := 4983230072969 + 3 ^ 40 * 3394450 * 2
def baseEnd_3394450 : Nat := 193664934183816603607135

theorem tailTrace_3394450 : CollatzResearch.WordTrace tailWord_3394450 prefixEnd_3394450 193664934183816603607135 := by
  unfold tailWord_3394450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951440638123712687693201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82537175034996567167181869 30951440638123712687693201)
  ·
    refine ⟨23213580478592784515769901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30951440638123712687693201 23213580478592784515769901)
    ·
      refine ⟨8705092679472294193413713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23213580478592784515769901 8705092679472294193413713)
      ·
        refine ⟨6528819509604220645060285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705092679472294193413713 6528819509604220645060285)
        ·
          refine ⟨2448307316101582741897607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6528819509604220645060285 2448307316101582741897607)
          ·
            refine ⟨3672460974152374112846411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448307316101582741897607 3672460974152374112846411)
            ·
              refine ⟨5508691461228561169269617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672460974152374112846411 5508691461228561169269617)
              ·
                refine ⟨4131518595921420876952213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5508691461228561169269617 4131518595921420876952213)
                ·
                  refine ⟨193664934183816603607135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4131518595921420876952213 193664934183816603607135)
                  ·
                    rfl

theorem cell23_3394450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_3394450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394450 prefixEnd_3394450 := by exact prefixLift 3394450
  have htrace : WordTrace (prefixWord ++ tailWord_3394450) baseStart_3394450 baseEnd_3394450 := by
    simpa [prefixWord, tailWord_3394450, baseEnd_3394450] using wordTrace_append hprefix tailTrace_3394450
  have hstable : (prefixWord ++ tailWord_3394450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394450).length < 2 ^ (prefixWord ++ tailWord_3394450).sum := by decide
  have hdescent : baseEnd_3394450 < baseStart_3394450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394460 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3394460 : Nat := 118140960795 + 3394460 * 2 ^ 59
def prefixEnd_3394460 : Nat := 4983230072969 + 3 ^ 40 * 3394460 * 2
def baseEnd_3394460 : Nat := 1742989542460894393339169

theorem tailTrace_3394460 : CollatzResearch.WordTrace tailWord_3394460 prefixEnd_3394460 1742989542460894393339169 := by
  unfold tailWord_3394460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61903063641229311229318417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82537418188305748305757889 61903063641229311229318417)
  ·
    refine ⟨46427297730921983421988813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61903063641229311229318417 46427297730921983421988813)
    ·
      refine ⟨17410236649095743783245805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46427297730921983421988813 17410236649095743783245805)
      ·
        refine ⟨6528838743410903918717177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17410236649095743783245805 6528838743410903918717177)
        ·
          refine ⟨4896629057558177939037883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6528838743410903918717177 4896629057558177939037883)
          ·
            refine ⟨7344943586337266908556825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896629057558177939037883 7344943586337266908556825)
            ·
              refine ⟨5508707689752950181417619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7344943586337266908556825 5508707689752950181417619)
              ·
                refine ⟨8263061534629425272126429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508707689752950181417619 8263061534629425272126429)
                ·
                  refine ⟨3098648075486034477047411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8263061534629425272126429 3098648075486034477047411)
                  ·
                    refine ⟨4647972113229051715571117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098648075486034477047411 4647972113229051715571117)
                    ·
                      refine ⟨1742989542460894393339169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647972113229051715571117 1742989542460894393339169)
                      ·
                        rfl

theorem cell23_3394460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3394460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394460 prefixEnd_3394460 := by exact prefixLift 3394460
  have htrace : WordTrace (prefixWord ++ tailWord_3394460) baseStart_3394460 baseEnd_3394460 := by
    simpa [prefixWord, tailWord_3394460, baseEnd_3394460] using wordTrace_append hprefix tailTrace_3394460
  have hstable : (prefixWord ++ tailWord_3394460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394460).length < 2 ^ (prefixWord ++ tailWord_3394460).sum := by decide
  have hdescent : baseEnd_3394460 < baseStart_3394460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394479 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_3394479 : Nat := 118140960795 + 3394479 * 2 ^ 59
def prefixEnd_3394479 : Nat := 4983230072969 + 3 ^ 40 * 3394479 * 2
def baseEnd_3394479 : Nat := 1742999298593329819001581

theorem tailTrace_3394479 : CollatzResearch.WordTrace tailWord_3394479 prefixEnd_3394479 1742999298593329819001581 := by
  unfold tailWord_3394479
  simp only [CollatzResearch.WordTrace]
  refine ⟨123806820269389788703578491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82537880179593192469052327 123806820269389788703578491)
  ·
    refine ⟨185710230404084683055367737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123806820269389788703578491 185710230404084683055367737)
    ·
      refine ⟨139282672803063512291525803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185710230404084683055367737 139282672803063512291525803)
      ·
        refine ⟨208924009204595268437288705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139282672803063512291525803 208924009204595268437288705)
        ·
          refine ⟨156693006903446451327966529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208924009204595268437288705 156693006903446451327966529)
          ·
            refine ⟨117519755177584838495974897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156693006903446451327966529 117519755177584838495974897)
            ·
              refine ⟨88139816383188628871981173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117519755177584838495974897 88139816383188628871981173)
              ·
                refine ⟨8263107785923933956748235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88139816383188628871981173 8263107785923933956748235)
                ·
                  refine ⟨12394661678885900935122353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8263107785923933956748235 12394661678885900935122353)
                  ·
                    refine ⟨9295996259164425701341765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12394661678885900935122353 9295996259164425701341765)
                    ·
                      refine ⟨1742999298593329819001581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9295996259164425701341765 1742999298593329819001581)
                      ·
                        rfl

theorem cell23_3394479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_3394479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394479 prefixEnd_3394479 := by exact prefixLift 3394479
  have htrace : WordTrace (prefixWord ++ tailWord_3394479) baseStart_3394479 baseEnd_3394479 := by
    simpa [prefixWord, tailWord_3394479, baseEnd_3394479] using wordTrace_append hprefix tailTrace_3394479
  have hstable : (prefixWord ++ tailWord_3394479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394479).length < 2 ^ (prefixWord ++ tailWord_3394479).sum := by decide
  have hdescent : baseEnd_3394479 < baseStart_3394479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394489 : List Nat := [1, 2, 1, 4, 2, 3, 1, 9]
def baseStart_3394489 : Nat := 118140960795 + 3394489 * 2 ^ 59
def prefixEnd_3394489 : Nat := 4983230072969 + 3 ^ 40 * 3394489 * 2
def baseEnd_3394489 : Nat := 64555719755550917773205

theorem tailTrace_3394489 : CollatzResearch.WordTrace tailWord_3394489 prefixEnd_3394489 64555719755550917773205 := by
  unfold tailWord_3394489
  simp only [CollatzResearch.WordTrace]
  refine ⟨123807184999353560411442521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82538123332902373607628347 123807184999353560411442521)
  ·
    refine ⟨92855388749515170308581891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123807184999353560411442521 92855388749515170308581891)
    ·
      refine ⟨139283083124272755462872837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92855388749515170308581891 139283083124272755462872837)
      ·
        refine ⟨26115578085801141649288657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139283083124272755462872837 26115578085801141649288657)
        ·
          refine ⟨19586683564350856236966493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26115578085801141649288657 19586683564350856236966493)
          ·
            refine ⟨7345006336631571088862435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19586683564350856236966493 7345006336631571088862435)
            ·
              refine ⟨11017509504947356633293653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345006336631571088862435 11017509504947356633293653)
              ·
                refine ⟨64555719755550917773205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11017509504947356633293653 64555719755550917773205)
                ·
                  rfl

theorem cell23_3394489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 9].length) (baseStart_3394489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394489 prefixEnd_3394489 := by exact prefixLift 3394489
  have htrace : WordTrace (prefixWord ++ tailWord_3394489) baseStart_3394489 baseEnd_3394489 := by
    simpa [prefixWord, tailWord_3394489, baseEnd_3394489] using wordTrace_append hprefix tailTrace_3394489
  have hstable : (prefixWord ++ tailWord_3394489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394489).length < 2 ^ (prefixWord ++ tailWord_3394489).sum := by decide
  have hdescent : baseEnd_3394489 < baseStart_3394489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394517 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3394517 : Nat := 118140960795 + 3394517 * 2 ^ 59
def prefixEnd_3394517 : Nat := 4983230072969 + 3 ^ 40 * 3394517 * 2
def baseEnd_3394517 : Nat := 1743018810858200670326407

theorem tailTrace_3394517 : CollatzResearch.WordTrace tailWord_3394517 prefixEnd_3394517 1743018810858200670326407 := by
  unfold tailWord_3394517
  simp only [CollatzResearch.WordTrace]
  refine ⟨123808206243252121193461805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82538804162168080795641203 123808206243252121193461805)
  ·
    refine ⟨46428077341219545447548177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123808206243252121193461805 46428077341219545447548177)
    ·
      refine ⟨34821058005914659085661133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46428077341219545447548177 34821058005914659085661133)
      ·
        refine ⟨13057896752217997157122925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34821058005914659085661133 13057896752217997157122925)
        ·
          refine ⟨4896711282081748933921097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13057896752217997157122925 4896711282081748933921097)
          ·
            refine ⟨3672533461561311700440823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4896711282081748933921097 3672533461561311700440823)
            ·
              refine ⟨5508800192341967550661235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672533461561311700440823 5508800192341967550661235)
              ·
                refine ⟨8263200288512951325991853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508800192341967550661235 8263200288512951325991853)
                ·
                  refine ⟨3098700108192356747246945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8263200288512951325991853 3098700108192356747246945)
                  ·
                    refine ⟨2324025081144267560435209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3098700108192356747246945 2324025081144267560435209)
                    ·
                      refine ⟨1743018810858200670326407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324025081144267560435209 1743018810858200670326407)
                      ·
                        rfl

theorem cell23_3394517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3394517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394517 prefixEnd_3394517 := by exact prefixLift 3394517
  have htrace : WordTrace (prefixWord ++ tailWord_3394517) baseStart_3394517 baseEnd_3394517 := by
    simpa [prefixWord, tailWord_3394517, baseEnd_3394517] using wordTrace_append hprefix tailTrace_3394517
  have hstable : (prefixWord ++ tailWord_3394517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394517).length < 2 ^ (prefixWord ++ tailWord_3394517).sum := by decide
  have hdescent : baseEnd_3394517 < baseStart_3394517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394527 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 2, 4]
def baseStart_3394527 : Nat := 118140960795 + 3394527 * 2 ^ 59
def prefixEnd_3394527 : Nat := 4983230072969 + 3 ^ 40 * 3394527 * 2
def baseEnd_3394527 : Nat := 581007981888248543733787

theorem tailTrace_3394527 : CollatzResearch.WordTrace tailWord_3394527 prefixEnd_3394527 581007981888248543733787 := by
  unfold tailWord_3394527
  simp only [CollatzResearch.WordTrace]
  refine ⟨123808570973215892901325835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82539047315477261934217223 123808570973215892901325835)
  ·
    refine ⟨185712856459823839351988753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123808570973215892901325835 185712856459823839351988753)
    ·
      refine ⟨139284642344867879513991565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185712856459823839351988753 139284642344867879513991565)
      ·
        refine ⟨52231740879325454817746837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139284642344867879513991565 52231740879325454817746837)
        ·
          refine ⟨2448362853718380694581883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52231740879325454817746837 2448362853718380694581883)
          ·
            refine ⟨3672544280577571041872825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448362853718380694581883 3672544280577571041872825)
            ·
              refine ⟨2754408210433178281404619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672544280577571041872825 2754408210433178281404619)
              ·
                refine ⟨4131612315649767422106929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754408210433178281404619 4131612315649767422106929)
                ·
                  refine ⟨3098709236737325566580197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131612315649767422106929 3098709236737325566580197)
                  ·
                    refine ⟨581007981888248543733787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098709236737325566580197 581007981888248543733787)
                    ·
                      rfl

theorem cell23_3394527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_3394527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394527 prefixEnd_3394527 := by exact prefixLift 3394527
  have htrace : WordTrace (prefixWord ++ tailWord_3394527) baseStart_3394527 baseEnd_3394527 := by
    simpa [prefixWord, tailWord_3394527, baseEnd_3394527] using wordTrace_append hprefix tailTrace_3394527
  have hstable : (prefixWord ++ tailWord_3394527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394527).length < 2 ^ (prefixWord ++ tailWord_3394527).sum := by decide
  have hdescent : baseEnd_3394527 < baseStart_3394527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394543 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 3, 3, 2]
def baseStart_3394543 : Nat := 118140960795 + 3394543 * 2 ^ 59
def prefixEnd_3394543 : Nat := 4983230072969 + 3 ^ 40 * 3394543 * 2
def baseEnd_3394543 : Nat := 1743032161355217568601287

theorem tailTrace_3394543 : CollatzResearch.WordTrace tailWord_3394543 prefixEnd_3394543 1743032161355217568601287 := by
  unfold tailWord_3394543
  simp only [CollatzResearch.WordTrace]
  refine ⟨123809154541157927633908283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82539436360771951755938855 123809154541157927633908283)
  ·
    refine ⟨185713731811736891450862425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123809154541157927633908283 185713731811736891450862425)
    ·
      refine ⟨139285298858802668588146819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185713731811736891450862425 139285298858802668588146819)
      ·
        refine ⟨208927948288204002882220229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139285298858802668588146819 208927948288204002882220229)
        ·
          refine ⟨39173990304038250540416293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208927948288204002882220229 39173990304038250540416293)
          ·
            refine ⟨7345123182007171976328055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39173990304038250540416293 7345123182007171976328055)
            ·
              refine ⟨11017684773010757964492083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345123182007171976328055 11017684773010757964492083)
              ·
                refine ⟨16526527159516136946738125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017684773010757964492083 16526527159516136946738125)
                ·
                  refine ⟨6197447684818551355026797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16526527159516136946738125 6197447684818551355026797)
                  ·
                    refine ⟨2324042881806956758135049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6197447684818551355026797 2324042881806956758135049)
                    ·
                      refine ⟨1743032161355217568601287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324042881806956758135049 1743032161355217568601287)
                      ·
                        rfl

theorem cell23_3394543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3, 2].length) (baseStart_3394543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394543 prefixEnd_3394543 := by exact prefixLift 3394543
  have htrace : WordTrace (prefixWord ++ tailWord_3394543) baseStart_3394543 baseEnd_3394543 := by
    simpa [prefixWord, tailWord_3394543, baseEnd_3394543] using wordTrace_append hprefix tailTrace_3394543
  have hstable : (prefixWord ++ tailWord_3394543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394543).length < 2 ^ (prefixWord ++ tailWord_3394543).sum := by decide
  have hdescent : baseEnd_3394543 < baseStart_3394543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394569 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_3394569 : Nat := 118140960795 + 3394569 * 2 ^ 59
def prefixEnd_3394569 : Nat := 4983230072969 + 3 ^ 40 * 3394569 * 2
def baseEnd_3394569 : Nat := 1743045511852234466876167

theorem tailTrace_3394569 : CollatzResearch.WordTrace tailWord_3394569 prefixEnd_3394569 1743045511852234466876167 := by
  unfold tailWord_3394569
  simp only [CollatzResearch.WordTrace]
  refine ⟨123810102839063734074354761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82540068559375822716236507 123810102839063734074354761)
  ·
    refine ⟨92857577129297800555766071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123810102839063734074354761 92857577129297800555766071)
    ·
      refine ⟨139286365693946700833649107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92857577129297800555766071 139286365693946700833649107)
      ·
        refine ⟨208929548540920051250473661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139286365693946700833649107 208929548540920051250473661)
        ·
          refine ⟨78348580702845019218927623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208929548540920051250473661 78348580702845019218927623)
          ·
            refine ⟨117522871054267528828391435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78348580702845019218927623 117522871054267528828391435)
            ·
              refine ⟨176284306581401293242587153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117522871054267528828391435 176284306581401293242587153)
              ·
                refine ⟨132213229936050969931940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176284306581401293242587153 132213229936050969931940365)
                ·
                  refine ⟨49579961226019113724477637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132213229936050969931940365 49579961226019113724477637)
                  ·
                    refine ⟨9296242729878583823339557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49579961226019113724477637 9296242729878583823339557)
                    ·
                      refine ⟨1743045511852234466876167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9296242729878583823339557 1743045511852234466876167)
                      ·
                        rfl

theorem cell23_3394569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_3394569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394569 prefixEnd_3394569 := by exact prefixLift 3394569
  have htrace : WordTrace (prefixWord ++ tailWord_3394569) baseStart_3394569 baseEnd_3394569 := by
    simpa [prefixWord, tailWord_3394569, baseEnd_3394569] using wordTrace_append hprefix tailTrace_3394569
  have hstable : (prefixWord ++ tailWord_3394569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394569).length < 2 ^ (prefixWord ++ tailWord_3394569).sum := by decide
  have hdescent : baseEnd_3394569 < baseStart_3394569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394579 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 7]
def baseStart_3394579 : Nat := 118140960795 + 3394579 * 2 ^ 59
def prefixEnd_3394579 : Nat := 4983230072969 + 3 ^ 40 * 3394579 * 2
def baseEnd_3394579 : Nat := 193672294073197714194569

theorem tailTrace_3394579 : CollatzResearch.WordTrace tailWord_3394579 prefixEnd_3394579 193672294073197714194569 := by
  unfold tailWord_3394579
  simp only [CollatzResearch.WordTrace]
  refine ⟨123810467569027505782218791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82540311712685003854812527 123810467569027505782218791)
  ·
    refine ⟨185715701353541258673328187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123810467569027505782218791 185715701353541258673328187)
    ·
      refine ⟨278573552030311888009992281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185715701353541258673328187 278573552030311888009992281)
      ·
        refine ⟨208930164022733916007494211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278573552030311888009992281 208930164022733916007494211)
        ·
          refine ⟨313395246034100874011241317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208930164022733916007494211 313395246034100874011241317)
          ·
            refine ⟨58761608631393913877107747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313395246034100874011241317 58761608631393913877107747)
            ·
              refine ⟨88142412947090870815661621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58761608631393913877107747 88142412947090870815661621)
              ·
                refine ⟨8263351213789769138968277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88142412947090870815661621 8263351213789769138968277)
                ·
                  refine ⟨193672294073197714194569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8263351213789769138968277 193672294073197714194569)
                  ·
                    rfl

theorem cell23_3394579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 7].length) (baseStart_3394579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394579 prefixEnd_3394579 := by exact prefixLift 3394579
  have htrace : WordTrace (prefixWord ++ tailWord_3394579) baseStart_3394579 baseEnd_3394579 := by
    simpa [prefixWord, tailWord_3394579, baseEnd_3394579] using wordTrace_append hprefix tailTrace_3394579
  have hstable : (prefixWord ++ tailWord_3394579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394579).length < 2 ^ (prefixWord ++ tailWord_3394579).sum := by decide
  have hdescent : baseEnd_3394579 < baseStart_3394579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394586 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3394586 : Nat := 118140960795 + 3394586 * 2 ^ 59
def prefixEnd_3394586 : Nat := 4983230072969 + 3 ^ 40 * 3394586 * 2
def baseEnd_3394586 : Nat := 1743054241023360900363589

theorem tailTrace_3394586 : CollatzResearch.WordTrace tailWord_3394586 prefixEnd_3394586 1743054241023360900363589 := by
  unfold tailWord_3394586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30952680720000536494430903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82540481920001430651815741 30952680720000536494430903)
  ·
    refine ⟨46429021080000804741646355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30952680720000536494430903 46429021080000804741646355)
    ·
      refine ⟨69643531620001207112469533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46429021080000804741646355 69643531620001207112469533)
      ·
        refine ⟨26116324357500452667176075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69643531620001207112469533 26116324357500452667176075)
        ·
          refine ⟨39174486536250679000764113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26116324357500452667176075 39174486536250679000764113)
          ·
            refine ⟨29380864902188009250573085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39174486536250679000764113 29380864902188009250573085)
            ·
              refine ⟨11017824338320503468964907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29380864902188009250573085 11017824338320503468964907)
              ·
                refine ⟨16526736507480755203447361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017824338320503468964907 16526736507480755203447361)
                ·
                  refine ⟨12395052380610566402585521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16526736507480755203447361 12395052380610566402585521)
                  ·
                    refine ⟨9296289285457924801939141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12395052380610566402585521 9296289285457924801939141)
                    ·
                      refine ⟨1743054241023360900363589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9296289285457924801939141 1743054241023360900363589)
                      ·
                        rfl

theorem cell23_3394586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3394586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394586 prefixEnd_3394586 := by exact prefixLift 3394586
  have htrace : WordTrace (prefixWord ++ tailWord_3394586) baseStart_3394586 baseEnd_3394586 := by
    simpa [prefixWord, tailWord_3394586, baseEnd_3394586] using wordTrace_append hprefix tailTrace_3394586
  have hstable : (prefixWord ++ tailWord_3394586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394586).length < 2 ^ (prefixWord ++ tailWord_3394586).sum := by decide
  have hdescent : baseEnd_3394586 < baseStart_3394586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394596 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 9]
def baseStart_3394596 : Nat := 118140960795 + 3394596 * 2 ^ 59
def prefixEnd_3394596 : Nat := 4983230072969 + 3 ^ 40 * 3394596 * 2
def baseEnd_3394596 : Nat := 193673263981100651248727

theorem tailTrace_3394596 : CollatzResearch.WordTrace tailWord_3394596 prefixEnd_3394596 193673263981100651248727 := by
  unfold tailWord_3394596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61905543804982958842793821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82540725073310611790391761 61905543804982958842793821)
  ·
    refine ⟨23214578926868609566047683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61905543804982958842793821 23214578926868609566047683)
    ·
      refine ⟨34821868390302914349071525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23214578926868609566047683 34821868390302914349071525)
      ·
        refine ⟨6529100323181796440450911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34821868390302914349071525 6529100323181796440450911)
        ·
          refine ⟨9793650484772694660676367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529100323181796440450911 9793650484772694660676367)
          ·
            refine ⟨14690475727159041991014551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793650484772694660676367 14690475727159041991014551)
            ·
              refine ⟨22035713590738562986521827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14690475727159041991014551 22035713590738562986521827)
              ·
                refine ⟨33053570386107844479782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22035713590738562986521827 33053570386107844479782741)
                ·
                  refine ⟨193673263981100651248727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33053570386107844479782741 193673263981100651248727)
                  ·
                    rfl

theorem cell23_3394596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_3394596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394596 prefixEnd_3394596 := by exact prefixLift 3394596
  have htrace : WordTrace (prefixWord ++ tailWord_3394596) baseStart_3394596 baseEnd_3394596 := by
    simpa [prefixWord, tailWord_3394596, baseEnd_3394596] using wordTrace_append hprefix tailTrace_3394596
  have hstable : (prefixWord ++ tailWord_3394596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394596).length < 2 ^ (prefixWord ++ tailWord_3394596).sum := by decide
  have hdescent : baseEnd_3394596 < baseStart_3394596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394630 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3394630 : Nat := 118140960795 + 3394630 * 2 ^ 59
def prefixEnd_3394630 : Nat := 4983230072969 + 3 ^ 40 * 3394630 * 2
def baseEnd_3394630 : Nat := 193675203796906525357043

theorem tailTrace_3394630 : CollatzResearch.WordTrace tailWord_3394630 prefixEnd_3394630 193675203796906525357043 := by
  unfold tailWord_3394630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869135240370085671635167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82541551794561827661550229 3869135240370085671635167)
  ·
    refine ⟨5803702860555128507452751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3869135240370085671635167 5803702860555128507452751)
    ·
      refine ⟨8705554290832692761179127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5803702860555128507452751 8705554290832692761179127)
      ·
        refine ⟨13058331436249039141768691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8705554290832692761179127 13058331436249039141768691)
        ·
          refine ⟨19587497154373558712653037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13058331436249039141768691 19587497154373558712653037)
          ·
            refine ⟨7345311432890084517244889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19587497154373558712653037 7345311432890084517244889)
            ·
              refine ⟨5508983574667563387933667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345311432890084517244889 5508983574667563387933667)
              ·
                refine ⟨8263475362001345081900501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508983574667563387933667 8263475362001345081900501)
                ·
                  refine ⟨193675203796906525357043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8263475362001345081900501 193675203796906525357043)
                  ·
                    rfl

theorem cell23_3394630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3394630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394630 prefixEnd_3394630 := by exact prefixLift 3394630
  have htrace : WordTrace (prefixWord ++ tailWord_3394630) baseStart_3394630 baseEnd_3394630 := by
    simpa [prefixWord, tailWord_3394630, baseEnd_3394630] using wordTrace_append hprefix tailTrace_3394630
  have hstable : (prefixWord ++ tailWord_3394630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394630).length < 2 ^ (prefixWord ++ tailWord_3394630).sum := by decide
  have hdescent : baseEnd_3394630 < baseStart_3394630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394639 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 8]
def baseStart_3394639 : Nat := 118140960795 + 3394639 * 2 ^ 59
def prefixEnd_3394639 : Nat := 4983230072969 + 3 ^ 40 * 3394639 * 2
def baseEnd_3394639 : Nat := 581027151832683064333615

theorem tailTrace_3394639 : CollatzResearch.WordTrace tailWord_3394639 prefixEnd_3394639 581027151832683064333615 := by
  unfold tailWord_3394639
  simp only [CollatzResearch.WordTrace]
  refine ⟨123812655948810136029402971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82541770632540090686268647 123812655948810136029402971)
  ·
    refine ⟨185718983923215204044104457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123812655948810136029402971 185718983923215204044104457)
    ·
      refine ⟨139289237942411403033078343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185718983923215204044104457 139289237942411403033078343)
      ·
        refine ⟨208933856913617104549617515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139289237942411403033078343 208933856913617104549617515)
        ·
          refine ⟨313400785370425656824426273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208933856913617104549617515 313400785370425656824426273)
          ·
            refine ⟨235050589027819242618319705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313400785370425656824426273 235050589027819242618319705)
            ·
              refine ⟨176287941770864431963739779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235050589027819242618319705 176287941770864431963739779)
              ·
                refine ⟨264431912656296647945609669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176287941770864431963739779 264431912656296647945609669)
                ·
                  refine ⟨49580983623055621489801813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264431912656296647945609669 49580983623055621489801813)
                  ·
                    refine ⟨581027151832683064333615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49580983623055621489801813 581027151832683064333615)
                    ·
                      rfl

theorem cell23_3394639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_3394639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394639 prefixEnd_3394639 := by exact prefixLift 3394639
  have htrace : WordTrace (prefixWord ++ tailWord_3394639) baseStart_3394639 baseEnd_3394639 := by
    simpa [prefixWord, tailWord_3394639, baseEnd_3394639] using wordTrace_append hprefix tailTrace_3394639
  have hstable : (prefixWord ++ tailWord_3394639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394639).length < 2 ^ (prefixWord ++ tailWord_3394639).sum := by decide
  have hdescent : baseEnd_3394639 < baseStart_3394639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394664 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 5]
def baseStart_3394664 : Nat := 118140960795 + 3394664 * 2 ^ 59
def prefixEnd_3394664 : Nat := 4983230072969 + 3 ^ 40 * 3394664 * 2
def baseEnd_3394664 : Nat := 193677143612712399465359

theorem tailTrace_3394664 : CollatzResearch.WordTrace tailWord_3394664 prefixEnd_3394664 193677143612712399465359 := by
  unfold tailWord_3394664
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906783886859782649531523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82542378515813043532708697 61906783886859782649531523)
  ·
    refine ⟨92860175830289673974297285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61906783886859782649531523 92860175830289673974297285)
    ·
      refine ⟨17411282968179313870180741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92860175830289673974297285 17411282968179313870180741)
      ·
        refine ⟨3264615556533621350658889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17411282968179313870180741 3264615556533621350658889)
        ·
          refine ⟨2448461667400216012994167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3264615556533621350658889 2448461667400216012994167)
          ·
            refine ⟨3672692501100324019491251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448461667400216012994167 3672692501100324019491251)
            ·
              refine ⟨5509038751650486029236877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672692501100324019491251 5509038751650486029236877)
              ·
                refine ⟨2065889531868932260963829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509038751650486029236877 2065889531868932260963829)
                ·
                  refine ⟨193677143612712399465359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065889531868932260963829 193677143612712399465359)
                  ·
                    rfl

theorem cell23_3394664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 5].length) (baseStart_3394664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394664 prefixEnd_3394664 := by exact prefixLift 3394664
  have htrace : WordTrace (prefixWord ++ tailWord_3394664) baseStart_3394664 baseEnd_3394664 := by
    simpa [prefixWord, tailWord_3394664, baseEnd_3394664] using wordTrace_append hprefix tailTrace_3394664
  have hstable : (prefixWord ++ tailWord_3394664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394664).length < 2 ^ (prefixWord ++ tailWord_3394664).sum := by decide
  have hdescent : baseEnd_3394664 < baseStart_3394664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394723 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 5, 2]
def baseStart_3394723 : Nat := 118140960795 + 3394723 * 2 ^ 59
def prefixEnd_3394723 : Nat := 4983230072969 + 3 ^ 40 * 3394723 * 2
def baseEnd_3394723 : Nat := 1743124587873026864350459

theorem tailTrace_3394723 : CollatzResearch.WordTrace tailWord_3394723 prefixEnd_3394723 1743124587873026864350459 := by
  unfold tailWord_3394723
  simp only [CollatzResearch.WordTrace]
  refine ⟨123815719680505818375460823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82543813120337212250307215 123815719680505818375460823)
  ·
    refine ⟨185723579520758727563191235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123815719680505818375460823 185723579520758727563191235)
    ·
      refine ⟨278585369281138091344786853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185723579520758727563191235 278585369281138091344786853)
      ·
        refine ⟨52234756740213392127147535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278585369281138091344786853 52234756740213392127147535)
        ·
          refine ⟨78352135110320088190721303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52234756740213392127147535 78352135110320088190721303)
          ·
            refine ⟨117528202665480132286081955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78352135110320088190721303 117528202665480132286081955)
            ·
              refine ⟨176292303998220198429122933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117528202665480132286081955 176292303998220198429122933)
              ·
                refine ⟨16527403499833143602730275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176292303998220198429122933 16527403499833143602730275)
                ·
                  refine ⟨24791105249749715404095413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527403499833143602730275 24791105249749715404095413)
                  ·
                    refine ⟨2324166117164035819133945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24791105249749715404095413 2324166117164035819133945)
                    ·
                      refine ⟨1743124587873026864350459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324166117164035819133945 1743124587873026864350459)
                      ·
                        rfl

theorem cell23_3394723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_3394723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394723 prefixEnd_3394723 := by exact prefixLift 3394723
  have htrace : WordTrace (prefixWord ++ tailWord_3394723) baseStart_3394723 baseEnd_3394723 := by
    simpa [prefixWord, tailWord_3394723, baseEnd_3394723] using wordTrace_append hprefix tailTrace_3394723
  have hstable : (prefixWord ++ tailWord_3394723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394723).length < 2 ^ (prefixWord ++ tailWord_3394723).sum := by decide
  have hdescent : baseEnd_3394723 < baseStart_3394723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394746 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_3394746 : Nat := 118140960795 + 3394746 * 2 ^ 59
def prefixEnd_3394746 : Nat := 4983230072969 + 3 ^ 40 * 3394746 * 2
def baseEnd_3394746 : Nat := 581045465976026758120951

theorem tailTrace_3394746 : CollatzResearch.WordTrace tailWord_3394746 prefixEnd_3394746 581045465976026758120951 := by
  unfold tailWord_3394746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30954139639855623325887023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82544372372948328869032061 30954139639855623325887023)
  ·
    refine ⟨46431209459783434988830535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30954139639855623325887023 46431209459783434988830535)
    ·
      refine ⟨69646814189675152483245803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46431209459783434988830535 69646814189675152483245803)
      ·
        refine ⟨104470221284512728724868705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69646814189675152483245803 104470221284512728724868705)
        ·
          refine ⟨78352665963384546543651529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104470221284512728724868705 78352665963384546543651529)
          ·
            refine ⟨58764499472538409907738647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78352665963384546543651529 58764499472538409907738647)
            ·
              refine ⟨88146749208807614861607971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58764499472538409907738647 88146749208807614861607971)
              ·
                refine ⟨132220123813211422292411957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88146749208807614861607971 132220123813211422292411957)
                ·
                  refine ⟨12395636607488570839913621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132220123813211422292411957 12395636607488570839913621)
                  ·
                    refine ⟨581045465976026758120951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12395636607488570839913621 581045465976026758120951)
                    ·
                      rfl

theorem cell23_3394746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3394746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394746 prefixEnd_3394746 := by exact prefixLift 3394746
  have htrace : WordTrace (prefixWord ++ tailWord_3394746) baseStart_3394746 baseEnd_3394746 := by
    simpa [prefixWord, tailWord_3394746, baseEnd_3394746] using wordTrace_append hprefix tailTrace_3394746
  have hstable : (prefixWord ++ tailWord_3394746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394746).length < 2 ^ (prefixWord ++ tailWord_3394746).sum := by decide
  have hdescent : baseEnd_3394746 < baseStart_3394746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394770 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3394770 : Nat := 118140960795 + 3394770 * 2 ^ 59
def prefixEnd_3394770 : Nat := 4983230072969 + 3 ^ 40 * 3394770 * 2
def baseEnd_3394770 : Nat := 1743148721463788180462743

theorem tailTrace_3394770 : CollatzResearch.WordTrace tailWord_3394770 prefixEnd_3394770 1743148721463788180462743 := by
  unfold tailWord_3394770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30954358477833886350605441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82544955940890363601614509 30954358477833886350605441)
  ·
    refine ⟨23215768858375414762954081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30954358477833886350605441 23215768858375414762954081)
    ·
      refine ⟨17411826643781561072215561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23215768858375414762954081 17411826643781561072215561)
      ·
        refine ⟨13058869982836170804161671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411826643781561072215561 13058869982836170804161671)
        ·
          refine ⟨19588304974254256206242507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13058869982836170804161671 19588304974254256206242507)
          ·
            refine ⟨29382457461381384309363761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19588304974254256206242507 29382457461381384309363761)
            ·
              refine ⟨22036843096036038232022821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29382457461381384309363761 22036843096036038232022821)
              ·
                refine ⟨4131908080506757168504279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22036843096036038232022821 4131908080506757168504279)
                ·
                  refine ⟨6197862120760135752756419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131908080506757168504279 6197862120760135752756419)
                  ·
                    refine ⟨9296793181140203629134629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6197862120760135752756419 9296793181140203629134629)
                    ·
                      refine ⟨1743148721463788180462743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9296793181140203629134629 1743148721463788180462743)
                      ·
                        rfl

theorem cell23_3394770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3394770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394770 prefixEnd_3394770 := by exact prefixLift 3394770
  have htrace : WordTrace (prefixWord ++ tailWord_3394770) baseStart_3394770 baseEnd_3394770 := by
    simpa [prefixWord, tailWord_3394770, baseEnd_3394770] using wordTrace_append hprefix tailTrace_3394770
  have hstable : (prefixWord ++ tailWord_3394770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394770).length < 2 ^ (prefixWord ++ tailWord_3394770).sum := by decide
  have hdescent : baseEnd_3394770 < baseStart_3394770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394774 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3394774 : Nat := 118140960795 + 3394774 * 2 ^ 59
def prefixEnd_3394774 : Nat := 4983230072969 + 3 ^ 40 * 3394774 * 2
def baseEnd_3394774 : Nat := 1743150775386406164812725

theorem tailTrace_3394774 : CollatzResearch.WordTrace tailWord_3394774 prefixEnd_3394774 1743150775386406164812725 := by
  unfold tailWord_3394774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738598737707565880347961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82545053202214036057044917 7738598737707565880347961)
  ·
    refine ⟨5803949053280674410260971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7738598737707565880347961 5803949053280674410260971)
    ·
      refine ⟨8705923579921011615391457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5803949053280674410260971 8705923579921011615391457)
      ·
        refine ⟨6529442684940758711543593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705923579921011615391457 6529442684940758711543593)
        ·
          refine ⟨4897082013705569033657695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6529442684940758711543593 4897082013705569033657695)
          ·
            refine ⟨7345623020558353550486543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897082013705569033657695 7345623020558353550486543)
            ·
              refine ⟨11018434530837530325729815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345623020558353550486543 11018434530837530325729815)
              ·
                refine ⟨16527651796256295488594723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018434530837530325729815 16527651796256295488594723)
                ·
                  refine ⟨24791477694384443232892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16527651796256295488594723 24791477694384443232892085)
                  ·
                    refine ⟨2324201033848541553083633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24791477694384443232892085 2324201033848541553083633)
                    ·
                      refine ⟨1743150775386406164812725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324201033848541553083633 1743150775386406164812725)
                      ·
                        rfl

theorem cell23_3394774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3394774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394774 prefixEnd_3394774 := by exact prefixLift 3394774
  have htrace : WordTrace (prefixWord ++ tailWord_3394774) baseStart_3394774 baseEnd_3394774 := by
    simpa [prefixWord, tailWord_3394774, baseEnd_3394774] using wordTrace_append hprefix tailTrace_3394774
  have hstable : (prefixWord ++ tailWord_3394774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394774).length < 2 ^ (prefixWord ++ tailWord_3394774).sum := by decide
  have hdescent : baseEnd_3394774 < baseStart_3394774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394781 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3394781 : Nat := 118140960795 + 3394781 * 2 ^ 59
def prefixEnd_3394781 : Nat := 4983230072969 + 3 ^ 40 * 3394781 * 2
def baseEnd_3394781 : Nat := 1743154369750987637425193

theorem tailTrace_3394781 : CollatzResearch.WordTrace tailWord_3394781 prefixEnd_3394781 1743154369750987637425193 := by
  unfold tailWord_3394781
  simp only [CollatzResearch.WordTrace]
  refine ⟨123817835114295694281072197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82545223409530462854048131 123817835114295694281072197)
  ·
    refine ⟨23215844083930442677701037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123817835114295694281072197 23215844083930442677701037)
    ·
      refine ⟨8705941531473916004137889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23215844083930442677701037 8705941531473916004137889)
      ·
        refine ⟨6529456148605437003103417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8705941531473916004137889 6529456148605437003103417)
        ·
          refine ⟨4897092111454077752327563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6529456148605437003103417 4897092111454077752327563)
          ·
            refine ⟨7345638167181116628491345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897092111454077752327563 7345638167181116628491345)
            ·
              refine ⟨5509228625385837471368509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345638167181116628491345 5509228625385837471368509)
              ·
                refine ⟨2065960734519689051763191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509228625385837471368509 2065960734519689051763191)
                ·
                  refine ⟨3098941101779533577644787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065960734519689051763191 3098941101779533577644787)
                  ·
                    refine ⟨4648411652669300366467181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3098941101779533577644787 4648411652669300366467181)
                    ·
                      refine ⟨1743154369750987637425193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4648411652669300366467181 1743154369750987637425193)
                      ·
                        rfl

theorem cell23_3394781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3394781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394781 prefixEnd_3394781 := by exact prefixLift 3394781
  have htrace : WordTrace (prefixWord ++ tailWord_3394781) baseStart_3394781 baseEnd_3394781 := by
    simpa [prefixWord, tailWord_3394781, baseEnd_3394781] using wordTrace_append hprefix tailTrace_3394781
  have hstable : (prefixWord ++ tailWord_3394781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394781).length < 2 ^ (prefixWord ++ tailWord_3394781).sum := by decide
  have hdescent : baseEnd_3394781 < baseStart_3394781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394783 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3394783 : Nat := 118140960795 + 3394783 * 2 ^ 59
def prefixEnd_3394783 : Nat := 4983230072969 + 3 ^ 40 * 3394783 * 2
def baseEnd_3394783 : Nat := 1743155396712296629600183

theorem tailTrace_3394783 : CollatzResearch.WordTrace tailWord_3394783 prefixEnd_3394783 1743155396712296629600183 := by
  unfold tailWord_3394783
  simp only [CollatzResearch.WordTrace]
  refine ⟨123817908060288448622645003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82545272040192299081763335 123817908060288448622645003)
  ·
    refine ⟨185726862090432672933967505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123817908060288448622645003 185726862090432672933967505)
    ·
      refine ⟨139295146567824504700475629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185726862090432672933967505 139295146567824504700475629)
      ·
        refine ⟨52235679962934189262678361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139295146567824504700475629 52235679962934189262678361)
        ·
          refine ⟨39176759972200641947008771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52235679962934189262678361 39176759972200641947008771)
          ·
            refine ⟨58765139958300962920513157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39176759972200641947008771 58765139958300962920513157)
            ·
              refine ⟨11018463742181430547596217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58765139958300962920513157 11018463742181430547596217)
              ·
                refine ⟨8263847806636072910697163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11018463742181430547596217 8263847806636072910697163)
                ·
                  refine ⟨12395771709954109366045745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8263847806636072910697163 12395771709954109366045745)
                  ·
                    refine ⟨9296828782465582024534309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12395771709954109366045745 9296828782465582024534309)
                    ·
                      refine ⟨1743155396712296629600183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9296828782465582024534309 1743155396712296629600183)
                      ·
                        rfl

theorem cell23_3394783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3394783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394783 prefixEnd_3394783 := by exact prefixLift 3394783
  have htrace : WordTrace (prefixWord ++ tailWord_3394783) baseStart_3394783 baseEnd_3394783 := by
    simpa [prefixWord, tailWord_3394783, baseEnd_3394783] using wordTrace_append hprefix tailTrace_3394783
  have hstable : (prefixWord ++ tailWord_3394783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394783).length < 2 ^ (prefixWord ++ tailWord_3394783).sum := by decide
  have hdescent : baseEnd_3394783 < baseStart_3394783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394797 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3394797 : Nat := 118140960795 + 3394797 * 2 ^ 59
def prefixEnd_3394797 : Nat := 4983230072969 + 3 ^ 40 * 3394797 * 2
def baseEnd_3394797 : Nat := 581054195147153191608373

theorem tailTrace_3394797 : CollatzResearch.WordTrace tailWord_3394797 prefixEnd_3394797 581054195147153191608373 := by
  unfold tailWord_3394797
  simp only [CollatzResearch.WordTrace]
  refine ⟨123818418682237729013654645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82545612454825152675769763 123818418682237729013654645)
  ·
    refine ⟨11607976751459787095030123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123818418682237729013654645 11607976751459787095030123)
    ·
      refine ⟨17411965127189680642545185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11607976751459787095030123 17411965127189680642545185)
      ·
        refine ⟨13058973845392260481908889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411965127189680642545185 13058973845392260481908889)
        ·
          refine ⟨9794230384044195361431667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13058973845392260481908889 9794230384044195361431667)
          ·
            refine ⟨14691345576066293042147501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794230384044195361431667 14691345576066293042147501)
            ·
              refine ⟨5509254591024859890805313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14691345576066293042147501 5509254591024859890805313)
              ·
                refine ⟨4131940943268644918103985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5509254591024859890805313 4131940943268644918103985)
                ·
                  refine ⟨3098955707451483688577989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131940943268644918103985 3098955707451483688577989)
                  ·
                    refine ⟨581054195147153191608373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098955707451483688577989 581054195147153191608373)
                    ·
                      rfl

theorem cell23_3394797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3394797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394797 prefixEnd_3394797 := by exact prefixLift 3394797
  have htrace : WordTrace (prefixWord ++ tailWord_3394797) baseStart_3394797 baseEnd_3394797 := by
    simpa [prefixWord, tailWord_3394797, baseEnd_3394797] using wordTrace_append hprefix tailTrace_3394797
  have hstable : (prefixWord ++ tailWord_3394797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394797).length < 2 ^ (prefixWord ++ tailWord_3394797).sum := by decide
  have hdescent : baseEnd_3394797 < baseStart_3394797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394814 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3394814 : Nat := 118140960795 + 3394814 * 2 ^ 59
def prefixEnd_3394814 : Nat := 4983230072969 + 3 ^ 40 * 3394814 * 2
def baseEnd_3394814 : Nat := 581057104870862002770847

theorem tailTrace_3394814 : CollatzResearch.WordTrace tailWord_3394814 prefixEnd_3394814 581057104870862002770847 := by
  unfold tailWord_3394814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477379840397017614627937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82546025815450760611348997 15477379840397017614627937)
  ·
    refine ⟨11608034880297763210970953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15477379840397017614627937 11608034880297763210970953)
    ·
      refine ⟨8706026160223322408228215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11608034880297763210970953 8706026160223322408228215)
      ·
        refine ⟨13059039240334983612342323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706026160223322408228215 13059039240334983612342323)
        ·
          refine ⟨19588558860502475418513485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13059039240334983612342323 19588558860502475418513485)
          ·
            refine ⟨7345709572688428281942557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19588558860502475418513485 7345709572688428281942557)
            ·
              refine ⟨2754641089758160605728459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7345709572688428281942557 2754641089758160605728459)
              ·
                refine ⟨4131961634637240908592689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754641089758160605728459 4131961634637240908592689)
                ·
                  refine ⟨3098971225977930681444517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131961634637240908592689 3098971225977930681444517)
                  ·
                    refine ⟨581057104870862002770847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098971225977930681444517 581057104870862002770847)
                    ·
                      rfl

theorem cell23_3394814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3394814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394814 prefixEnd_3394814 := by exact prefixLift 3394814
  have htrace : WordTrace (prefixWord ++ tailWord_3394814) baseStart_3394814 baseEnd_3394814 := by
    simpa [prefixWord, tailWord_3394814, baseEnd_3394814] using wordTrace_append hprefix tailTrace_3394814
  have hstable : (prefixWord ++ tailWord_3394814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394814).length < 2 ^ (prefixWord ++ tailWord_3394814).sum := by decide
  have hdescent : baseEnd_3394814 < baseStart_3394814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394863 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_3394863 : Nat := 118140960795 + 3394863 * 2 ^ 59
def prefixEnd_3394863 : Nat := 4983230072969 + 3 ^ 40 * 3394863 * 2
def baseEnd_3394863 : Nat := 1743196475164656316599815

theorem tailTrace_3394863 : CollatzResearch.WordTrace tailWord_3394863 prefixEnd_3394863 1743196475164656316599815 := by
  unfold tailWord_3394863
  simp only [CollatzResearch.WordTrace]
  refine ⟨123820825899998622285557243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82547217266665748190371495 123820825899998622285557243)
  ·
    refine ⟨185731238849997933428335865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123820825899998622285557243 185731238849997933428335865)
    ·
      refine ⟨139298429137498450071251899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185731238849997933428335865 139298429137498450071251899)
      ·
        refine ⟨208947643706247675106877849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139298429137498450071251899 208947643706247675106877849)
        ·
          refine ⟨156710732779685756330158387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208947643706247675106877849 156710732779685756330158387)
          ·
            refine ⟨235066099169528634495237581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156710732779685756330158387 235066099169528634495237581)
            ·
              refine ⟨88149787188573237935714093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235066099169528634495237581 88149787188573237935714093)
              ·
                refine ⟨33056170195714964225892785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88149787188573237935714093 33056170195714964225892785)
                ·
                  refine ⟨24792127646786223169419589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33056170195714964225892785 24792127646786223169419589)
                  ·
                    refine ⟨4648523933772416844266173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24792127646786223169419589 4648523933772416844266173)
                    ·
                      refine ⟨1743196475164656316599815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4648523933772416844266173 1743196475164656316599815)
                      ·
                        rfl

theorem cell23_3394863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_3394863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394863 prefixEnd_3394863 := by exact prefixLift 3394863
  have htrace : WordTrace (prefixWord ++ tailWord_3394863) baseStart_3394863 baseEnd_3394863 := by
    simpa [prefixWord, tailWord_3394863, baseEnd_3394863] using wordTrace_append hprefix tailTrace_3394863
  have hstable : (prefixWord ++ tailWord_3394863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394863).length < 2 ^ (prefixWord ++ tailWord_3394863).sum := by decide
  have hdescent : baseEnd_3394863 < baseStart_3394863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394881 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3394881 : Nat := 118140960795 + 3394881 * 2 ^ 59
def prefixEnd_3394881 : Nat := 4983230072969 + 3 ^ 40 * 3394881 * 2
def baseEnd_3394881 : Nat := 1743205717816437246174733

theorem tailTrace_3394881 : CollatzResearch.WordTrace tailWord_3394881 prefixEnd_3394881 1743205717816437246174733 := by
  unfold tailWord_3394881
  simp only [CollatzResearch.WordTrace]
  refine ⟨123821482413933411359712497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82547654942622274239808331 123821482413933411359712497)
  ·
    refine ⟨92866111810450058519784373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123821482413933411359712497 92866111810450058519784373)
    ·
      refine ⟨8706197982229692986229785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92866111810450058519784373 8706197982229692986229785)
      ·
        refine ⟨6529648486672269739672339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8706197982229692986229785 6529648486672269739672339)
        ·
          refine ⟨9794472730008404609508509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529648486672269739672339 9794472730008404609508509)
          ·
            refine ⟨3672927273753151728565691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9794472730008404609508509 3672927273753151728565691)
            ·
              refine ⟨5509390910629727592848537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672927273753151728565691 5509390910629727592848537)
              ·
                refine ⟨4132043182972295694636403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5509390910629727592848537 4132043182972295694636403)
                ·
                  refine ⟨6198064774458443541954605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132043182972295694636403 6198064774458443541954605)
                  ·
                    refine ⟨2324274290421916328232977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6198064774458443541954605 2324274290421916328232977)
                    ·
                      refine ⟨1743205717816437246174733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324274290421916328232977 1743205717816437246174733)
                      ·
                        rfl

theorem cell23_3394881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3394881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394881 prefixEnd_3394881 := by exact prefixLift 3394881
  have htrace : WordTrace (prefixWord ++ tailWord_3394881) baseStart_3394881 baseEnd_3394881 := by
    simpa [prefixWord, tailWord_3394881, baseEnd_3394881] using wordTrace_append hprefix tailTrace_3394881
  have hstable : (prefixWord ++ tailWord_3394881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394881).length < 2 ^ (prefixWord ++ tailWord_3394881).sum := by decide
  have hdescent : baseEnd_3394881 < baseStart_3394881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394947 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 2, 5]
def baseStart_3394947 : Nat := 118140960795 + 3394947 * 2 ^ 59
def prefixEnd_3394947 : Nat := 4983230072969 + 3 ^ 40 * 3394947 * 2
def baseEnd_3394947 : Nat := 581079869179877995983143

theorem tailTrace_3394947 : CollatzResearch.WordTrace tailWord_3394947 prefixEnd_3394947 581079869179877995983143 := by
  unfold tailWord_3394947
  simp only [CollatzResearch.WordTrace]
  refine ⟨123823889631694304631615095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82549259754462869754410063 123823889631694304631615095)
  ·
    refine ⟨185735834447541456947422643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123823889631694304631615095 185735834447541456947422643)
    ·
      refine ⟨278603751671312185421133965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185735834447541456947422643 278603751671312185421133965)
      ·
        refine ⟨104476406876742069532925237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278603751671312185421133965 104476406876742069532925237)
        ·
          refine ⟨9794663144694569018711741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104476406876742069532925237 9794663144694569018711741)
          ·
            refine ⟨3672998679260463382016903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9794663144694569018711741 3672998679260463382016903)
            ·
              refine ⟨5509498018890695073025355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672998679260463382016903 5509498018890695073025355)
              ·
                refine ⟨8264247028336042609538033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509498018890695073025355 8264247028336042609538033)
                ·
                  refine ⟨6198185271252031957153525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8264247028336042609538033 6198185271252031957153525)
                  ·
                    refine ⟨581079869179877995983143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6198185271252031957153525 581079869179877995983143)
                    ·
                      rfl

theorem cell23_3394947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 5].length) (baseStart_3394947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394947 prefixEnd_3394947 := by exact prefixLift 3394947
  have htrace : WordTrace (prefixWord ++ tailWord_3394947) baseStart_3394947 baseEnd_3394947 := by
    simpa [prefixWord, tailWord_3394947, baseEnd_3394947] using wordTrace_append hprefix tailTrace_3394947
  have hstable : (prefixWord ++ tailWord_3394947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394947).length < 2 ^ (prefixWord ++ tailWord_3394947).sum := by decide
  have hdescent : baseEnd_3394947 < baseStart_3394947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394963 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_3394963 : Nat := 118140960795 + 3394963 * 2 ^ 59
def prefixEnd_3394963 : Nat := 4983230072969 + 3 ^ 40 * 3394963 * 2
def baseEnd_3394963 : Nat := 1743247823230105925349355

theorem tailTrace_3394963 : CollatzResearch.WordTrace tailWord_3394963 prefixEnd_3394963 1743247823230105925349355 := by
  unfold tailWord_3394963
  simp only [CollatzResearch.WordTrace]
  refine ⟨123824473199636339364197543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82549648799757559576131695 123824473199636339364197543)
  ·
    refine ⟨185736709799454509046296315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123824473199636339364197543 185736709799454509046296315)
    ·
      refine ⟨278605064699181763569444473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185736709799454509046296315 278605064699181763569444473)
      ·
        refine ⟨208953798524386322677083355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278605064699181763569444473 208953798524386322677083355)
        ·
          refine ⟨313430697786579484015625033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208953798524386322677083355 313430697786579484015625033)
          ·
            refine ⟨235073023339934613011718775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313430697786579484015625033 235073023339934613011718775)
            ·
              refine ⟨352609535009901919517578163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235073023339934613011718775 352609535009901919517578163)
              ·
                refine ⟨528914302514852879276367245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352609535009901919517578163 528914302514852879276367245)
                ·
                  refine ⟨198342863443069829728637717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528914302514852879276367245 198342863443069829728637717)
                  ·
                    refine ⟨9297321723893898268529893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 198342863443069829728637717 9297321723893898268529893)
                    ·
                      refine ⟨1743247823230105925349355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9297321723893898268529893 1743247823230105925349355)
                      ·
                        rfl

theorem cell23_3394963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_3394963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3394963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3394963 prefixEnd_3394963 := by exact prefixLift 3394963
  have htrace : WordTrace (prefixWord ++ tailWord_3394963) baseStart_3394963 baseEnd_3394963 := by
    simpa [prefixWord, tailWord_3394963, baseEnd_3394963] using wordTrace_append hprefix tailTrace_3394963
  have hstable : (prefixWord ++ tailWord_3394963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394963).length < 2 ^ (prefixWord ++ tailWord_3394963).sum := by decide
  have hdescent : baseEnd_3394963 < baseStart_3394963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395028 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_3395028 : Nat := 118140960795 + 3395028 * 2 ^ 59
def prefixEnd_3395028 : Nat := 4983230072969 + 3 ^ 40 * 3395028 * 2
def baseEnd_3395028 : Nat := 581093733157549390345519

theorem tailTrace_3395028 : CollatzResearch.WordTrace tailWord_3395028 prefixEnd_3395028 581093733157549390345519 := by
  unfold tailWord_3395028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61913421972200427732656869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82551229296267236976875825 61913421972200427732656869)
  ·
    refine ⟨11608766619787580199873163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61913421972200427732656869 11608766619787580199873163)
    ·
      refine ⟨17413149929681370299809745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11608766619787580199873163 17413149929681370299809745)
      ·
        refine ⟨13059862447261027724857309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17413149929681370299809745 13059862447261027724857309)
        ·
          refine ⟨4897448417722885396821491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13059862447261027724857309 4897448417722885396821491)
          ·
            refine ⟨7346172626584328095232237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897448417722885396821491 7346172626584328095232237)
            ·
              refine ⟨2754814734969123035712089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7346172626584328095232237 2754814734969123035712089)
              ·
                refine ⟨2066111051226842276784067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2754814734969123035712089 2066111051226842276784067)
                ·
                  refine ⟨3099166576840263415176101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066111051226842276784067 3099166576840263415176101)
                  ·
                    refine ⟨581093733157549390345519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099166576840263415176101 581093733157549390345519)
                    ·
                      rfl

theorem cell23_3395028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_3395028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395028 prefixEnd_3395028 := by exact prefixLift 3395028
  have htrace : WordTrace (prefixWord ++ tailWord_3395028) baseStart_3395028 baseEnd_3395028 := by
    simpa [prefixWord, tailWord_3395028, baseEnd_3395028] using wordTrace_append hprefix tailTrace_3395028
  have hstable : (prefixWord ++ tailWord_3395028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395028).length < 2 ^ (prefixWord ++ tailWord_3395028).sum := by decide
  have hdescent : baseEnd_3395028 < baseStart_3395028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395034 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_3395034 : Nat := 118140960795 + 3395034 * 2 ^ 59
def prefixEnd_3395034 : Nat := 4983230072969 + 3 ^ 40 * 3395034 * 2
def baseEnd_3395034 : Nat := 1743284280356575147561529

theorem tailTrace_3395034 : CollatzResearch.WordTrace tailWord_3395034 prefixEnd_3395034 1743284280356575147561529 := by
  unfold tailWord_3395034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30956765695594779622508039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82551375188252745660021437 30956765695594779622508039)
  ·
    refine ⟨46435148543392169433762059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30956765695594779622508039 46435148543392169433762059)
    ·
      refine ⟨69652722815088254150643089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46435148543392169433762059 69652722815088254150643089)
      ·
        refine ⟨52239542111316190612982317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69652722815088254150643089 52239542111316190612982317)
        ·
          refine ⟨19589828291743571479868369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52239542111316190612982317 19589828291743571479868369)
          ·
            refine ⟨14692371218807678609901277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19589828291743571479868369 14692371218807678609901277)
            ·
              refine ⟨5509639207052879478712979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14692371218807678609901277 5509639207052879478712979)
              ·
                refine ⟨8264458810579319218069469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509639207052879478712979 8264458810579319218069469)
                ·
                  refine ⟨3099172053967244706776051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8264458810579319218069469 3099172053967244706776051)
                  ·
                    refine ⟨4648758080950867060164077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099172053967244706776051 4648758080950867060164077)
                    ·
                      refine ⟨1743284280356575147561529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4648758080950867060164077 1743284280356575147561529)
                      ·
                        rfl

theorem cell23_3395034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_3395034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395034 prefixEnd_3395034 := by exact prefixLift 3395034
  have htrace : WordTrace (prefixWord ++ tailWord_3395034) baseStart_3395034 baseEnd_3395034 := by
    simpa [prefixWord, tailWord_3395034, baseEnd_3395034] using wordTrace_append hprefix tailTrace_3395034
  have hstable : (prefixWord ++ tailWord_3395034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395034).length < 2 ^ (prefixWord ++ tailWord_3395034).sum := by decide
  have hdescent : baseEnd_3395034 < baseStart_3395034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395057 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3395057 : Nat := 118140960795 + 3395057 * 2 ^ 59
def prefixEnd_3395057 : Nat := 4983230072969 + 3 ^ 40 * 3395057 * 2
def baseEnd_3395057 : Nat := 1743296090411628557573923

theorem tailTrace_3395057 : CollatzResearch.WordTrace tailWord_3395057 prefixEnd_3395057 1743296090411628557573923 := by
  unfold tailWord_3395057
  simp only [CollatzResearch.WordTrace]
  refine ⟨123827901661295793418119425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82551934440863862278746283 123827901661295793418119425)
  ·
    refine ⟨92870926245971845063589569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123827901661295793418119425 92870926245971845063589569)
    ·
      refine ⟨69653194684478883797692177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92870926245971845063589569 69653194684478883797692177)
      ·
        refine ⟨52239896013359162848269133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69653194684478883797692177 52239896013359162848269133)
        ·
          refine ⟨19589961005009686068100925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52239896013359162848269133 19589961005009686068100925)
          ·
            refine ⟨7346235376878632275537847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19589961005009686068100925 7346235376878632275537847)
            ·
              refine ⟨11019353065317948413306771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346235376878632275537847 11019353065317948413306771)
              ·
                refine ⟨16529029597976922619960157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11019353065317948413306771 16529029597976922619960157)
                ·
                  refine ⟨6198386099241345982485059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16529029597976922619960157 6198386099241345982485059)
                  ·
                    refine ⟨9297579148862018973727589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6198386099241345982485059 9297579148862018973727589)
                    ·
                      refine ⟨1743296090411628557573923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9297579148862018973727589 1743296090411628557573923)
                      ·
                        rfl

theorem cell23_3395057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3395057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395057 prefixEnd_3395057 := by exact prefixLift 3395057
  have htrace : WordTrace (prefixWord ++ tailWord_3395057) baseStart_3395057 baseEnd_3395057 := by
    simpa [prefixWord, tailWord_3395057, baseEnd_3395057] using wordTrace_append hprefix tailTrace_3395057
  have hstable : (prefixWord ++ tailWord_3395057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395057).length < 2 ^ (prefixWord ++ tailWord_3395057).sum := by decide
  have hdescent : baseEnd_3395057 < baseStart_3395057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395061 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3395061 : Nat := 118140960795 + 3395061 * 2 ^ 59
def prefixEnd_3395061 : Nat := 4983230072969 + 3 ^ 40 * 3395061 * 2
def baseEnd_3395061 : Nat := 1743298144334246541923905

theorem tailTrace_3395061 : CollatzResearch.WordTrace tailWord_3395061 prefixEnd_3395061 1743298144334246541923905 := by
  unfold tailWord_3395061
  simp only [CollatzResearch.WordTrace]
  refine ⟨123828047553281302101265037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82552031702187534734176691 123828047553281302101265037)
  ·
    refine ⟨46435517832480488287974389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123828047553281302101265037 46435517832480488287974389)
    ·
      refine ⟨4353329796795045776997599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46435517832480488287974389 4353329796795045776997599)
      ·
        refine ⟨6529994695192568665496399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353329796795045776997599 6529994695192568665496399)
        ·
          refine ⟨9794992042788852998244599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529994695192568665496399 9794992042788852998244599)
          ·
            refine ⟨14692488064183279497366899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794992042788852998244599 14692488064183279497366899)
            ·
              refine ⟨22038732096274919246050349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14692488064183279497366899 22038732096274919246050349)
              ·
                refine ⟨8264524536103094717268881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22038732096274919246050349 8264524536103094717268881)
                ·
                  refine ⟨6198393402077321037951661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8264524536103094717268881 6198393402077321037951661)
                  ·
                    refine ⟨2324397525778995389231873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6198393402077321037951661 2324397525778995389231873)
                    ·
                      refine ⟨1743298144334246541923905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324397525778995389231873 1743298144334246541923905)
                      ·
                        rfl

theorem cell23_3395061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3395061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395061 prefixEnd_3395061 := by exact prefixLift 3395061
  have htrace : WordTrace (prefixWord ++ tailWord_3395061) baseStart_3395061 baseEnd_3395061 := by
    simpa [prefixWord, tailWord_3395061, baseEnd_3395061] using wordTrace_append hprefix tailTrace_3395061
  have hstable : (prefixWord ++ tailWord_3395061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395061).length < 2 ^ (prefixWord ++ tailWord_3395061).sum := by decide
  have hdescent : baseEnd_3395061 < baseStart_3395061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395104 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3395104 : Nat := 118140960795 + 3395104 * 2 ^ 59
def prefixEnd_3395104 : Nat := 4983230072969 + 3 ^ 40 * 3395104 * 2
def baseEnd_3395104 : Nat := 1743320224002389873686207

theorem tailTrace_3395104 : CollatzResearch.WordTrace tailWord_3395104 prefixEnd_3395104 1743320224002389873686207 := by
  unfold tailWord_3395104
  simp only [CollatzResearch.WordTrace]
  refine ⟨61914807946062760222540183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82553077261417013630053577 61914807946062760222540183)
  ·
    refine ⟨92872211919094140333810275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61914807946062760222540183 92872211919094140333810275)
    ·
      refine ⟨139308317878641210500715413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92872211919094140333810275 139308317878641210500715413)
      ·
        refine ⟨6530077400561306742221035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139308317878641210500715413 6530077400561306742221035)
        ·
          refine ⟨9795116100841960113331553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6530077400561306742221035 9795116100841960113331553)
          ·
            refine ⟨7346337075631470084998665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9795116100841960113331553 7346337075631470084998665)
            ·
              refine ⟨5509752806723602563748999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346337075631470084998665 5509752806723602563748999)
              ·
                refine ⟨8264629210085403845623499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509752806723602563748999 8264629210085403845623499)
                ·
                  refine ⟨12396943815128105768435249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8264629210085403845623499 12396943815128105768435249)
                  ·
                    refine ⟨9297707861346079326326437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12396943815128105768435249 9297707861346079326326437)
                    ·
                      refine ⟨1743320224002389873686207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9297707861346079326326437 1743320224002389873686207)
                      ·
                        rfl

theorem cell23_3395104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3395104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395104 prefixEnd_3395104 := by exact prefixLift 3395104
  have htrace : WordTrace (prefixWord ++ tailWord_3395104) baseStart_3395104 baseEnd_3395104 := by
    simpa [prefixWord, tailWord_3395104, baseEnd_3395104] using wordTrace_append hprefix tailTrace_3395104
  have hstable : (prefixWord ++ tailWord_3395104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395104).length < 2 ^ (prefixWord ++ tailWord_3395104).sum := by decide
  have hdescent : baseEnd_3395104 < baseStart_3395104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395120 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_3395120 : Nat := 118140960795 + 3395120 * 2 ^ 59
def prefixEnd_3395120 : Nat := 4983230072969 + 3 ^ 40 * 3395120 * 2
def baseEnd_3395120 : Nat := 1743328439692861811086133

theorem tailTrace_3395120 : CollatzResearch.WordTrace tailWord_3395120 prefixEnd_3395120 1743328439692861811086133 := by
  unfold tailWord_3395120
  simp only [CollatzResearch.WordTrace]
  refine ⟨61915099730033777588831407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82553466306711703451775209 61915099730033777588831407)
  ·
    refine ⟨92872649595050666383247111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61915099730033777588831407 92872649595050666383247111)
    ·
      refine ⟨139308974392575999574870667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92872649595050666383247111 139308974392575999574870667)
      ·
        refine ⟨208963461588863999362306001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139308974392575999574870667 208963461588863999362306001)
        ·
          refine ⟨156722596191647999521729501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208963461588863999362306001 156722596191647999521729501)
          ·
            refine ⟨58770973571867999820648563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156722596191647999521729501 58770973571867999820648563)
            ·
              refine ⟨88156460357801999730972845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58770973571867999820648563 88156460357801999730972845)
              ·
                refine ⟨33058672634175749899114817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88156460357801999730972845 33058672634175749899114817)
                ·
                  refine ⟨24794004475631812424336113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33058672634175749899114817 24794004475631812424336113)
                  ·
                    refine ⟨18595503356723859318252085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24794004475631812424336113 18595503356723859318252085)
                    ·
                      refine ⟨1743328439692861811086133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18595503356723859318252085 1743328439692861811086133)
                      ·
                        rfl

theorem cell23_3395120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_3395120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395120 prefixEnd_3395120 := by exact prefixLift 3395120
  have htrace : WordTrace (prefixWord ++ tailWord_3395120) baseStart_3395120 baseEnd_3395120 := by
    simpa [prefixWord, tailWord_3395120, baseEnd_3395120] using wordTrace_append hprefix tailTrace_3395120
  have hstable : (prefixWord ++ tailWord_3395120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395120).length < 2 ^ (prefixWord ++ tailWord_3395120).sum := by decide
  have hdescent : baseEnd_3395120 < baseStart_3395120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395237 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3395237 : Nat := 118140960795 + 3395237 * 2 ^ 59
def prefixEnd_3395237 : Nat := 4983230072969 + 3 ^ 40 * 3395237 * 2
def baseEnd_3395237 : Nat := 1743388516929437853323095

theorem tailTrace_3395237 : CollatzResearch.WordTrace tailWord_3395237 prefixEnd_3395237 1743388516929437853323095 := by
  unfold tailWord_3395237
  simp only [CollatzResearch.WordTrace]
  refine ⟨123834466800643684159671965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82556311200429122773114643 123834466800643684159671965)
  ·
    refine ⟨46437925050241381559876987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123834466800643684159671965 46437925050241381559876987)
    ·
      refine ⟨69656887575362072339815481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46437925050241381559876987 69656887575362072339815481)
      ·
        refine ⟨52242665681521554254861611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69656887575362072339815481 52242665681521554254861611)
        ·
          refine ⟨78363998522282331382292417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52242665681521554254861611 78363998522282331382292417)
          ·
            refine ⟨58772998891711748536719313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78363998522282331382292417 58772998891711748536719313)
            ·
              refine ⟨44079749168783811402539485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58772998891711748536719313 44079749168783811402539485)
              ·
                refine ⟨16529905938293929275952307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44079749168783811402539485 16529905938293929275952307)
                ·
                  refine ⟨24794858907440893913928461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16529905938293929275952307 24794858907440893913928461)
                  ·
                    refine ⟨9298072090290335217723173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24794858907440893913928461 9298072090290335217723173)
                    ·
                      refine ⟨1743388516929437853323095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9298072090290335217723173 1743388516929437853323095)
                      ·
                        rfl

theorem cell23_3395237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3395237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395237 prefixEnd_3395237 := by exact prefixLift 3395237
  have htrace : WordTrace (prefixWord ++ tailWord_3395237) baseStart_3395237 baseEnd_3395237 := by
    simpa [prefixWord, tailWord_3395237, baseEnd_3395237] using wordTrace_append hprefix tailTrace_3395237
  have hstable : (prefixWord ++ tailWord_3395237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395237).length < 2 ^ (prefixWord ++ tailWord_3395237).sum := by decide
  have hdescent : baseEnd_3395237 < baseStart_3395237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395264 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_3395264 : Nat := 118140960795 + 3395264 * 2 ^ 59
def prefixEnd_3395264 : Nat := 4983230072969 + 3 ^ 40 * 3395264 * 2
def baseEnd_3395264 : Nat := 581134126969036415895157

theorem tailTrace_3395264 : CollatzResearch.WordTrace tailWord_3395264 prefixEnd_3395264 581134126969036415895157 := by
  unfold tailWord_3395264
  simp only [CollatzResearch.WordTrace]
  refine ⟨61917725785772933885452423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82556967714363911847269897 61917725785772933885452423)
  ·
    refine ⟨92876588678659400828178635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61917725785772933885452423 92876588678659400828178635)
    ·
      refine ⟨139314883017989101242267953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92876588678659400828178635 139314883017989101242267953)
      ·
        refine ⟨104486162263491825931700965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139314883017989101242267953 104486162263491825931700965)
        ·
          refine ⟨19591155424404717362193931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104486162263491825931700965 19591155424404717362193931)
          ·
            refine ⟨29386733136607076043290897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19591155424404717362193931 29386733136607076043290897)
            ·
              refine ⟨22040049852455307032468173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29386733136607076043290897 22040049852455307032468173)
              ·
                refine ⟨8265018694670740137175565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22040049852455307032468173 8265018694670740137175565)
                ·
                  refine ⟨3099382010501527551440837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8265018694670740137175565 3099382010501527551440837)
                  ·
                    refine ⟨581134126969036415895157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099382010501527551440837 581134126969036415895157)
                    ·
                      rfl

theorem cell23_3395264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_3395264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395264 prefixEnd_3395264 := by exact prefixLift 3395264
  have htrace : WordTrace (prefixWord ++ tailWord_3395264) baseStart_3395264 baseEnd_3395264 := by
    simpa [prefixWord, tailWord_3395264, baseEnd_3395264] using wordTrace_append hprefix tailTrace_3395264
  have hstable : (prefixWord ++ tailWord_3395264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395264).length < 2 ^ (prefixWord ++ tailWord_3395264).sum := by decide
  have hdescent : baseEnd_3395264 < baseStart_3395264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395361 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3395361 : Nat := 118140960795 + 3395361 * 2 ^ 59
def prefixEnd_3395361 : Nat := 4983230072969 + 3 ^ 40 * 3395361 * 2
def baseEnd_3395361 : Nat := 1743452188530595368172525

theorem tailTrace_3395361 : CollatzResearch.WordTrace tailWord_3395361 prefixEnd_3395361 1743452188530595368172525 := by
  unfold tailWord_3395361
  simp only [CollatzResearch.WordTrace]
  refine ⟨123838989452194453337185937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82559326301462968891457291 123838989452194453337185937)
  ·
    refine ⟨92879242089145840002889453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123838989452194453337185937 92879242089145840002889453)
    ·
      refine ⟨34829715783429690001083545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92879242089145840002889453 34829715783429690001083545)
      ·
        refine ⟨26122286837572267500812659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34829715783429690001083545 26122286837572267500812659)
        ·
          refine ⟨39183430256358401251218989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26122286837572267500812659 39183430256358401251218989)
          ·
            refine ⟨14693786346134400469207121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39183430256358401251218989 14693786346134400469207121)
            ·
              refine ⟨11020339759600800351905341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14693786346134400469207121 11020339759600800351905341)
              ·
                refine ⟨4132627409850300131964503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11020339759600800351905341 4132627409850300131964503)
                ·
                  refine ⟨6198941114775450197946755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132627409850300131964503 6198941114775450197946755)
                  ·
                    refine ⟨9298411672163175296920133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6198941114775450197946755 9298411672163175296920133)
                    ·
                      refine ⟨1743452188530595368172525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9298411672163175296920133 1743452188530595368172525)
                      ·
                        rfl

theorem cell23_3395361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3395361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395361 prefixEnd_3395361 := by exact prefixLift 3395361
  have htrace : WordTrace (prefixWord ++ tailWord_3395361) baseStart_3395361 baseEnd_3395361 := by
    simpa [prefixWord, tailWord_3395361, baseEnd_3395361] using wordTrace_append hprefix tailTrace_3395361
  have hstable : (prefixWord ++ tailWord_3395361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395361).length < 2 ^ (prefixWord ++ tailWord_3395361).sum := by decide
  have hdescent : baseEnd_3395361 < baseStart_3395361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395384 : List Nat := [2, 1, 2, 1, 3, 4, 2, 8]
def baseStart_3395384 : Nat := 118140960795 + 3395384 * 2 ^ 59
def prefixEnd_3395384 : Nat := 4983230072969 + 3 ^ 40 * 3395384 * 2
def baseEnd_3395384 : Nat := 64572740688357362154997

theorem tailTrace_3395384 : CollatzResearch.WordTrace tailWord_3395384 prefixEnd_3395384 64572740688357362154997 := by
  unfold tailWord_3395384
  simp only [CollatzResearch.WordTrace]
  refine ⟨61919914165555564132636603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82559885554074085510182137 61919914165555564132636603)
  ·
    refine ⟨92879871248333346198954905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61919914165555564132636603 92879871248333346198954905)
    ·
      refine ⟨69659903436250009649216179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92879871248333346198954905 69659903436250009649216179)
      ·
        refine ⟨104489855154375014473824269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69659903436250009649216179 104489855154375014473824269)
        ·
          refine ⟨39183695682890630427684101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104489855154375014473824269 39183695682890630427684101)
          ·
            refine ⟨7346942940541993205190769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39183695682890630427684101 7346942940541993205190769)
            ·
              refine ⟨5510207205406494903893077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346942940541993205190769 5510207205406494903893077)
              ·
                refine ⟨64572740688357362154997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5510207205406494903893077 64572740688357362154997)
                ·
                  rfl

theorem cell23_3395384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 8].length) (baseStart_3395384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395384 prefixEnd_3395384 := by exact prefixLift 3395384
  have htrace : WordTrace (prefixWord ++ tailWord_3395384) baseStart_3395384 baseEnd_3395384 := by
    simpa [prefixWord, tailWord_3395384, baseEnd_3395384] using wordTrace_append hprefix tailTrace_3395384
  have hstable : (prefixWord ++ tailWord_3395384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395384).length < 2 ^ (prefixWord ++ tailWord_3395384).sum := by decide
  have hdescent : baseEnd_3395384 < baseStart_3395384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395388 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_3395388 : Nat := 118140960795 + 3395388 * 2 ^ 59
def prefixEnd_3395388 : Nat := 4983230072969 + 3 ^ 40 * 3395388 * 2
def baseEnd_3395388 : Nat := 581155350836088920844967

theorem tailTrace_3395388 : CollatzResearch.WordTrace tailWord_3395388 prefixEnd_3395388 581155350836088920844967 := by
  unfold tailWord_3395388
  simp only [CollatzResearch.WordTrace]
  refine ⟨61919987111548318474209409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82559982815397757965612545 61919987111548318474209409)
  ·
    refine ⟨46439990333661238855657057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61919987111548318474209409 46439990333661238855657057)
    ·
      refine ⟨34829992750245929141742793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46439990333661238855657057 34829992750245929141742793)
      ·
        refine ⟨26122494562684446856307095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34829992750245929141742793 26122494562684446856307095)
        ·
          refine ⟨39183741844026670284460643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26122494562684446856307095 39183741844026670284460643)
          ·
            refine ⟨58775612766040005426690965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39183741844026670284460643 58775612766040005426690965)
            ·
              refine ⟨2755106848408125254376139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58775612766040005426690965 2755106848408125254376139)
              ·
                refine ⟨4132660272612187881564209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755106848408125254376139 4132660272612187881564209)
                ·
                  refine ⟨3099495204459140911173157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132660272612187881564209 3099495204459140911173157)
                  ·
                    refine ⟨581155350836088920844967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099495204459140911173157 581155350836088920844967)
                    ·
                      rfl

theorem cell23_3395388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_3395388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395388 prefixEnd_3395388 := by exact prefixLift 3395388
  have htrace : WordTrace (prefixWord ++ tailWord_3395388) baseStart_3395388 baseEnd_3395388 := by
    simpa [prefixWord, tailWord_3395388, baseEnd_3395388] using wordTrace_append hprefix tailTrace_3395388
  have hstable : (prefixWord ++ tailWord_3395388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395388).length < 2 ^ (prefixWord ++ tailWord_3395388).sum := by decide
  have hdescent : baseEnd_3395388 < baseStart_3395388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395415 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_3395415 : Nat := 118140960795 + 3395415 * 2 ^ 59
def prefixEnd_3395415 : Nat := 4983230072969 + 3 ^ 40 * 3395415 * 2
def baseEnd_3395415 : Nat := 1743479916485938156897277

theorem tailTrace_3395415 : CollatzResearch.WordTrace tailWord_3395415 prefixEnd_3395415 1743479916485938156897277 := by
  unfold tailWord_3395415
  simp only [CollatzResearch.WordTrace]
  refine ⟨123840958993998820559651699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82560639329332547039767799 123840958993998820559651699)
  ·
    refine ⟨185761438490998230839477549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123840958993998820559651699 185761438490998230839477549)
    ·
      refine ⟨69660539434124336564804081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185761438490998230839477549 69660539434124336564804081)
      ·
        refine ⟨52245404575593252423603061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69660539434124336564804081 52245404575593252423603061)
        ·
          refine ⟨4898006678961867414712787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52245404575593252423603061 4898006678961867414712787)
          ·
            refine ⟨7347010018442801122069181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898006678961867414712787 7347010018442801122069181)
            ·
              refine ⟨2755128756916050420775943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7347010018442801122069181 2755128756916050420775943)
              ·
                refine ⟨4132693135374075631163915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755128756916050420775943 4132693135374075631163915)
                ·
                  refine ⟨6199039703061113446745873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132693135374075631163915 6199039703061113446745873)
                  ·
                    refine ⟨4649279777295835085059405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6199039703061113446745873 4649279777295835085059405)
                    ·
                      refine ⟨1743479916485938156897277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4649279777295835085059405 1743479916485938156897277)
                      ·
                        rfl

theorem cell23_3395415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_3395415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395415 prefixEnd_3395415 := by exact prefixLift 3395415
  have htrace : WordTrace (prefixWord ++ tailWord_3395415) baseStart_3395415 baseEnd_3395415 := by
    simpa [prefixWord, tailWord_3395415, baseEnd_3395415] using wordTrace_append hprefix tailTrace_3395415
  have hstable : (prefixWord ++ tailWord_3395415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395415).length < 2 ^ (prefixWord ++ tailWord_3395415).sum := by decide
  have hdescent : baseEnd_3395415 < baseStart_3395415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395468 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_3395468 : Nat := 118140960795 + 3395468 * 2 ^ 59
def prefixEnd_3395468 : Nat := 4983230072969 + 3 ^ 40 * 3395468 * 2
def baseEnd_3395468 : Nat := 1743507130960626449534533

theorem tailTrace_3395468 : CollatzResearch.WordTrace tailWord_3395468 prefixEnd_3395468 1743507130960626449534533 := by
  unfold tailWord_3395468
  simp only [CollatzResearch.WordTrace]
  refine ⟨61921446031403405305665529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82561928041871207074220705 61921446031403405305665529)
  ·
    refine ⟨46441084523552553979249147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61921446031403405305665529 46441084523552553979249147)
    ·
      refine ⟨69661626785328830968873721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46441084523552553979249147 69661626785328830968873721)
      ·
        refine ⟨52246220088996623226655291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69661626785328830968873721 52246220088996623226655291)
        ·
          refine ⟨78369330133494934839982937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52246220088996623226655291 78369330133494934839982937)
          ·
            refine ⟨58776997600121201129987203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78369330133494934839982937 58776997600121201129987203)
            ·
              refine ⟨88165496400181801694980805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58776997600121201129987203 88165496400181801694980805)
              ·
                refine ⟨16531030575034087817808901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88165496400181801694980805 16531030575034087817808901)
                ·
                  refine ⟨3099568232818891465839169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16531030575034087817808901 3099568232818891465839169)
                  ·
                    refine ⟨2324676174614168599379377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3099568232818891465839169 2324676174614168599379377)
                    ·
                      refine ⟨1743507130960626449534533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324676174614168599379377 1743507130960626449534533)
                      ·
                        rfl

theorem cell23_3395468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_3395468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395468 prefixEnd_3395468 := by exact prefixLift 3395468
  have htrace : WordTrace (prefixWord ++ tailWord_3395468) baseStart_3395468 baseEnd_3395468 := by
    simpa [prefixWord, tailWord_3395468, baseEnd_3395468] using wordTrace_append hprefix tailTrace_3395468
  have hstable : (prefixWord ++ tailWord_3395468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395468).length < 2 ^ (prefixWord ++ tailWord_3395468).sum := by decide
  have hdescent : baseEnd_3395468 < baseStart_3395468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395485 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_3395485 : Nat := 118140960795 + 3395485 * 2 ^ 59
def prefixEnd_3395485 : Nat := 4983230072969 + 3 ^ 40 * 3395485 * 2
def baseEnd_3395485 : Nat := 1743515860131752883021955

theorem tailTrace_3395485 : CollatzResearch.WordTrace tailWord_3395485 prefixEnd_3395485 1743515860131752883021955 := by
  unfold tailWord_3395485
  simp only [CollatzResearch.WordTrace]
  refine ⟨123843512103745222514699909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82562341402496815009799939 123843512103745222514699909)
  ·
    refine ⟨23220658519452229221506233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123843512103745222514699909 23220658519452229221506233)
    ·
      refine ⟨17415493889589171916129675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23220658519452229221506233 17415493889589171916129675)
      ·
        refine ⟨26123240834383757874194513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17415493889589171916129675 26123240834383757874194513)
        ·
          refine ⟨19592430625787818405645885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26123240834383757874194513 19592430625787818405645885)
          ·
            refine ⟨7347161484670431902117207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19592430625787818405645885 7347161484670431902117207)
            ·
              refine ⟨11020742227005647853175811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347161484670431902117207 11020742227005647853175811)
              ·
                refine ⟨16531113340508471779763717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11020742227005647853175811 16531113340508471779763717)
                ·
                  refine ⟨3099583751345338458705697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16531113340508471779763717 3099583751345338458705697)
                  ·
                    refine ⟨2324687813509003844029273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3099583751345338458705697 2324687813509003844029273)
                    ·
                      refine ⟨1743515860131752883021955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324687813509003844029273 1743515860131752883021955)
                      ·
                        rfl

theorem cell23_3395485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_3395485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395485 prefixEnd_3395485 := by exact prefixLift 3395485
  have htrace : WordTrace (prefixWord ++ tailWord_3395485) baseStart_3395485 baseEnd_3395485 := by
    simpa [prefixWord, tailWord_3395485, baseEnd_3395485] using wordTrace_append hprefix tailTrace_3395485
  have hstable : (prefixWord ++ tailWord_3395485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395485).length < 2 ^ (prefixWord ++ tailWord_3395485).sum := by decide
  have hdescent : baseEnd_3395485 < baseStart_3395485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395514 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3395514 : Nat := 118140960795 + 3395514 * 2 ^ 59
def prefixEnd_3395514 : Nat := 4983230072969 + 3 ^ 40 * 3395514 * 2
def baseEnd_3395514 : Nat := 1743530751070733269559321

theorem tailTrace_3395514 : CollatzResearch.WordTrace tailWord_3395514 prefixEnd_3395514 1743530751070733269559321 := by
  unfold tailWord_3395514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30961142455160040116876399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82563046547093440311670397 30961142455160040116876399)
  ·
    refine ⟨46441713682740060175314599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30961142455160040116876399 46441713682740060175314599)
    ·
      refine ⟨69662570524110090262971899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46441713682740060175314599 69662570524110090262971899)
      ·
        refine ⟨104493855786165135394457849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69662570524110090262971899 104493855786165135394457849)
        ·
          refine ⟨78370391839623851545843387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104493855786165135394457849 78370391839623851545843387)
          ·
            refine ⟨117555587759435777318765081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78370391839623851545843387 117555587759435777318765081)
            ·
              refine ⟨88166690819576832989073811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117555587759435777318765081 88166690819576832989073811)
              ·
                refine ⟨132250036229365249483610717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88166690819576832989073811 132250036229365249483610717)
                ·
                  refine ⟨49593763586011968556354019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132250036229365249483610717 49593763586011968556354019)
                  ·
                    refine ⟨74390645379017952834531029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49593763586011968556354019 74390645379017952834531029)
                    ·
                      refine ⟨1743530751070733269559321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74390645379017952834531029 1743530751070733269559321)
                      ·
                        rfl

theorem cell23_3395514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3395514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395514 prefixEnd_3395514 := by exact prefixLift 3395514
  have htrace : WordTrace (prefixWord ++ tailWord_3395514) baseStart_3395514 baseEnd_3395514 := by
    simpa [prefixWord, tailWord_3395514, baseEnd_3395514] using wordTrace_append hprefix tailTrace_3395514
  have hstable : (prefixWord ++ tailWord_3395514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395514).length < 2 ^ (prefixWord ++ tailWord_3395514).sum := by decide
  have hdescent : baseEnd_3395514 < baseStart_3395514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395542 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3395542 : Nat := 118140960795 + 3395542 * 2 ^ 59
def prefixEnd_3395542 : Nat := 4983230072969 + 3 ^ 40 * 3395542 * 2
def baseEnd_3395542 : Nat := 193727236503228795556577

theorem tailTrace_3395542 : CollatzResearch.WordTrace tailWord_3395542 prefixEnd_3395542 193727236503228795556577 := by
  unfold tailWord_3395542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740349441533670078095305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82563727376359147499683253 7740349441533670078095305)
  ·
    refine ⟨5805262081150252558571479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7740349441533670078095305 5805262081150252558571479)
    ·
      refine ⟨8707893121725378837857219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805262081150252558571479 8707893121725378837857219)
      ·
        refine ⟨13061839682588068256785829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707893121725378837857219 13061839682588068256785829)
        ·
          refine ⟨2449094940485262798147343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13061839682588068256785829 2449094940485262798147343)
          ·
            refine ⟨3673642410727894197221015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449094940485262798147343 3673642410727894197221015)
            ·
              refine ⟨5510463616091841295831523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673642410727894197221015 5510463616091841295831523)
              ·
                refine ⟨8265695424137761943747285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510463616091841295831523 8265695424137761943747285)
                ·
                  refine ⟨193727236503228795556577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8265695424137761943747285 193727236503228795556577)
                  ·
                    rfl

theorem cell23_3395542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3395542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395542 prefixEnd_3395542 := by exact prefixLift 3395542
  have htrace : WordTrace (prefixWord ++ tailWord_3395542) baseStart_3395542 baseEnd_3395542 := by
    simpa [prefixWord, tailWord_3395542, baseEnd_3395542] using wordTrace_append hprefix tailTrace_3395542
  have hstable : (prefixWord ++ tailWord_3395542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395542).length < 2 ^ (prefixWord ++ tailWord_3395542).sum := by decide
  have hdescent : baseEnd_3395542 < baseStart_3395542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395585 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3395585 : Nat := 118140960795 + 3395585 * 2 ^ 59
def prefixEnd_3395585 : Nat := 4983230072969 + 3 ^ 40 * 3395585 * 2
def baseEnd_3395585 : Nat := 581189069399067497257165

theorem tailTrace_3395585 : CollatzResearch.WordTrace tailWord_3395585 prefixEnd_3395585 581189069399067497257165 := by
  unfold tailWord_3395585
  simp only [CollatzResearch.WordTrace]
  refine ⟨123847159403382939593340209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82564772935588626395560139 123847159403382939593340209)
  ·
    refine ⟨92885369552537204695005157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123847159403382939593340209 92885369552537204695005157)
    ·
      refine ⟨17416006791100725880313467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92885369552537204695005157 17416006791100725880313467)
      ·
        refine ⟨26124010186651088820470201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17416006791100725880313467 26124010186651088820470201)
        ·
          refine ⟨19593007639988316615352651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26124010186651088820470201 19593007639988316615352651)
          ·
            refine ⟨29389511459982474923028977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19593007639988316615352651 29389511459982474923028977)
            ·
              refine ⟨22042133594986856192271733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29389511459982474923028977 22042133594986856192271733)
              ·
                refine ⟨2066450024530017768025475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22042133594986856192271733 2066450024530017768025475)
                ·
                  refine ⟨3099675036795026652038213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066450024530017768025475 3099675036795026652038213)
                  ·
                    refine ⟨581189069399067497257165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099675036795026652038213 581189069399067497257165)
                    ·
                      rfl

theorem cell23_3395585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3395585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395585 prefixEnd_3395585 := by exact prefixLift 3395585
  have htrace : WordTrace (prefixWord ++ tailWord_3395585) baseStart_3395585 baseEnd_3395585 := by
    simpa [prefixWord, tailWord_3395585, baseEnd_3395585] using wordTrace_append hprefix tailTrace_3395585
  have hstable : (prefixWord ++ tailWord_3395585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395585).length < 2 ^ (prefixWord ++ tailWord_3395585).sum := by decide
  have hdescent : baseEnd_3395585 < baseStart_3395585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395598 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_3395598 : Nat := 118140960795 + 3395598 * 2 ^ 59
def prefixEnd_3395598 : Nat := 4983230072969 + 3 ^ 40 * 3395598 * 2
def baseEnd_3395598 : Nat := 193730431493967882323215

theorem tailTrace_3395598 : CollatzResearch.WordTrace tailWord_3395598 prefixEnd_3395598 193730431493967882323215 := by
  unfold tailWord_3395598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480954194041980351695431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82565089034890561875708965 15480954194041980351695431)
  ·
    refine ⟨23221431291062970527543147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15480954194041980351695431 23221431291062970527543147)
    ·
      refine ⟨34832146936594455791314721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23221431291062970527543147 34832146936594455791314721)
      ·
        refine ⟨26124110202445841843486041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34832146936594455791314721 26124110202445841843486041)
        ·
          refine ⟨19593082651834381382614531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26124110202445841843486041 19593082651834381382614531)
          ·
            refine ⟨29389623977751572073921797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19593082651834381382614531 29389623977751572073921797)
            ·
              refine ⟨5510554495828419763860337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29389623977751572073921797 5510554495828419763860337)
              ·
                refine ⟨4132915871871314822895253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510554495828419763860337 4132915871871314822895253)
                ·
                  refine ⟨193730431493967882323215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4132915871871314822895253 193730431493967882323215)
                  ·
                    rfl

theorem cell23_3395598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_3395598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395598 prefixEnd_3395598 := by exact prefixLift 3395598
  have htrace : WordTrace (prefixWord ++ tailWord_3395598) baseStart_3395598 baseEnd_3395598 := by
    simpa [prefixWord, tailWord_3395598, baseEnd_3395598] using wordTrace_append hprefix tailTrace_3395598
  have hstable : (prefixWord ++ tailWord_3395598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395598).length < 2 ^ (prefixWord ++ tailWord_3395598).sum := by decide
  have hdescent : baseEnd_3395598 < baseStart_3395598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395635 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 2, 3, 2]
def baseStart_3395635 : Nat := 118140960795 + 3395635 * 2 ^ 59
def prefixEnd_3395635 : Nat := 4983230072969 + 3 ^ 40 * 3395635 * 2
def baseEnd_3395635 : Nat := 1743592882229927296146265

theorem tailTrace_3395635 : CollatzResearch.WordTrace tailWord_3395635 prefixEnd_3395635 1743592882229927296146265 := by
  unfold tailWord_3395635
  simp only [CollatzResearch.WordTrace]
  refine ⟨123848983053201798132660359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82565988702134532088440239 123848983053201798132660359)
  ·
    refine ⟨185773474579802697198990539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123848983053201798132660359 185773474579802697198990539)
    ·
      refine ⟨278660211869704045798485809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185773474579802697198990539 278660211869704045798485809)
      ·
        refine ⟨208995158902278034348864357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278660211869704045798485809 208995158902278034348864357)
        ·
          refine ⟨39186592294177131440412067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208995158902278034348864357 39186592294177131440412067)
          ·
            refine ⟨58779888441265697160618101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39186592294177131440412067 58779888441265697160618101)
            ·
              refine ⟨5510614541368659108807947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58779888441265697160618101 5510614541368659108807947)
              ·
                refine ⟨8265921812052988663211921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510614541368659108807947 8265921812052988663211921)
                ·
                  refine ⟨6199441359039741497408941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8265921812052988663211921 6199441359039741497408941)
                  ·
                    refine ⟨2324790509639903061528353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6199441359039741497408941 2324790509639903061528353)
                    ·
                      refine ⟨1743592882229927296146265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324790509639903061528353 1743592882229927296146265)
                      ·
                        rfl

theorem cell23_3395635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3, 2].length) (baseStart_3395635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395635 prefixEnd_3395635 := by exact prefixLift 3395635
  have htrace : WordTrace (prefixWord ++ tailWord_3395635) baseStart_3395635 baseEnd_3395635 := by
    simpa [prefixWord, tailWord_3395635, baseEnd_3395635] using wordTrace_append hprefix tailTrace_3395635
  have hstable : (prefixWord ++ tailWord_3395635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395635).length < 2 ^ (prefixWord ++ tailWord_3395635).sum := by decide
  have hdescent : baseEnd_3395635 < baseStart_3395635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395685 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3395685 : Nat := 118140960795 + 3395685 * 2 ^ 59
def prefixEnd_3395685 : Nat := 4983230072969 + 3 ^ 40 * 3395685 * 2
def baseEnd_3395685 : Nat := 1743618556262652100521035

theorem tailTrace_3395685 : CollatzResearch.WordTrace tailWord_3395685 prefixEnd_3395685 1743618556262652100521035 := by
  unfold tailWord_3395685
  simp only [CollatzResearch.WordTrace]
  refine ⟨123850806703020656671980509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82567204468680437781320339 123850806703020656671980509)
  ·
    refine ⟨46444052513632746251992691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123850806703020656671980509 46444052513632746251992691)
    ·
      refine ⟨69666078770449119377989037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46444052513632746251992691 69666078770449119377989037)
      ·
        refine ⟨26124779538918419766745889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69666078770449119377989037 26124779538918419766745889)
        ·
          refine ⟨19593584654188814825059417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26124779538918419766745889 19593584654188814825059417)
          ·
            refine ⟨14695188490641611118794563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19593584654188814825059417 14695188490641611118794563)
            ·
              refine ⟨22042782735962416678191845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14695188490641611118794563 22042782735962416678191845)
              ·
                refine ⟨4133021762992953127160971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22042782735962416678191845 4133021762992953127160971)
                ·
                  refine ⟨6199532644489429690741457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133021762992953127160971 6199532644489429690741457)
                  ·
                    refine ⟨4649649483367072268056093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6199532644489429690741457 4649649483367072268056093)
                    ·
                      refine ⟨1743618556262652100521035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4649649483367072268056093 1743618556262652100521035)
                      ·
                        rfl

theorem cell23_3395685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3395685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395685 prefixEnd_3395685 := by exact prefixLift 3395685
  have htrace : WordTrace (prefixWord ++ tailWord_3395685) baseStart_3395685 baseEnd_3395685 := by
    simpa [prefixWord, tailWord_3395685, baseEnd_3395685] using wordTrace_append hprefix tailTrace_3395685
  have hstable : (prefixWord ++ tailWord_3395685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395685).length < 2 ^ (prefixWord ++ tailWord_3395685).sum := by decide
  have hdescent : baseEnd_3395685 < baseStart_3395685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395702 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3395702 : Nat := 118140960795 + 3395702 * 2 ^ 59
def prefixEnd_3395702 : Nat := 4983230072969 + 3 ^ 40 * 3395702 * 2
def baseEnd_3395702 : Nat := 1743627285433778534008457

theorem tailTrace_3395702 : CollatzResearch.WordTrace tailWord_3395702 prefixEnd_3395702 1743627285433778534008457 := by
  unfold tailWord_3395702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740714171497441785959335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82567617829306045716899573 7740714171497441785959335)
  ·
    refine ⟨11611071257246162678939003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7740714171497441785959335 11611071257246162678939003)
    ·
      refine ⟨17416606885869244018408505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11611071257246162678939003 17416606885869244018408505)
      ·
        refine ⟨13062455164401933013806379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17416606885869244018408505 13062455164401933013806379)
        ·
          refine ⟨19593682746602899520709569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13062455164401933013806379 19593682746602899520709569)
          ·
            refine ⟨14695262059952174640532177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19593682746602899520709569 14695262059952174640532177)
            ·
              refine ⟨11021446544964130980399133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14695262059952174640532177 11021446544964130980399133)
              ·
                refine ⟨4133042454361549117649675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11021446544964130980399133 4133042454361549117649675)
                ·
                  refine ⟨6199563681542323676474513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133042454361549117649675 6199563681542323676474513)
                  ·
                    refine ⟨4649672761156742757355885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6199563681542323676474513 4649672761156742757355885)
                    ·
                      refine ⟨1743627285433778534008457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4649672761156742757355885 1743627285433778534008457)
                      ·
                        rfl

theorem cell23_3395702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3395702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395702 prefixEnd_3395702 := by exact prefixLift 3395702
  have htrace : WordTrace (prefixWord ++ tailWord_3395702) baseStart_3395702 baseEnd_3395702 := by
    simpa [prefixWord, tailWord_3395702, baseEnd_3395702] using wordTrace_append hprefix tailTrace_3395702
  have hstable : (prefixWord ++ tailWord_3395702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395702).length < 2 ^ (prefixWord ++ tailWord_3395702).sum := by decide
  have hdescent : baseEnd_3395702 < baseStart_3395702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395715 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 3]
def baseStart_3395715 : Nat := 118140960795 + 3395715 * 2 ^ 59
def prefixEnd_3395715 : Nat := 4983230072969 + 3 ^ 40 * 3395715 * 2
def baseEnd_3395715 : Nat := 1743633960682286983145897

theorem tailTrace_3395715 : CollatzResearch.WordTrace tailWord_3395715 prefixEnd_3395715 1743633960682286983145897 := by
  unfold tailWord_3395715
  simp only [CollatzResearch.WordTrace]
  refine ⟨123851900892911971795572599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82567933928607981197048399 123851900892911971795572599)
  ·
    refine ⟨185777851339367957693358899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123851900892911971795572599 185777851339367957693358899)
    ·
      refine ⟨278666777009051936540038349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185777851339367957693358899 278666777009051936540038349)
      ·
        refine ⟨104500041378394476202514381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278666777009051936540038349 104500041378394476202514381)
        ·
          refine ⟨39187515516897928575942893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104500041378394476202514381 39187515516897928575942893)
          ·
            refine ⟨14695318318836723215978585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39187515516897928575942893 14695318318836723215978585)
            ·
              refine ⟨11021488739127542411983939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14695318318836723215978585 11021488739127542411983939)
              ·
                refine ⟨16532233108691313617975909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11021488739127542411983939 16532233108691313617975909)
                ·
                  refine ⟨3099793707879621303370483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16532233108691313617975909 3099793707879621303370483)
                  ·
                    refine ⟨4649690561819431955055725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099793707879621303370483 4649690561819431955055725)
                    ·
                      refine ⟨1743633960682286983145897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4649690561819431955055725 1743633960682286983145897)
                      ·
                        rfl

theorem cell23_3395715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_3395715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395715 prefixEnd_3395715 := by exact prefixLift 3395715
  have htrace : WordTrace (prefixWord ++ tailWord_3395715) baseStart_3395715 baseEnd_3395715 := by
    simpa [prefixWord, tailWord_3395715, baseEnd_3395715] using wordTrace_append hprefix tailTrace_3395715
  have hstable : (prefixWord ++ tailWord_3395715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395715).length < 2 ^ (prefixWord ++ tailWord_3395715).sum := by decide
  have hdescent : baseEnd_3395715 < baseStart_3395715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395716 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_3395716 : Nat := 118140960795 + 3395716 * 2 ^ 59
def prefixEnd_3395716 : Nat := 4983230072969 + 3 ^ 40 * 3395716 * 2
def baseEnd_3395716 : Nat := 1743634474162941479233393

theorem tailTrace_3395716 : CollatzResearch.WordTrace tailWord_3395716 prefixEnd_3395716 1743634474162941479233393 := by
  unfold tailWord_3395716
  simp only [CollatzResearch.WordTrace]
  refine ⟨61925968682954174483179501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82567958243938899310906001 61925968682954174483179501)
  ·
    refine ⟨23222238256107815431192313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61925968682954174483179501 23222238256107815431192313)
    ·
      refine ⟨17416678692080861573394235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23222238256107815431192313 17416678692080861573394235)
      ·
        refine ⟨26125018038121292360091353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17416678692080861573394235 26125018038121292360091353)
        ·
          refine ⟨19593763528590969270068515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26125018038121292360091353 19593763528590969270068515)
          ·
            refine ⟨29390645292886453905102773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19593763528590969270068515 29390645292886453905102773)
            ·
              refine ⟨2755372996208105053603385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29390645292886453905102773 2755372996208105053603385)
              ·
                refine ⟨2066529747156078790202539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2755372996208105053603385 2066529747156078790202539)
                ·
                  refine ⟨3099794620734118185303809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066529747156078790202539 3099794620734118185303809)
                  ·
                    refine ⟨2324845965550588638977857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3099794620734118185303809 2324845965550588638977857)
                    ·
                      refine ⟨1743634474162941479233393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324845965550588638977857 1743634474162941479233393)
                      ·
                        rfl

theorem cell23_3395716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_3395716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395716 prefixEnd_3395716 := by exact prefixLift 3395716
  have htrace : WordTrace (prefixWord ++ tailWord_3395716) baseStart_3395716 baseEnd_3395716 := by
    simpa [prefixWord, tailWord_3395716, baseEnd_3395716] using wordTrace_append hprefix tailTrace_3395716
  have hstable : (prefixWord ++ tailWord_3395716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395716).length < 2 ^ (prefixWord ++ tailWord_3395716).sum := by decide
  have hdescent : baseEnd_3395716 < baseStart_3395716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395726 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_3395726 : Nat := 118140960795 + 3395726 * 2 ^ 59
def prefixEnd_3395726 : Nat := 4983230072969 + 3 ^ 40 * 3395726 * 2
def baseEnd_3395726 : Nat := 581213202989828813369449

theorem tailTrace_3395726 : CollatzResearch.WordTrace tailWord_3395726 prefixEnd_3395726 581213202989828813369449 := by
  unfold tailWord_3395726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15481537761984015084277879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82568201397248080449482021 15481537761984015084277879)
  ·
    refine ⟨23222306642976022626416819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15481537761984015084277879 23222306642976022626416819)
    ·
      refine ⟨34833459964464033939625229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23222306642976022626416819 34833459964464033939625229)
      ·
        refine ⟨13062547486674012727359461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34833459964464033939625229 13062547486674012727359461)
        ·
          refine ⟨2449227653751377386379899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13062547486674012727359461 2449227653751377386379899)
          ·
            refine ⟨3673841480627066079569849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449227653751377386379899 3673841480627066079569849)
            ·
              refine ⟨2755381110470299559677387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3673841480627066079569849 2755381110470299559677387)
              ·
                refine ⟨4133071665705449339516081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755381110470299559677387 4133071665705449339516081)
                ·
                  refine ⟨3099803749279087004637061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133071665705449339516081 3099803749279087004637061)
                  ·
                    refine ⟨581213202989828813369449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099803749279087004637061 581213202989828813369449)
                    ·
                      rfl

theorem cell23_3395726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_3395726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395726 prefixEnd_3395726 := by exact prefixLift 3395726
  have htrace : WordTrace (prefixWord ++ tailWord_3395726) baseStart_3395726 baseEnd_3395726 := by
    simpa [prefixWord, tailWord_3395726, baseEnd_3395726] using wordTrace_append hprefix tailTrace_3395726
  have hstable : (prefixWord ++ tailWord_3395726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395726).length < 2 ^ (prefixWord ++ tailWord_3395726).sum := by decide
  have hdescent : baseEnd_3395726 < baseStart_3395726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395731 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 8]
def baseStart_3395731 : Nat := 118140960795 + 3395731 * 2 ^ 59
def prefixEnd_3395731 : Nat := 4983230072969 + 3 ^ 40 * 3395731 * 2
def baseEnd_3395731 : Nat := 581214058790919640181941

theorem tailTrace_3395731 : CollatzResearch.WordTrace tailWord_3395731 prefixEnd_3395731 581214058790919640181941 := by
  unfold tailWord_3395731
  simp only [CollatzResearch.WordTrace]
  refine ⟨123852484460854006528155047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82568322973902671018770031 123852484460854006528155047)
  ·
    refine ⟨185778726691281009792232571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123852484460854006528155047 185778726691281009792232571)
    ·
      refine ⟨278668090036921514688348857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185778726691281009792232571 278668090036921514688348857)
      ·
        refine ⟨209001067527691136016261643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278668090036921514688348857 209001067527691136016261643)
        ·
          refine ⟨313501601291536704024392465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209001067527691136016261643 313501601291536704024392465)
          ·
            refine ⟨235126200968652528018294349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313501601291536704024392465 235126200968652528018294349)
            ·
              refine ⟨88172325363244698006860381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235126200968652528018294349 88172325363244698006860381)
              ·
                refine ⟨33064622011216761752572643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88172325363244698006860381 33064622011216761752572643)
                ·
                  refine ⟨49596933016825142628858965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33064622011216761752572643 49596933016825142628858965)
                  ·
                    refine ⟨581214058790919640181941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49596933016825142628858965 581214058790919640181941)
                    ·
                      rfl

theorem cell23_3395731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_3395731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395731 prefixEnd_3395731 := by exact prefixLift 3395731
  have htrace : WordTrace (prefixWord ++ tailWord_3395731) baseStart_3395731 baseEnd_3395731 := by
    simpa [prefixWord, tailWord_3395731, baseEnd_3395731] using wordTrace_append hprefix tailTrace_3395731
  have hstable : (prefixWord ++ tailWord_3395731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395731).length < 2 ^ (prefixWord ++ tailWord_3395731).sum := by decide
  have hdescent : baseEnd_3395731 < baseStart_3395731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395768 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_3395768 : Nat := 118140960795 + 3395768 * 2 ^ 59
def prefixEnd_3395768 : Nat := 4983230072969 + 3 ^ 40 * 3395768 * 2
def baseEnd_3395768 : Nat := 1743661175156975275783153

theorem tailTrace_3395768 : CollatzResearch.WordTrace tailWord_3395768 prefixEnd_3395768 1743661175156975275783153 := by
  unfold tailWord_3395768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61926916980859980923625979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82569222641146641231501305 61926916980859980923625979)
  ·
    refine ⟨92890375471289971385438969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61926916980859980923625979 92890375471289971385438969)
    ·
      refine ⟨69667781603467478539079227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92890375471289971385438969 69667781603467478539079227)
      ·
        refine ⟨104501672405201217808618841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69667781603467478539079227 104501672405201217808618841)
        ·
          refine ⟨78376254303900913356464131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104501672405201217808618841 78376254303900913356464131)
          ·
            refine ⟨117564381455851370034696197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78376254303900913356464131 117564381455851370034696197)
            ·
              refine ⟨22043321522972131881505537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117564381455851370034696197 22043321522972131881505537)
              ·
                refine ⟨16532491142229098911129153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22043321522972131881505537 16532491142229098911129153)
                ·
                  refine ⟨12399368356671824183346865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16532491142229098911129153 12399368356671824183346865)
                  ·
                    refine ⟨9299526267503868137510149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12399368356671824183346865 9299526267503868137510149)
                    ·
                      refine ⟨1743661175156975275783153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9299526267503868137510149 1743661175156975275783153)
                      ·
                        rfl

theorem cell23_3395768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_3395768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395768 prefixEnd_3395768 := by exact prefixLift 3395768
  have htrace : WordTrace (prefixWord ++ tailWord_3395768) baseStart_3395768 baseEnd_3395768 := by
    simpa [prefixWord, tailWord_3395768, baseEnd_3395768] using wordTrace_append hprefix tailTrace_3395768
  have hstable : (prefixWord ++ tailWord_3395768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395768).length < 2 ^ (prefixWord ++ tailWord_3395768).sum := by decide
  have hdescent : baseEnd_3395768 < baseStart_3395768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395808 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_3395808 : Nat := 118140960795 + 3395808 * 2 ^ 59
def prefixEnd_3395808 : Nat := 4983230072969 + 3 ^ 40 * 3395808 * 2
def baseEnd_3395808 : Nat := 581227238127718373094323

theorem tailTrace_3395808 : CollatzResearch.WordTrace tailWord_3395808 prefixEnd_3395808 581227238127718373094323 := by
  unfold tailWord_3395808
  simp only [CollatzResearch.WordTrace]
  refine ⟨61927646440787524339354039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82570195254383365785805385 61927646440787524339354039)
  ·
    refine ⟨92891469661181286509031059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61927646440787524339354039 92891469661181286509031059)
    ·
      refine ⟨139337204491771929763546589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92891469661181286509031059 139337204491771929763546589)
      ·
        refine ⟨52251451684414473661329971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139337204491771929763546589 52251451684414473661329971)
        ·
          refine ⟨78377177526621710491994957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52251451684414473661329971 78377177526621710491994957)
          ·
            refine ⟨29391441572483141434498109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78377177526621710491994957 29391441572483141434498109)
            ·
              refine ⟨11021790589681178037936791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29391441572483141434498109 11021790589681178037936791)
              ·
                refine ⟨16532685884521767056905187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11021790589681178037936791 16532685884521767056905187)
                ·
                  refine ⟨24799028826782650585357781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16532685884521767056905187 24799028826782650585357781)
                  ·
                    refine ⟨581227238127718373094323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24799028826782650585357781 581227238127718373094323)
                    ·
                      rfl

theorem cell23_3395808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_3395808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395808 prefixEnd_3395808 := by exact prefixLift 3395808
  have htrace : WordTrace (prefixWord ++ tailWord_3395808) baseStart_3395808 baseEnd_3395808 := by
    simpa [prefixWord, tailWord_3395808, baseEnd_3395808] using wordTrace_append hprefix tailTrace_3395808
  have hstable : (prefixWord ++ tailWord_3395808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395808).length < 2 ^ (prefixWord ++ tailWord_3395808).sum := by decide
  have hdescent : baseEnd_3395808 < baseStart_3395808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395845 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_3395845 : Nat := 118140960795 + 3395845 * 2 ^ 59
def prefixEnd_3395845 : Nat := 4983230072969 + 3 ^ 40 * 3395845 * 2
def baseEnd_3395845 : Nat := 1743700713167371474520299

theorem tailTrace_3395845 : CollatzResearch.WordTrace tailWord_3395845 prefixEnd_3395845 1743700713167371474520299 := by
  unfold tailWord_3395845
  simp only [CollatzResearch.WordTrace]
  refine ⟨123856642382441003997804989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82571094921627335998536659 123856642382441003997804989)
  ·
    refine ⟨46446240893415376499176871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123856642382441003997804989 46446240893415376499176871)
    ·
      refine ⟨69669361340123064748765307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46446240893415376499176871 69669361340123064748765307)
      ·
        refine ⟨104504042010184597123147961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69669361340123064748765307 104504042010184597123147961)
        ·
          refine ⟨78378031507638447842360971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104504042010184597123147961 78378031507638447842360971)
          ·
            refine ⟨117567047261457671763541457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78378031507638447842360971 117567047261457671763541457)
            ·
              refine ⟨88175285446093253822656093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117567047261457671763541457 88175285446093253822656093)
              ·
                refine ⟨33065732042284970183496035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88175285446093253822656093 33065732042284970183496035)
                ·
                  refine ⟨49598598063427455275244053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33065732042284970183496035 49598598063427455275244053)
                  ·
                    refine ⟨2324934284223161966027065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49598598063427455275244053 2324934284223161966027065)
                    ·
                      refine ⟨1743700713167371474520299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324934284223161966027065 1743700713167371474520299)
                      ·
                        rfl

theorem cell23_3395845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_3395845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395845 prefixEnd_3395845 := by exact prefixLift 3395845
  have htrace : WordTrace (prefixWord ++ tailWord_3395845) baseStart_3395845 baseEnd_3395845 := by
    simpa [prefixWord, tailWord_3395845, baseEnd_3395845] using wordTrace_append hprefix tailTrace_3395845
  have hstable : (prefixWord ++ tailWord_3395845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395845).length < 2 ^ (prefixWord ++ tailWord_3395845).sum := by decide
  have hdescent : baseEnd_3395845 < baseStart_3395845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395888 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_3395888 : Nat := 118140960795 + 3395888 * 2 ^ 59
def prefixEnd_3395888 : Nat := 4983230072969 + 3 ^ 40 * 3395888 * 2
def baseEnd_3395888 : Nat := 1743722792835514806282601

theorem tailTrace_3395888 : CollatzResearch.WordTrace tailWord_3395888 prefixEnd_3395888 1743722792835514806282601 := by
  unfold tailWord_3395888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929105360642611170810159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82572140480856814894413545 61929105360642611170810159)
  ·
    refine ⟨92893658040963916756215239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61929105360642611170810159 92893658040963916756215239)
    ·
      refine ⟨139340487061445875134322859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92893658040963916756215239 139340487061445875134322859)
      ·
        refine ⟨209010730592168812701484289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139340487061445875134322859 209010730592168812701484289)
        ·
          refine ⟨156758047944126609526113217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209010730592168812701484289 156758047944126609526113217)
          ·
            refine ⟨117568535958094957144584913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156758047944126609526113217 117568535958094957144584913)
            ·
              refine ⟨88176401968571217858438685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117568535958094957144584913 88176401968571217858438685)
              ·
                refine ⟨33066150738214206696914507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88176401968571217858438685 33066150738214206696914507)
                ·
                  refine ⟨49599226107321310045371761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33066150738214206696914507 49599226107321310045371761)
                  ·
                    refine ⟨37199419580490982534028821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49599226107321310045371761 37199419580490982534028821)
                    ·
                      refine ⟨1743722792835514806282601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37199419580490982534028821 1743722792835514806282601)
                      ·
                        rfl

theorem cell23_3395888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_3395888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395888 prefixEnd_3395888 := by exact prefixLift 3395888
  have htrace : WordTrace (prefixWord ++ tailWord_3395888) baseStart_3395888 baseEnd_3395888 := by
    simpa [prefixWord, tailWord_3395888, baseEnd_3395888] using wordTrace_append hprefix tailTrace_3395888
  have hstable : (prefixWord ++ tailWord_3395888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395888).length < 2 ^ (prefixWord ++ tailWord_3395888).sum := by decide
  have hdescent : baseEnd_3395888 < baseStart_3395888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395889 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_3395889 : Nat := 118140960795 + 3395889 * 2 ^ 59
def prefixEnd_3395889 : Nat := 4983230072969 + 3 ^ 40 * 3395889 * 2
def baseEnd_3395889 : Nat := 581241102105389767456699

theorem tailTrace_3395889 : CollatzResearch.WordTrace tailWord_3395889 prefixEnd_3395889 581241102105389767456699 := by
  unfold tailWord_3395889
  simp only [CollatzResearch.WordTrace]
  refine ⟨123858247194281599512406721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82572164796187733008271147 123858247194281599512406721)
  ·
    refine ⟨92893685395711199634305041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123858247194281599512406721 92893685395711199634305041)
    ·
      refine ⟨69670264046783399725728781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92893685395711199634305041 69670264046783399725728781)
      ·
        refine ⟨26126349017543774897148293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69670264046783399725728781 26126349017543774897148293)
        ·
          refine ⟨4898690440789457793215305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26126349017543774897148293 4898690440789457793215305)
          ·
            refine ⟨3674017830592093344911479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898690440789457793215305 3674017830592093344911479)
            ·
              refine ⟨5511026745888140017367219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674017830592093344911479 5511026745888140017367219)
              ·
                refine ⟨8266540118832210026050829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511026745888140017367219 8266540118832210026050829)
                ·
                  refine ⟨3099952544562078759769061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8266540118832210026050829 3099952544562078759769061)
                  ·
                    refine ⟨581241102105389767456699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099952544562078759769061 581241102105389767456699)
                    ·
                      rfl

theorem cell23_3395889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_3395889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395889 prefixEnd_3395889 := by exact prefixLift 3395889
  have htrace : WordTrace (prefixWord ++ tailWord_3395889) baseStart_3395889 baseEnd_3395889 := by
    simpa [prefixWord, tailWord_3395889, baseEnd_3395889] using wordTrace_append hprefix tailTrace_3395889
  have hstable : (prefixWord ++ tailWord_3395889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395889).length < 2 ^ (prefixWord ++ tailWord_3395889).sum := by decide
  have hdescent : baseEnd_3395889 < baseStart_3395889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395902 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3395902 : Nat := 118140960795 + 3395902 * 2 ^ 59
def prefixEnd_3395902 : Nat := 4983230072969 + 3 ^ 40 * 3395902 * 2
def baseEnd_3395902 : Nat := 193747775729408639056393

theorem tailTrace_3395902 : CollatzResearch.WordTrace tailWord_3395902 prefixEnd_3395902 193747775729408639056393 := by
  unfold tailWord_3395902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482340167904312841578745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82572480895489668488419973 15482340167904312841578745)
  ·
    refine ⟨11611755125928234631184059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15482340167904312841578745 11611755125928234631184059)
    ·
      refine ⟨17417632688892351946776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11611755125928234631184059 17417632688892351946776089)
      ·
        refine ⟨13063224516669263960082067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17417632688892351946776089 13063224516669263960082067)
        ·
          refine ⟨19594836775003895940123101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13063224516669263960082067 19594836775003895940123101)
          ·
            refine ⟨7348063790626460977546163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19594836775003895940123101 7348063790626460977546163)
            ·
              refine ⟨11022095685939691466319245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348063790626460977546163 11022095685939691466319245)
              ·
                refine ⟨4133285882227384299869717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11022095685939691466319245 4133285882227384299869717)
                ·
                  refine ⟨193747775729408639056393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4133285882227384299869717 193747775729408639056393)
                  ·
                    rfl

theorem cell23_3395902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3395902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395902 prefixEnd_3395902 := by exact prefixLift 3395902
  have htrace : WordTrace (prefixWord ++ tailWord_3395902) baseStart_3395902 baseEnd_3395902 := by
    simpa [prefixWord, tailWord_3395902, baseEnd_3395902] using wordTrace_append hprefix tailTrace_3395902
  have hstable : (prefixWord ++ tailWord_3395902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395902).length < 2 ^ (prefixWord ++ tailWord_3395902).sum := by decide
  have hdescent : baseEnd_3395902 < baseStart_3395902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395912 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_3395912 : Nat := 118140960795 + 3395912 * 2 ^ 59
def prefixEnd_3395912 : Nat := 4983230072969 + 3 ^ 40 * 3395912 * 2
def baseEnd_3395912 : Nat := 1743735116371222712382491

theorem tailTrace_3395912 : CollatzResearch.WordTrace tailWord_3395912 prefixEnd_3395912 1743735116371222712382491 := by
  unfold tailWord_3395912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929543036599137220246995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82572724048798849626995993 61929543036599137220246995)
  ·
    refine ⟨92894314554898705830370493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61929543036599137220246995 92894314554898705830370493)
    ·
      refine ⟨34835367958087014686388935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92894314554898705830370493 34835367958087014686388935)
      ·
        refine ⟨52253051937130522029583403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34835367958087014686388935 52253051937130522029583403)
        ·
          refine ⟨78379577905695783044375105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52253051937130522029583403 78379577905695783044375105)
          ·
            refine ⟨58784683429271837283281329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78379577905695783044375105 58784683429271837283281329)
            ·
              refine ⟨44088512571953877962460997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58784683429271837283281329 44088512571953877962460997)
              ·
                refine ⟨8266596107241352117961437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44088512571953877962460997 8266596107241352117961437)
                ·
                  refine ⟨3099973540215507044235539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8266596107241352117961437 3099973540215507044235539)
                  ·
                    refine ⟨4649960310323260566353309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099973540215507044235539 4649960310323260566353309)
                    ·
                      refine ⟨1743735116371222712382491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4649960310323260566353309 1743735116371222712382491)
                      ·
                        rfl

theorem cell23_3395912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_3395912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395912 prefixEnd_3395912 := by exact prefixLift 3395912
  have htrace : WordTrace (prefixWord ++ tailWord_3395912) baseStart_3395912 baseEnd_3395912 := by
    simpa [prefixWord, tailWord_3395912, baseEnd_3395912] using wordTrace_append hprefix tailTrace_3395912
  have hstable : (prefixWord ++ tailWord_3395912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395912).length < 2 ^ (prefixWord ++ tailWord_3395912).sum := by decide
  have hdescent : baseEnd_3395912 < baseStart_3395912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395915 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 1, 5]
def baseStart_3395915 : Nat := 118140960795 + 3395915 * 2 ^ 59
def prefixEnd_3395915 : Nat := 4983230072969 + 3 ^ 40 * 3395915 * 2
def baseEnd_3395915 : Nat := 581245552271062066881659

theorem tailTrace_3395915 : CollatzResearch.WordTrace tailWord_3395915 prefixEnd_3395915 581245552271062066881659 := by
  unfold tailWord_3395915
  simp only [CollatzResearch.WordTrace]
  refine ⟨123859195492187405952853199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82572796994791603968568799 123859195492187405952853199)
  ·
    refine ⟨185788793238281108929279799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123859195492187405952853199 185788793238281108929279799)
    ·
      refine ⟨278683189857421663393919699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185788793238281108929279799 278683189857421663393919699)
      ·
        refine ⟨418024784786132495090879549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278683189857421663393919699 418024784786132495090879549)
        ·
          refine ⟨156759294294799685659079831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418024784786132495090879549 156759294294799685659079831)
          ·
            refine ⟨235138941442199528488619747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156759294294799685659079831 235138941442199528488619747)
            ·
              refine ⟨352708412163299292732929621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235138941442199528488619747 352708412163299292732929621)
              ·
                refine ⟨4133301705038663586714019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 352708412163299292732929621 4133301705038663586714019)
                ·
                  refine ⟨6199952557557995380071029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133301705038663586714019 6199952557557995380071029)
                  ·
                    refine ⟨581245552271062066881659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6199952557557995380071029 581245552271062066881659)
                    ·
                      rfl

theorem cell23_3395915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 5].length) (baseStart_3395915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395915 prefixEnd_3395915 := by exact prefixLift 3395915
  have htrace : WordTrace (prefixWord ++ tailWord_3395915) baseStart_3395915 baseEnd_3395915 := by
    simpa [prefixWord, tailWord_3395915, baseEnd_3395915] using wordTrace_append hprefix tailTrace_3395915
  have hstable : (prefixWord ++ tailWord_3395915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395915).length < 2 ^ (prefixWord ++ tailWord_3395915).sum := by decide
  have hdescent : baseEnd_3395915 < baseStart_3395915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395922 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_3395922 : Nat := 118140960795 + 3395922 * 2 ^ 59
def prefixEnd_3395922 : Nat := 4983230072969 + 3 ^ 40 * 3395922 * 2
def baseEnd_3395922 : Nat := 1743740251177767673257445

theorem tailTrace_3395922 : CollatzResearch.WordTrace tailWord_3395922 prefixEnd_3395922 1743740251177767673257445 := by
  unfold tailWord_3395922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964862700790511537089505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82572967202108030765572013 30964862700790511537089505)
  ·
    refine ⟨23223647025592883652817129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30964862700790511537089505 23223647025592883652817129)
    ·
      refine ⟨17417735269194662739612847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23223647025592883652817129 17417735269194662739612847)
      ·
        refine ⟨26126602903791994109419271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417735269194662739612847 26126602903791994109419271)
        ·
          refine ⟨39189904355687991164128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126602903791994109419271 39189904355687991164128907)
          ·
            refine ⟨58784856533531986746193361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39189904355687991164128907 58784856533531986746193361)
            ·
              refine ⟨44088642400148990059645021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58784856533531986746193361 44088642400148990059645021)
              ·
                refine ⟨16533240900055871272366883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44088642400148990059645021 16533240900055871272366883)
                ·
                  refine ⟨24799861350083806908550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16533240900055871272366883 24799861350083806908550325)
                  ·
                    refine ⟨2324987001570356897676593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24799861350083806908550325 2324987001570356897676593)
                    ·
                      refine ⟨1743740251177767673257445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2324987001570356897676593 1743740251177767673257445)
                      ·
                        rfl

theorem cell23_3395922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_3395922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395922 prefixEnd_3395922 := by exact prefixLift 3395922
  have htrace : WordTrace (prefixWord ++ tailWord_3395922) baseStart_3395922 baseEnd_3395922 := by
    simpa [prefixWord, tailWord_3395922, baseEnd_3395922] using wordTrace_append hprefix tailTrace_3395922
  have hstable : (prefixWord ++ tailWord_3395922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395922).length < 2 ^ (prefixWord ++ tailWord_3395922).sum := by decide
  have hdescent : baseEnd_3395922 < baseStart_3395922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395929 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 1, 1, 3]
def baseStart_3395929 : Nat := 118140960795 + 3395929 * 2 ^ 59
def prefixEnd_3395929 : Nat := 4983230072969 + 3 ^ 40 * 3395929 * 2
def baseEnd_3395929 : Nat := 1743743845542349145869913

theorem tailTrace_3395929 : CollatzResearch.WordTrace tailWord_3395929 prefixEnd_3395929 1743743845542349145869913 := by
  unfold tailWord_3395929
  simp only [CollatzResearch.WordTrace]
  refine ⟨123859706114136686343862841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82573137409424457562575227 123859706114136686343862841)
  ·
    refine ⟨92894779585602514757897131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123859706114136686343862841 92894779585602514757897131)
    ·
      refine ⟨139342169378403772136845697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92894779585602514757897131 139342169378403772136845697)
      ·
        refine ⟨104506627033802829102634273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139342169378403772136845697 104506627033802829102634273)
        ·
          refine ⟨78379970275352121826975705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104506627033802829102634273 78379970275352121826975705)
          ·
            refine ⟨58784977706514091370231779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78379970275352121826975705 58784977706514091370231779)
            ·
              refine ⟨88177466559771137055347669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58784977706514091370231779 88177466559771137055347669)
              ·
                refine ⟨2066659372494636024734711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88177466559771137055347669 2066659372494636024734711)
                ·
                  refine ⟨3099989058741954037102067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066659372494636024734711 3099989058741954037102067)
                  ·
                    refine ⟨4649983588112931055653101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3099989058741954037102067 4649983588112931055653101)
                    ·
                      refine ⟨1743743845542349145869913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4649983588112931055653101 1743743845542349145869913)
                      ·
                        rfl

theorem cell23_3395929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_3395929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395929 prefixEnd_3395929 := by exact prefixLift 3395929
  have htrace : WordTrace (prefixWord ++ tailWord_3395929) baseStart_3395929 baseEnd_3395929 := by
    simpa [prefixWord, tailWord_3395929, baseEnd_3395929] using wordTrace_append hprefix tailTrace_3395929
  have hstable : (prefixWord ++ tailWord_3395929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395929).length < 2 ^ (prefixWord ++ tailWord_3395929).sum := by decide
  have hdescent : baseEnd_3395929 < baseStart_3395929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395972 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_3395972 : Nat := 118140960795 + 3395972 * 2 ^ 59
def prefixEnd_3395972 : Nat := 4983230072969 + 3 ^ 40 * 3395972 * 2
def baseEnd_3395972 : Nat := 1743765925210492477632215

theorem tailTrace_3395972 : CollatzResearch.WordTrace tailWord_3395972 prefixEnd_3395972 1743765925210492477632215 := by
  unfold tailWord_3395972
  simp only [CollatzResearch.WordTrace]
  refine ⟨61930637226490452343839085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82574182968653936458452113 61930637226490452343839085)
  ·
    refine ⟨23223988959933919628939657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61930637226490452343839085 23223988959933919628939657)
    ·
      refine ⟨17417991719950439721704743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23223988959933919628939657 17417991719950439721704743)
      ·
        refine ⟨26126987579925659582557115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417991719950439721704743 26126987579925659582557115)
        ·
          refine ⟨39190481369888489373835673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126987579925659582557115 39190481369888489373835673)
          ·
            refine ⟨29392861027416367030376755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39190481369888489373835673 29392861027416367030376755)
            ·
              refine ⟨44089291541124550545565133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29392861027416367030376755 44089291541124550545565133)
              ·
                refine ⟨16533484327921706454586925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44089291541124550545565133 16533484327921706454586925)
                ·
                  refine ⟨6200056622970639920470097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16533484327921706454586925 6200056622970639920470097)
                  ·
                    refine ⟨4650042467227979940352573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6200056622970639920470097 4650042467227979940352573)
                    ·
                      refine ⟨1743765925210492477632215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4650042467227979940352573 1743765925210492477632215)
                      ·
                        rfl

theorem cell23_3395972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_3395972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3395972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3395972 prefixEnd_3395972 := by exact prefixLift 3395972
  have htrace : WordTrace (prefixWord ++ tailWord_3395972) baseStart_3395972 baseEnd_3395972 := by
    simpa [prefixWord, tailWord_3395972, baseEnd_3395972] using wordTrace_append hprefix tailTrace_3395972
  have hstable : (prefixWord ++ tailWord_3395972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395972).length < 2 ^ (prefixWord ++ tailWord_3395972).sum := by decide
  have hdescent : baseEnd_3395972 < baseStart_3395972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396013 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3396013 : Nat := 118140960795 + 3396013 * 2 ^ 59
def prefixEnd_3396013 : Nat := 4983230072969 + 3 ^ 40 * 3396013 * 2
def baseEnd_3396013 : Nat := 581262325972442272406509

theorem tailTrace_3396013 : CollatzResearch.WordTrace tailWord_3396013 prefixEnd_3396013 581262325972442272406509 := by
  unfold tailWord_3396013
  simp only [CollatzResearch.WordTrace]
  refine ⟨123862769845832368689920693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82575179897221579126613795 123862769845832368689920693)
  ·
    refine ⟨11612134673046784564680065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123862769845832368689920693 11612134673046784564680065)
    ·
      refine ⟨8709101004785088423510049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11612134673046784564680065 8709101004785088423510049)
      ·
        refine ⟨6531825753588816317632537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8709101004785088423510049 6531825753588816317632537)
        ·
          refine ⟨4898869315191612238224403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6531825753588816317632537 4898869315191612238224403)
          ·
            refine ⟨7348303972787418357336605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898869315191612238224403 7348303972787418357336605)
            ·
              refine ⟨2755613989795281884001227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7348303972787418357336605 2755613989795281884001227)
              ·
                refine ⟨4133420984692922826001841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755613989795281884001227 4133420984692922826001841)
                ·
                  refine ⟨3100065738519692119501381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133420984692922826001841 3100065738519692119501381)
                  ·
                    refine ⟨581262325972442272406509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100065738519692119501381 581262325972442272406509)
                    ·
                      rfl

theorem cell23_3396013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3396013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396013 prefixEnd_3396013 := by exact prefixLift 3396013
  have htrace : WordTrace (prefixWord ++ tailWord_3396013) baseStart_3396013 baseEnd_3396013 := by
    simpa [prefixWord, tailWord_3396013, baseEnd_3396013] using wordTrace_append hprefix tailTrace_3396013
  have hstable : (prefixWord ++ tailWord_3396013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396013).length < 2 ^ (prefixWord ++ tailWord_3396013).sum := by decide
  have hdescent : baseEnd_3396013 < baseStart_3396013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396076 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_3396076 : Nat := 118140960795 + 3396076 * 2 ^ 59
def prefixEnd_3396076 : Nat := 4983230072969 + 3 ^ 40 * 3396076 * 2
def baseEnd_3396076 : Nat := 1743819327198560070731737

theorem tailTrace_3396076 : CollatzResearch.WordTrace tailWord_3396076 prefixEnd_3396076 1743819327198560070731737 := by
  unfold tailWord_3396076
  simp only [CollatzResearch.WordTrace]
  refine ⟨61932533822302065224732041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82576711763069420299642721 61932533822302065224732041)
  ·
    refine ⟨46449400366726548918549031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61932533822302065224732041 46449400366726548918549031)
    ·
      refine ⟨69674100550089823377823547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46449400366726548918549031 69674100550089823377823547)
      ·
        refine ⟨104511150825134735066735321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69674100550089823377823547 104511150825134735066735321)
        ·
          refine ⟨78383363118851051300051491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104511150825134735066735321 78383363118851051300051491)
          ·
            refine ⟨117575044678276576950077237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78383363118851051300051491 117575044678276576950077237)
            ·
              refine ⟨11022660438588429089069741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117575044678276576950077237 11022660438588429089069741)
              ·
                refine ⟨4133497664470660908401153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11022660438588429089069741 4133497664470660908401153)
                ·
                  refine ⟨3100123248352995681300865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133497664470660908401153 3100123248352995681300865)
                  ·
                    refine ⟨2325092436264746760975649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3100123248352995681300865 2325092436264746760975649)
                    ·
                      refine ⟨1743819327198560070731737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325092436264746760975649 1743819327198560070731737)
                      ·
                        rfl

theorem cell23_3396076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_3396076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396076 prefixEnd_3396076 := by exact prefixLift 3396076
  have htrace : WordTrace (prefixWord ++ tailWord_3396076) baseStart_3396076 baseEnd_3396076 := by
    simpa [prefixWord, tailWord_3396076, baseEnd_3396076] using wordTrace_append hprefix tailTrace_3396076
  have hstable : (prefixWord ++ tailWord_3396076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396076).length < 2 ^ (prefixWord ++ tailWord_3396076).sum := by decide
  have hdescent : baseEnd_3396076 < baseStart_3396076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396092 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_3396092 : Nat := 118140960795 + 3396092 * 2 ^ 59
def prefixEnd_3396092 : Nat := 4983230072969 + 3 ^ 40 * 3396092 * 2
def baseEnd_3396092 : Nat := 1743827542889032008131663

theorem tailTrace_3396092 : CollatzResearch.WordTrace tailWord_3396092 prefixEnd_3396092 1743827542889032008131663 := by
  unfold tailWord_3396092
  simp only [CollatzResearch.WordTrace]
  refine ⟨61932825606273082591023265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82577100808364110121364353 61932825606273082591023265)
  ·
    refine ⟨46449619204704811943267449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61932825606273082591023265 46449619204704811943267449)
    ·
      refine ⟨34837214403528608957450587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46449619204704811943267449 34837214403528608957450587)
      ·
        refine ⟨52255821605292913436175881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34837214403528608957450587 52255821605292913436175881)
        ·
          refine ⟨39191866203969685077131911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52255821605292913436175881 39191866203969685077131911)
          ·
            refine ⟨58787799305954527615697867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39191866203969685077131911 58787799305954527615697867)
            ·
              refine ⟨88181698958931791423546801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58787799305954527615697867 88181698958931791423546801)
              ·
                refine ⟨66136274219198843567660101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88181698958931791423546801 66136274219198843567660101)
                ·
                  refine ⟨12400551416099783168936269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66136274219198843567660101 12400551416099783168936269)
                  ·
                    refine ⟨4650206781037418688351101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12400551416099783168936269 4650206781037418688351101)
                    ·
                      refine ⟨1743827542889032008131663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4650206781037418688351101 1743827542889032008131663)
                      ·
                        rfl

theorem cell23_3396092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_3396092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396092 prefixEnd_3396092 := by exact prefixLift 3396092
  have htrace : WordTrace (prefixWord ++ tailWord_3396092) baseStart_3396092 baseEnd_3396092 := by
    simpa [prefixWord, tailWord_3396092, baseEnd_3396092] using wordTrace_append hprefix tailTrace_3396092
  have hstable : (prefixWord ++ tailWord_3396092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396092).length < 2 ^ (prefixWord ++ tailWord_3396092).sum := by decide
  have hdescent : baseEnd_3396092 < baseStart_3396092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396122 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3396122 : Nat := 118140960795 + 3396122 * 2 ^ 59
def prefixEnd_3396122 : Nat := 4983230072969 + 3 ^ 40 * 3396122 * 2
def baseEnd_3396122 : Nat := 1743842947308666890756525

theorem tailTrace_3396122 : CollatzResearch.WordTrace tailWord_3396122 prefixEnd_3396122 1743842947308666890756525 := by
  unfold tailWord_3396122
  simp only [CollatzResearch.WordTrace]
  refine ⟨30966686350609370076409655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82577830268291653537092413 30966686350609370076409655)
  ·
    refine ⟨46450029525914055114614483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30966686350609370076409655 46450029525914055114614483)
    ·
      refine ⟨69675044288871082671921725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46450029525914055114614483 69675044288871082671921725)
      ·
        refine ⟨26128141608326656001970647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69675044288871082671921725 26128141608326656001970647)
        ·
          refine ⟨39192212412489984002955971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26128141608326656001970647 39192212412489984002955971)
          ·
            refine ⟨58788318618734976004433957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39192212412489984002955971 58788318618734976004433957)
            ·
              refine ⟨11022809741012808000831367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58788318618734976004433957 11022809741012808000831367)
              ·
                refine ⟨16534214611519212001247051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11022809741012808000831367 16534214611519212001247051)
                ·
                  refine ⟨24801321917278818001870577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16534214611519212001247051 24801321917278818001870577)
                  ·
                    refine ⟨18600991437959113501402933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24801321917278818001870577 18600991437959113501402933)
                    ·
                      refine ⟨1743842947308666890756525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18600991437959113501402933 1743842947308666890756525)
                      ·
                        rfl

theorem cell23_3396122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3396122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396122 prefixEnd_3396122 := by exact prefixLift 3396122
  have htrace : WordTrace (prefixWord ++ tailWord_3396122) baseStart_3396122 baseEnd_3396122 := by
    simpa [prefixWord, tailWord_3396122, baseEnd_3396122] using wordTrace_append hprefix tailTrace_3396122
  have hstable : (prefixWord ++ tailWord_3396122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396122).length < 2 ^ (prefixWord ++ tailWord_3396122).sum := by decide
  have hdescent : baseEnd_3396122 < baseStart_3396122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396149 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_3396149 : Nat := 118140960795 + 3396149 * 2 ^ 59
def prefixEnd_3396149 : Nat := 4983230072969 + 3 ^ 40 * 3396149 * 2
def baseEnd_3396149 : Nat := 1743856811286338285118901

theorem tailTrace_3396149 : CollatzResearch.WordTrace tailWord_3396149 prefixEnd_3396149 1743856811286338285118901 := by
  unfold tailWord_3396149
  simp only [CollatzResearch.WordTrace]
  refine ⟨123867730173339663916871501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82578486782226442611247667 123867730173339663916871501)
  ·
    refine ⟨46450398815002373968826813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123867730173339663916871501 46450398815002373968826813)
    ·
      refine ⟨17418899555625890238310055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46450398815002373968826813 17418899555625890238310055)
      ·
        refine ⟨26128349333438835357465083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418899555625890238310055 26128349333438835357465083)
        ·
          refine ⟨39192524000158253036197625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26128349333438835357465083 39192524000158253036197625)
          ·
            refine ⟨29394393000118689777148219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39192524000158253036197625 29394393000118689777148219)
            ·
              refine ⟨44091589500178034665722329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29394393000118689777148219 44091589500178034665722329)
              ·
                refine ⟨33068692125133525999291747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44091589500178034665722329 33068692125133525999291747)
                ·
                  refine ⟨49603038187700288998937621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33068692125133525999291747 49603038187700288998937621)
                  ·
                    refine ⟨2325142415048451046825201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49603038187700288998937621 2325142415048451046825201)
                    ·
                      refine ⟨1743856811286338285118901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325142415048451046825201 1743856811286338285118901)
                      ·
                        rfl

theorem cell23_3396149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_3396149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396149 prefixEnd_3396149 := by exact prefixLift 3396149
  have htrace : WordTrace (prefixWord ++ tailWord_3396149) baseStart_3396149 baseEnd_3396149 := by
    simpa [prefixWord, tailWord_3396149, baseEnd_3396149] using wordTrace_append hprefix tailTrace_3396149
  have hstable : (prefixWord ++ tailWord_3396149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396149).length < 2 ^ (prefixWord ++ tailWord_3396149).sum := by decide
  have hdescent : baseEnd_3396149 < baseStart_3396149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396172 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 8]
def baseStart_3396172 : Nat := 118140960795 + 3396172 * 2 ^ 59
def prefixEnd_3396172 : Nat := 4983230072969 + 3 ^ 40 * 3396172 * 2
def baseEnd_3396172 : Nat := 193763180149043521681255

theorem tailTrace_3396172 : CollatzResearch.WordTrace tailWord_3396172 prefixEnd_3396172 193763180149043521681255 := by
  unfold tailWord_3396172
  simp only [CollatzResearch.WordTrace]
  refine ⟨61934284526128169422479385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82579046034837559229972513 61934284526128169422479385)
  ·
    refine ⟨46450713394596127066859539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61934284526128169422479385 46450713394596127066859539)
    ·
      refine ⟨69676070091894190600289309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46450713394596127066859539 69676070091894190600289309)
      ·
        refine ⟨26128526284460321475108491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69676070091894190600289309 26128526284460321475108491)
        ·
          refine ⟨39192789426690482212662737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26128526284460321475108491 39192789426690482212662737)
          ·
            refine ⟨29394592070017861659497053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39192789426690482212662737 29394592070017861659497053)
            ·
              refine ⟨11022972026256698122311395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29394592070017861659497053 11022972026256698122311395)
              ·
                refine ⟨16534458039385047183467093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11022972026256698122311395 16534458039385047183467093)
                ·
                  refine ⟨193763180149043521681255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16534458039385047183467093 193763180149043521681255)
                  ·
                    rfl

theorem cell23_3396172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_3396172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396172 prefixEnd_3396172 := by exact prefixLift 3396172
  have htrace : WordTrace (prefixWord ++ tailWord_3396172) baseStart_3396172 baseEnd_3396172 := by
    simpa [prefixWord, tailWord_3396172, baseEnd_3396172] using wordTrace_append hprefix tailTrace_3396172
  have hstable : (prefixWord ++ tailWord_3396172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396172).length < 2 ^ (prefixWord ++ tailWord_3396172).sum := by decide
  have hdescent : baseEnd_3396172 < baseStart_3396172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396210 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3396210 : Nat := 118140960795 + 3396210 * 2 ^ 59
def prefixEnd_3396210 : Nat := 4983230072969 + 3 ^ 40 * 3396210 * 2
def baseEnd_3396210 : Nat := 581296044535420848818707

theorem tailTrace_3396210 : CollatzResearch.WordTrace tailWord_3396210 prefixEnd_3396210 581296044535420848818707 := by
  unfold tailWord_3396210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967488756529667833710521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82579970017412447556561389 30967488756529667833710521)
  ·
    refine ⟨23225616567397250875282891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30967488756529667833710521 23225616567397250875282891)
    ·
      refine ⟨34838424851095876312924337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23225616567397250875282891 34838424851095876312924337)
      ·
        refine ⟨26128818638321907234693253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34838424851095876312924337 26128818638321907234693253)
        ·
          refine ⟨4899153494685357606504985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26128818638321907234693253 4899153494685357606504985)
          ·
            refine ⟨3674365121014018204878739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899153494685357606504985 3674365121014018204878739)
            ·
              refine ⟨5511547681521027307318109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674365121014018204878739 5511547681521027307318109)
              ·
                refine ⟨2066830380570385240244291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511547681521027307318109 2066830380570385240244291)
                ·
                  refine ⟨3100245570855577860366437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066830380570385240244291 3100245570855577860366437)
                  ·
                    refine ⟨581296044535420848818707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100245570855577860366437 581296044535420848818707)
                    ·
                      rfl

theorem cell23_3396210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3396210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396210 prefixEnd_3396210 := by exact prefixLift 3396210
  have htrace : WordTrace (prefixWord ++ tailWord_3396210) baseStart_3396210 baseEnd_3396210 := by
    simpa [prefixWord, tailWord_3396210, baseEnd_3396210] using wordTrace_append hprefix tailTrace_3396210
  have hstable : (prefixWord ++ tailWord_3396210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396210).length < 2 ^ (prefixWord ++ tailWord_3396210).sum := by decide
  have hdescent : baseEnd_3396210 < baseStart_3396210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396256 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3396256 : Nat := 118140960795 + 3396256 * 2 ^ 59
def prefixEnd_3396256 : Nat := 4983230072969 + 3 ^ 40 * 3396256 * 2
def baseEnd_3396256 : Nat := 1743911753716369366480909

theorem tailTrace_3396256 : CollatzResearch.WordTrace tailWord_3396256 prefixEnd_3396256 1743911753716369366480909 := by
  unfold tailWord_3396256
  simp only [CollatzResearch.WordTrace]
  refine ⟨61935816391976010595508311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82581088522634680794011081 61935816391976010595508311)
  ·
    refine ⟨92903724587964015893262467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61935816391976010595508311 92903724587964015893262467)
    ·
      refine ⟨139355586881946023839893701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92903724587964015893262467 139355586881946023839893701)
      ·
        refine ⟨26129172540364879469980069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139355586881946023839893701 26129172540364879469980069)
        ·
          refine ⟨4899219851318414900621263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26129172540364879469980069 4899219851318414900621263)
          ·
            refine ⟨7348829776977622350931895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899219851318414900621263 7348829776977622350931895)
            ·
              refine ⟨11023244665466433526397843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348829776977622350931895 11023244665466433526397843)
              ·
                refine ⟨16534866998199650289596765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11023244665466433526397843 16534866998199650289596765)
                ·
                  refine ⟨6200575124324868858598787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16534866998199650289596765 6200575124324868858598787)
                  ·
                    refine ⟨9300862686487303287898181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6200575124324868858598787 9300862686487303287898181)
                    ·
                      refine ⟨1743911753716369366480909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9300862686487303287898181 1743911753716369366480909)
                      ·
                        rfl

theorem cell23_3396256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3396256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396256 prefixEnd_3396256 := by exact prefixLift 3396256
  have htrace : WordTrace (prefixWord ++ tailWord_3396256) baseStart_3396256 baseEnd_3396256 := by
    simpa [prefixWord, tailWord_3396256, baseEnd_3396256] using wordTrace_append hprefix tailTrace_3396256
  have hstable : (prefixWord ++ tailWord_3396256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396256).length < 2 ^ (prefixWord ++ tailWord_3396256).sum := by decide
  have hdescent : baseEnd_3396256 < baseStart_3396256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396270 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3396270 : Nat := 118140960795 + 3396270 * 2 ^ 59
def prefixEnd_3396270 : Nat := 4983230072969 + 3 ^ 40 * 3396270 * 2
def baseEnd_3396270 : Nat := 581306314148510770568615

theorem tailTrace_3396270 : CollatzResearch.WordTrace tailWord_3396270 prefixEnd_3396270 581306314148510770568615 := by
  unfold tailWord_3396270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15484017925737662697753283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82581428937267534388017509 15484017925737662697753283)
  ·
    refine ⟨23226026888606494046629925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15484017925737662697753283 23226026888606494046629925)
    ·
      refine ⟨4354880041613717633743111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23226026888606494046629925 4354880041613717633743111)
      ·
        refine ⟨6532320062420576450614667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354880041613717633743111 6532320062420576450614667)
        ·
          refine ⟨9798480093630864675922001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532320062420576450614667 9798480093630864675922001)
          ·
            refine ⟨7348860070223148506941501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9798480093630864675922001 7348860070223148506941501)
            ·
              refine ⟨2755822526333680690103063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7348860070223148506941501 2755822526333680690103063)
              ·
                refine ⟨4133733789500521035154595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755822526333680690103063 4133733789500521035154595)
                ·
                  refine ⟨6200600684250781552731893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133733789500521035154595 6200600684250781552731893)
                  ·
                    refine ⟨581306314148510770568615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6200600684250781552731893 581306314148510770568615)
                    ·
                      rfl

theorem cell23_3396270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3396270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396270 prefixEnd_3396270 := by exact prefixLift 3396270
  have htrace : WordTrace (prefixWord ++ tailWord_3396270) baseStart_3396270 baseEnd_3396270 := by
    simpa [prefixWord, tailWord_3396270, baseEnd_3396270] using wordTrace_append hprefix tailTrace_3396270
  have hstable : (prefixWord ++ tailWord_3396270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396270).length < 2 ^ (prefixWord ++ tailWord_3396270).sum := by decide
  have hdescent : baseEnd_3396270 < baseStart_3396270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396279 : List Nat := [1, 1, 3, 1, 7, 10]
def baseStart_3396279 : Nat := 118140960795 + 3396279 * 2 ^ 59
def prefixEnd_3396279 : Nat := 4983230072969 + 3 ^ 40 * 3396279 * 2
def baseEnd_3396279 : Nat := 7176640180129311837421

theorem tailTrace_3396279 : CollatzResearch.WordTrace tailWord_3396279 prefixEnd_3396279 7176640180129311837421 := by
  unfold tailWord_3396279
  simp only [CollatzResearch.WordTrace]
  refine ⟨123872471662868696119103891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82581647775245797412735927 123872471662868696119103891)
  ·
    refine ⟨185808707494303044178655837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123872471662868696119103891 185808707494303044178655837)
    ·
      refine ⟨69678265310363641566995939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185808707494303044178655837 69678265310363641566995939)
      ·
        refine ⟨104517397965545462350493909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69678265310363641566995939 104517397965545462350493909)
        ·
          refine ⟨2449626514817471773839701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 104517397965545462350493909 2449626514817471773839701)
          ·
            refine ⟨7176640180129311837421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2449626514817471773839701 7176640180129311837421)
            ·
              rfl

theorem cell23_3396279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 10].length) (baseStart_3396279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396279 prefixEnd_3396279 := by exact prefixLift 3396279
  have htrace : WordTrace (prefixWord ++ tailWord_3396279) baseStart_3396279 baseEnd_3396279 := by
    simpa [prefixWord, tailWord_3396279, baseEnd_3396279] using wordTrace_append hprefix tailTrace_3396279
  have hstable : (prefixWord ++ tailWord_3396279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396279).length < 2 ^ (prefixWord ++ tailWord_3396279).sum := by decide
  have hdescent : baseEnd_3396279 < baseStart_3396279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396346 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_3396346 : Nat := 118140960795 + 3396346 * 2 ^ 59
def prefixEnd_3396346 : Nat := 4983230072969 + 3 ^ 40 * 3396346 * 2
def baseEnd_3396346 : Nat := 1743957966975274014355495

theorem tailTrace_3396346 : CollatzResearch.WordTrace tailWord_3396346 prefixEnd_3396346 1743957966975274014355495 := by
  unfold tailWord_3396346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30968728838406491640448223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82583276902417311041195261 30968728838406491640448223)
  ·
    refine ⟨46453093257609737460672335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30968728838406491640448223 46453093257609737460672335)
    ·
      refine ⟨69679639886414606191008503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46453093257609737460672335 69679639886414606191008503)
      ·
        refine ⟨104519459829621909286512755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69679639886414606191008503 104519459829621909286512755)
        ·
          refine ⟨156779189744432863929769133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104519459829621909286512755 156779189744432863929769133)
          ·
            refine ⟨58792196154162323973663425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156779189744432863929769133 58792196154162323973663425)
            ·
              refine ⟨44094147115621742980247569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58792196154162323973663425 44094147115621742980247569)
              ·
                refine ⟨33070610336716307235185677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44094147115621742980247569 33070610336716307235185677)
                ·
                  refine ⟨12401478876268615213194629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33070610336716307235185677 12401478876268615213194629)
                  ·
                    refine ⟨2325277289300365352473993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12401478876268615213194629 2325277289300365352473993)
                    ·
                      refine ⟨1743957966975274014355495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325277289300365352473993 1743957966975274014355495)
                      ·
                        rfl

theorem cell23_3396346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_3396346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396346 prefixEnd_3396346 := by exact prefixLift 3396346
  have htrace : WordTrace (prefixWord ++ tailWord_3396346) baseStart_3396346 baseEnd_3396346 := by
    simpa [prefixWord, tailWord_3396346, baseEnd_3396346] using wordTrace_append hprefix tailTrace_3396346
  have hstable : (prefixWord ++ tailWord_3396346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396346).length < 2 ^ (prefixWord ++ tailWord_3396346).sum := by decide
  have hdescent : baseEnd_3396346 < baseStart_3396346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396369 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 7]
def baseStart_3396369 : Nat := 118140960795 + 3396369 * 2 ^ 59
def prefixEnd_3396369 : Nat := 4983230072969 + 3 ^ 40 * 3396369 * 2
def baseEnd_3396369 : Nat := 193774419670036380485321

theorem tailTrace_3396369 : CollatzResearch.WordTrace tailWord_3396369 prefixEnd_3396369 193774419670036380485321 := by
  unfold tailWord_3396369
  simp only [CollatzResearch.WordTrace]
  refine ⟨123875754232542641489880161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82583836155028427659920107 123875754232542641489880161)
  ·
    refine ⟨92906815674406981117410121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123875754232542641489880161 92906815674406981117410121)
    ·
      refine ⟨69680111755805235838057591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92906815674406981117410121 69680111755805235838057591)
      ·
        refine ⟨104520167633707853757086387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69680111755805235838057591 104520167633707853757086387)
        ·
          refine ⟨156780251450561780635629581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104520167633707853757086387 156780251450561780635629581)
          ·
            refine ⟨58792594293960667738361093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156780251450561780635629581 58792594293960667738361093)
            ·
              refine ⟨11023611430117625200942705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58792594293960667738361093 11023611430117625200942705)
              ·
                refine ⟨8267708572588218900707029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11023611430117625200942705 8267708572588218900707029)
                ·
                  refine ⟨193774419670036380485321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8267708572588218900707029 193774419670036380485321)
                  ·
                    rfl

theorem cell23_3396369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_3396369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396369 prefixEnd_3396369 := by exact prefixLift 3396369
  have htrace : WordTrace (prefixWord ++ tailWord_3396369) baseStart_3396369 baseEnd_3396369 := by
    simpa [prefixWord, tailWord_3396369, baseEnd_3396369] using wordTrace_append hprefix tailTrace_3396369
  have hstable : (prefixWord ++ tailWord_3396369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396369).length < 2 ^ (prefixWord ++ tailWord_3396369).sum := by decide
  have hdescent : baseEnd_3396369 < baseStart_3396369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396433 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_3396433 : Nat := 118140960795 + 3396433 * 2 ^ 59
def prefixEnd_3396433 : Nat := 4983230072969 + 3 ^ 40 * 3396433 * 2
def baseEnd_3396433 : Nat := 581334213264071724655865

theorem tailTrace_3396433 : CollatzResearch.WordTrace tailWord_3396433 prefixEnd_3396433 581334213264071724655865 := by
  unfold tailWord_3396433
  simp only [CollatzResearch.WordTrace]
  refine ⟨123878088504310780420209953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82585392336207186946806635 123878088504310780420209953)
  ·
    refine ⟨92908566378233085315157465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123878088504310780420209953 92908566378233085315157465)
    ·
      refine ⟨69681424783674813986368099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92908566378233085315157465 69681424783674813986368099)
      ·
        refine ⟨104522137175512220979552149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69681424783674813986368099 104522137175512220979552149)
        ·
          refine ⟨4899475180102135358416507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104522137175512220979552149 4899475180102135358416507)
          ·
            refine ⟨7349212770153203037624761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899475180102135358416507 7349212770153203037624761)
            ·
              refine ⟨5511909577614902278218571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349212770153203037624761 5511909577614902278218571)
              ·
                refine ⟨8267864366422353417327857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511909577614902278218571 8267864366422353417327857)
                ·
                  refine ⟨6200898274816765062995893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8267864366422353417327857 6200898274816765062995893)
                  ·
                    refine ⟨581334213264071724655865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6200898274816765062995893 581334213264071724655865)
                    ·
                      rfl

theorem cell23_3396433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_3396433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396433 prefixEnd_3396433 := by exact prefixLift 3396433
  have htrace : WordTrace (prefixWord ++ tailWord_3396433) baseStart_3396433 baseEnd_3396433 := by
    simpa [prefixWord, tailWord_3396433, baseEnd_3396433] using wordTrace_append hprefix tailTrace_3396433
  have hstable : (prefixWord ++ tailWord_3396433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396433).length < 2 ^ (prefixWord ++ tailWord_3396433).sum := by decide
  have hdescent : baseEnd_3396433 < baseStart_3396433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396459 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 8]
def baseStart_3396459 : Nat := 118140960795 + 3396459 * 2 ^ 59
def prefixEnd_3396459 : Nat := 4983230072969 + 3 ^ 40 * 3396459 * 2
def baseEnd_3396459 : Nat := 193779554476581341360275

theorem tailTrace_3396459 : CollatzResearch.WordTrace tailWord_3396459 prefixEnd_3396459 193779554476581341360275 := by
  unfold tailWord_3396459
  simp only [CollatzResearch.WordTrace]
  refine ⟨123879036802216586860656431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82586024534811057907104287 123879036802216586860656431)
  ·
    refine ⟨185818555203324880290984647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123879036802216586860656431 185818555203324880290984647)
    ·
      refine ⟨278727832804987320436476971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185818555203324880290984647 278727832804987320436476971)
      ·
        refine ⟨418091749207480980654715457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278727832804987320436476971 418091749207480980654715457)
        ·
          refine ⟨313568811905610735491036593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418091749207480980654715457 313568811905610735491036593)
          ·
            refine ⟨235176608929208051618277445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313568811905610735491036593 235176608929208051618277445)
            ·
              refine ⟨44095614174226509678427021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235176608929208051618277445 44095614174226509678427021)
              ·
                refine ⟨16535855315334941129410133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44095614174226509678427021 16535855315334941129410133)
                ·
                  refine ⟨193779554476581341360275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16535855315334941129410133 193779554476581341360275)
                  ·
                    rfl

theorem cell23_3396459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 8].length) (baseStart_3396459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396459 prefixEnd_3396459 := by exact prefixLift 3396459
  have htrace : WordTrace (prefixWord ++ tailWord_3396459) baseStart_3396459 baseEnd_3396459 := by
    simpa [prefixWord, tailWord_3396459, baseEnd_3396459] using wordTrace_append hprefix tailTrace_3396459
  have hstable : (prefixWord ++ tailWord_3396459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396459).length < 2 ^ (prefixWord ++ tailWord_3396459).sum := by decide
  have hdescent : baseEnd_3396459 < baseStart_3396459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396470 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3396470 : Nat := 118140960795 + 3396470 * 2 ^ 59
def prefixEnd_3396470 : Nat := 4983230072969 + 3 ^ 40 * 3396470 * 2
def baseEnd_3396470 : Nat := 1744021638576431529204925

theorem tailTrace_3396470 : CollatzResearch.WordTrace tailWord_3396470 prefixEnd_3396470 1744021638576431529204925 := by
  unfold tailWord_3396470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742464875323545983706679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82586292003451157159537909 7742464875323545983706679)
  ·
    refine ⟨11613697312985318975560019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7742464875323545983706679 11613697312985318975560019)
    ·
      refine ⟨17420545969477978463340029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11613697312985318975560019 17420545969477978463340029)
      ·
        refine ⟨6532704738554241923752511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17420545969477978463340029 6532704738554241923752511)
        ·
          refine ⟨9799057107831362885628767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532704738554241923752511 9799057107831362885628767)
          ·
            refine ⟨14698585661747044328443151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799057107831362885628767 14698585661747044328443151)
            ·
              refine ⟨22047878492620566492664727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14698585661747044328443151 22047878492620566492664727)
              ·
                refine ⟨33071817738930849738997091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22047878492620566492664727 33071817738930849738997091)
                ·
                  refine ⟨49607726608396274608495637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33071817738930849738997091 49607726608396274608495637)
                  ·
                    refine ⟨2325362184768575372273233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49607726608396274608495637 2325362184768575372273233)
                    ·
                      refine ⟨1744021638576431529204925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325362184768575372273233 1744021638576431529204925)
                      ·
                        rfl

theorem cell23_3396470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3396470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396470 prefixEnd_3396470 := by exact prefixLift 3396470
  have htrace : WordTrace (prefixWord ++ tailWord_3396470) baseStart_3396470 baseEnd_3396470 := by
    simpa [prefixWord, tailWord_3396470, baseEnd_3396470] using wordTrace_append hprefix tailTrace_3396470
  have hstable : (prefixWord ++ tailWord_3396470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396470).length < 2 ^ (prefixWord ++ tailWord_3396470).sum := by decide
  have hdescent : baseEnd_3396470 < baseStart_3396470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396490 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3396490 : Nat := 118140960795 + 3396490 * 2 ^ 59
def prefixEnd_3396490 : Nat := 4983230072969 + 3 ^ 40 * 3396490 * 2
def baseEnd_3396490 : Nat := 1744031908189521450954833

theorem tailTrace_3396490 : CollatzResearch.WordTrace tailWord_3396490 prefixEnd_3396490 1744031908189521450954833 := by
  unfold tailWord_3396490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970041866276069788758731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82586778310069519436689949 30970041866276069788758731)
  ·
    refine ⟨46455062799414104683138097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30970041866276069788758731 46455062799414104683138097)
    ·
      refine ⟨34841297099560578512353573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46455062799414104683138097 34841297099560578512353573)
      ·
        refine ⟨6532743206167608471066295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34841297099560578512353573 6532743206167608471066295)
        ·
          refine ⟨9799114809251412706599443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532743206167608471066295 9799114809251412706599443)
          ·
            refine ⟨14698672213877119059899165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799114809251412706599443 14698672213877119059899165)
            ·
              refine ⟨5512002080203919647462187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14698672213877119059899165 5512002080203919647462187)
              ·
                refine ⟨8268003120305879471193281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512002080203919647462187 8268003120305879471193281)
                ·
                  refine ⟨6201002340229409603394961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8268003120305879471193281 6201002340229409603394961)
                  ·
                    refine ⟨4650751755172057202546221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6201002340229409603394961 4650751755172057202546221)
                    ·
                      refine ⟨1744031908189521450954833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4650751755172057202546221 1744031908189521450954833)
                      ·
                        rfl

theorem cell23_3396490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3396490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396490 prefixEnd_3396490 := by exact prefixLift 3396490
  have htrace : WordTrace (prefixWord ++ tailWord_3396490) baseStart_3396490 baseEnd_3396490 := by
    simpa [prefixWord, tailWord_3396490, baseEnd_3396490] using wordTrace_append hprefix tailTrace_3396490
  have hstable : (prefixWord ++ tailWord_3396490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396490).length < 2 ^ (prefixWord ++ tailWord_3396490).sum := by decide
  have hdescent : baseEnd_3396490 < baseStart_3396490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396503 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_3396503 : Nat := 118140960795 + 3396503 * 2 ^ 59
def prefixEnd_3396503 : Nat := 4983230072969 + 3 ^ 40 * 3396503 * 2
def baseEnd_3396503 : Nat := 1744038583438029900092273

theorem tailTrace_3396503 : CollatzResearch.WordTrace tailWord_3396503 prefixEnd_3396503 1744038583438029900092273 := by
  unfold tailWord_3396503
  simp only [CollatzResearch.WordTrace]
  refine ⟨123880641614057182375258163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82587094409371454916838775 123880641614057182375258163)
  ·
    refine ⟨185820962421085773562887245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123880641614057182375258163 185820962421085773562887245)
    ·
      refine ⟨69682860907907165086082717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185820962421085773562887245 69682860907907165086082717)
      ·
        refine ⟨26131072840465186907281019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69682860907907165086082717 26131072840465186907281019)
        ·
          refine ⟨39196609260697780360921529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26131072840465186907281019 39196609260697780360921529)
          ·
            refine ⟨29397456945523335270691147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39196609260697780360921529 29397456945523335270691147)
            ·
              refine ⟨44096185418285002906036721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29397456945523335270691147 44096185418285002906036721)
              ·
                refine ⟨33072139063713752179527541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44096185418285002906036721 33072139063713752179527541)
                ·
                  refine ⟨3100513037223164266830707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33072139063713752179527541 3100513037223164266830707)
                  ·
                    refine ⟨4650769555834746400246061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100513037223164266830707 4650769555834746400246061)
                    ·
                      refine ⟨1744038583438029900092273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4650769555834746400246061 1744038583438029900092273)
                      ·
                        rfl

theorem cell23_3396503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_3396503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396503 prefixEnd_3396503 := by exact prefixLift 3396503
  have htrace : WordTrace (prefixWord ++ tailWord_3396503) baseStart_3396503 baseEnd_3396503 := by
    simpa [prefixWord, tailWord_3396503, baseEnd_3396503] using wordTrace_append hprefix tailTrace_3396503
  have hstable : (prefixWord ++ tailWord_3396503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396503).length < 2 ^ (prefixWord ++ tailWord_3396503).sum := by decide
  have hdescent : baseEnd_3396503 < baseStart_3396503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396573 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3396573 : Nat := 118140960795 + 3396573 * 2 ^ 59
def prefixEnd_3396573 : Nat := 4983230072969 + 3 ^ 40 * 3396573 * 2
def baseEnd_3396573 : Nat := 1744074527083844626216951

theorem tailTrace_3396573 : CollatzResearch.WordTrace tailWord_3396573 prefixEnd_3396573 1744074527083844626216951 := by
  unfold tailWord_3396573
  simp only [CollatzResearch.WordTrace]
  refine ⟨123883194723803584330306373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82588796482535722886870915 123883194723803584330306373)
  ·
    refine ⟨23228099010713172061932445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123883194723803584330306373 23228099010713172061932445)
    ·
      refine ⟨8710537129017439523224667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23228099010713172061932445 8710537129017439523224667)
      ·
        refine ⟨13065805693526159284837001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8710537129017439523224667 13065805693526159284837001)
        ·
          refine ⟨9799354270144619463627751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13065805693526159284837001 9799354270144619463627751)
          ·
            refine ⟨14699031405216929195441627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799354270144619463627751 14699031405216929195441627)
            ·
              refine ⟨22048547107825393793162441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699031405216929195441627 22048547107825393793162441)
              ·
                refine ⟨16536410330869045344871831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22048547107825393793162441 16536410330869045344871831)
                ·
                  refine ⟨24804615496303568017307747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16536410330869045344871831 24804615496303568017307747)
                  ·
                    refine ⟨37206923244455352025961621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24804615496303568017307747 37206923244455352025961621)
                    ·
                      refine ⟨1744074527083844626216951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37206923244455352025961621 1744074527083844626216951)
                      ·
                        rfl

theorem cell23_3396573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3396573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396573 prefixEnd_3396573 := by exact prefixLift 3396573
  have htrace : WordTrace (prefixWord ++ tailWord_3396573) baseStart_3396573 baseEnd_3396573 := by
    simpa [prefixWord, tailWord_3396573, baseEnd_3396573] using wordTrace_append hprefix tailTrace_3396573
  have hstable : (prefixWord ++ tailWord_3396573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396573).length < 2 ^ (prefixWord ++ tailWord_3396573).sum := by decide
  have hdescent : baseEnd_3396573 < baseStart_3396573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396583 : List Nat := [1, 1, 5, 2, 2, 2, 2, 8]
def baseStart_3396583 : Nat := 118140960795 + 3396583 * 2 ^ 59
def prefixEnd_3396583 : Nat := 4983230072969 + 3 ^ 40 * 3396583 * 2
def baseEnd_3396583 : Nat := 64595543032977392114515

theorem tailTrace_3396583 : CollatzResearch.WordTrace tailWord_3396583 prefixEnd_3396583 64595543032977392114515 := by
  unfold tailWord_3396583
  simp only [CollatzResearch.WordTrace]
  refine ⟨123883559453767356038170403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82589039635844904025446935 123883559453767356038170403)
  ·
    refine ⟨185825339180651034057255605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123883559453767356038170403 185825339180651034057255605)
    ·
      refine ⟨17421125548186034442867713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185825339180651034057255605 17421125548186034442867713)
      ·
        refine ⟨13065844161139525832150785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17421125548186034442867713 13065844161139525832150785)
        ·
          refine ⟨9799383120854644374113089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13065844161139525832150785 9799383120854644374113089)
          ·
            refine ⟨7349537340640983280584817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9799383120854644374113089 7349537340640983280584817)
            ·
              refine ⟨5512153005480737460438613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349537340640983280584817 5512153005480737460438613)
              ·
                refine ⟨64595543032977392114515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5512153005480737460438613 64595543032977392114515)
                ·
                  rfl

theorem cell23_3396583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 8].length) (baseStart_3396583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396583 prefixEnd_3396583 := by exact prefixLift 3396583
  have htrace : WordTrace (prefixWord ++ tailWord_3396583) baseStart_3396583 baseEnd_3396583 := by
    simpa [prefixWord, tailWord_3396583, baseEnd_3396583] using wordTrace_append hprefix tailTrace_3396583
  have hstable : (prefixWord ++ tailWord_3396583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396583).length < 2 ^ (prefixWord ++ tailWord_3396583).sum := by decide
  have hdescent : baseEnd_3396583 < baseStart_3396583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396594 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3396594 : Nat := 118140960795 + 3396594 * 2 ^ 59
def prefixEnd_3396594 : Nat := 4983230072969 + 3 ^ 40 * 3396594 * 2
def baseEnd_3396594 : Nat := 1744085310177589044054355

theorem tailTrace_3396594 : CollatzResearch.WordTrace tailWord_3396594 prefixEnd_3396594 1744085310177589044054355 := by
  unfold tailWord_3396594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970990164181876229205209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82589307104485003277880557 30970990164181876229205209)
  ·
    refine ⟨23228242623136407171903907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30970990164181876229205209 23228242623136407171903907)
    ·
      refine ⟨34842363934704610757855861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23228242623136407171903907 34842363934704610757855861)
      ·
        refine ⟨3266471618878557258548987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34842363934704610757855861 3266471618878557258548987)
        ·
          refine ⟨4899707428317835887823481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266471618878557258548987 4899707428317835887823481)
          ·
            refine ⟨3674780571238376915867611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899707428317835887823481 3674780571238376915867611)
            ·
              refine ⟨5512170856857565373801417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674780571238376915867611 5512170856857565373801417)
              ·
                refine ⟨4134128142643174030351063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512170856857565373801417 4134128142643174030351063)
                ·
                  refine ⟨6201192213964761045526595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134128142643174030351063 6201192213964761045526595)
                  ·
                    refine ⟨9301788320947141568289893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201192213964761045526595 9301788320947141568289893)
                    ·
                      refine ⟨1744085310177589044054355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9301788320947141568289893 1744085310177589044054355)
                      ·
                        rfl

theorem cell23_3396594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3396594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396594 prefixEnd_3396594 := by exact prefixLift 3396594
  have htrace : WordTrace (prefixWord ++ tailWord_3396594) baseStart_3396594 baseEnd_3396594 := by
    simpa [prefixWord, tailWord_3396594, baseEnd_3396594] using wordTrace_append hprefix tailTrace_3396594
  have hstable : (prefixWord ++ tailWord_3396594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396594).length < 2 ^ (prefixWord ++ tailWord_3396594).sum := by decide
  have hdescent : baseEnd_3396594 < baseStart_3396594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396643 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 2, 6]
def baseStart_3396643 : Nat := 118140960795 + 3396643 * 2 ^ 59
def prefixEnd_3396643 : Nat := 4983230072969 + 3 ^ 40 * 3396643 * 2
def baseEnd_3396643 : Nat := 581370156909886450780543

theorem tailTrace_3396643 : CollatzResearch.WordTrace tailWord_3396643 prefixEnd_3396643 581370156909886450780543 := by
  unfold tailWord_3396643
  simp only [CollatzResearch.WordTrace]
  refine ⟨123885747833549986285354583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82590498555699990856903055 123885747833549986285354583)
  ·
    refine ⟨185828621750324979428031875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123885747833549986285354583 185828621750324979428031875)
    ·
      refine ⟨278742932625487469142047813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185828621750324979428031875 278742932625487469142047813)
      ·
        refine ⟨52264299867278900464133965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278742932625487469142047813 52264299867278900464133965)
        ·
          refine ⟨19599112450229587674050237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52264299867278900464133965 19599112450229587674050237)
          ·
            refine ⟨7349667168836095377768839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19599112450229587674050237 7349667168836095377768839)
            ·
              refine ⟨11024500753254143066653259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349667168836095377768839 11024500753254143066653259)
              ·
                refine ⟨16536751129881214599979889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11024500753254143066653259 16536751129881214599979889)
                ·
                  refine ⟨12402563347410910949984917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16536751129881214599979889 12402563347410910949984917)
                  ·
                    refine ⟨581370156909886450780543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12402563347410910949984917 581370156909886450780543)
                    ·
                      rfl

theorem cell23_3396643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 6].length) (baseStart_3396643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396643 prefixEnd_3396643 := by exact prefixLift 3396643
  have htrace : WordTrace (prefixWord ++ tailWord_3396643) baseStart_3396643 baseEnd_3396643 := by
    simpa [prefixWord, tailWord_3396643, baseEnd_3396643] using wordTrace_append hprefix tailTrace_3396643
  have hstable : (prefixWord ++ tailWord_3396643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396643).length < 2 ^ (prefixWord ++ tailWord_3396643).sum := by decide
  have hdescent : baseEnd_3396643 < baseStart_3396643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396690 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_3396690 : Nat := 118140960795 + 3396690 * 2 ^ 59
def prefixEnd_3396690 : Nat := 4983230072969 + 3 ^ 40 * 3396690 * 2
def baseEnd_3396690 : Nat := 193792733813380074272657

theorem tailTrace_3396690 : CollatzResearch.WordTrace tailWord_3396690 prefixEnd_3396690 193792733813380074272657 := by
  unfold tailWord_3396690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30971865516094928328078881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82591641376253142208210349 30971865516094928328078881)
  ·
    refine ⟨23228899137071196246059161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30971865516094928328078881 23228899137071196246059161)
    ·
      refine ⟨17421674352803397184544371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23228899137071196246059161 17421674352803397184544371)
      ·
        refine ⟨26132511529205095776816557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421674352803397184544371 26132511529205095776816557)
        ·
          refine ⟨9799691823451910916306209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26132511529205095776816557 9799691823451910916306209)
          ·
            refine ⟨7349768867588933187229657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9799691823451910916306209 7349768867588933187229657)
            ·
              refine ⟨5512326650691699890422243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349768867588933187229657 5512326650691699890422243)
              ·
                refine ⟨8268489976037549835633365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512326650691699890422243 8268489976037549835633365)
                ·
                  refine ⟨193792733813380074272657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8268489976037549835633365 193792733813380074272657)
                  ·
                    rfl

theorem cell23_3396690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_3396690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396690 prefixEnd_3396690 := by exact prefixLift 3396690
  have htrace : WordTrace (prefixWord ++ tailWord_3396690) baseStart_3396690 baseEnd_3396690 := by
    simpa [prefixWord, tailWord_3396690, baseEnd_3396690] using wordTrace_append hprefix tailTrace_3396690
  have hstable : (prefixWord ++ tailWord_3396690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396690).length < 2 ^ (prefixWord ++ tailWord_3396690).sum := by decide
  have hdescent : baseEnd_3396690 < baseStart_3396690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396700 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3396700 : Nat := 118140960795 + 3396700 * 2 ^ 59
def prefixEnd_3396700 : Nat := 4983230072969 + 3 ^ 40 * 3396700 * 2
def baseEnd_3396700 : Nat := 1744139739126965629328867

theorem tailTrace_3396700 : CollatzResearch.WordTrace tailWord_3396700 prefixEnd_3396700 1744139739126965629328867 := by
  unfold tailWord_3396700
  simp only [CollatzResearch.WordTrace]
  refine ⟨61943913397171742510089777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82591884529562323346786369 61943913397171742510089777)
  ·
    refine ⟨46457935047878806882567333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61943913397171742510089777 46457935047878806882567333)
    ·
      refine ⟨8710862821477276290481375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46457935047878806882567333 8710862821477276290481375)
      ·
        refine ⟨13066294232215914435722063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8710862821477276290481375 13066294232215914435722063)
        ·
          refine ⟨19599441348323871653583095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13066294232215914435722063 19599441348323871653583095)
          ·
            refine ⟨29399162022485807480374643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19599441348323871653583095 29399162022485807480374643)
            ·
              refine ⟨44098743033728711220561965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29399162022485807480374643 44098743033728711220561965)
              ·
                refine ⟨16537028637648266707710737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44098743033728711220561965 16537028637648266707710737)
                ·
                  refine ⟨12402771478236200030783053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16537028637648266707710737 12402771478236200030783053)
                  ·
                    refine ⟨4651039304338575011543645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12402771478236200030783053 4651039304338575011543645)
                    ·
                      refine ⟨1744139739126965629328867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651039304338575011543645 1744139739126965629328867)
                      ·
                        rfl

theorem cell23_3396700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3396700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396700 prefixEnd_3396700 := by exact prefixLift 3396700
  have htrace : WordTrace (prefixWord ++ tailWord_3396700) baseStart_3396700 baseEnd_3396700 := by
    simpa [prefixWord, tailWord_3396700, baseEnd_3396700] using wordTrace_append hprefix tailTrace_3396700
  have hstable : (prefixWord ++ tailWord_3396700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396700).length < 2 ^ (prefixWord ++ tailWord_3396700).sum := by decide
  have hdescent : baseEnd_3396700 < baseStart_3396700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396701 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3396701 : Nat := 118140960795 + 3396701 * 2 ^ 59
def prefixEnd_3396701 : Nat := 4983230072969 + 3 ^ 40 * 3396701 * 2
def baseEnd_3396701 : Nat := 1744140252607620125416363

theorem tailTrace_3396701 : CollatzResearch.WordTrace tailWord_3396701 prefixEnd_3396701 1744140252607620125416363 := by
  unfold tailWord_3396701
  simp only [CollatzResearch.WordTrace]
  refine ⟨123887863267339862190965957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82591908844893241460643971 123887863267339862190965957)
  ·
    refine ⟨23228974362626224160806117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123887863267339862190965957 23228974362626224160806117)
    ·
      refine ⟨4355432692992417030151147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23228974362626224160806117 4355432692992417030151147)
      ·
        refine ⟨6533149039488625545226721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355432692992417030151147 6533149039488625545226721)
        ·
          refine ⟨4899861779616469158920041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533149039488625545226721 4899861779616469158920041)
          ·
            refine ⟨3674896334712351869190031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899861779616469158920041 3674896334712351869190031)
            ·
              refine ⟨5512344502068527803785047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674896334712351869190031 5512344502068527803785047)
              ·
                refine ⟨8268516753102791705677571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512344502068527803785047 8268516753102791705677571)
                ·
                  refine ⟨12402775129654187558516357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8268516753102791705677571 12402775129654187558516357)
                  ·
                    refine ⟨2325520336810160167221817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12402775129654187558516357 2325520336810160167221817)
                    ·
                      refine ⟨1744140252607620125416363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325520336810160167221817 1744140252607620125416363)
                      ·
                        rfl

theorem cell23_3396701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3396701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396701 prefixEnd_3396701 := by exact prefixLift 3396701
  have htrace : WordTrace (prefixWord ++ tailWord_3396701) baseStart_3396701 baseEnd_3396701 := by
    simpa [prefixWord, tailWord_3396701, baseEnd_3396701] using wordTrace_append hprefix tailTrace_3396701
  have hstable : (prefixWord ++ tailWord_3396701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396701).length < 2 ^ (prefixWord ++ tailWord_3396701).sum := by decide
  have hdescent : baseEnd_3396701 < baseStart_3396701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396723 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4]
def baseStart_3396723 : Nat := 118140960795 + 3396723 * 2 ^ 59
def prefixEnd_3396723 : Nat := 4983230072969 + 3 ^ 40 * 3396723 * 2
def baseEnd_3396723 : Nat := 1744151549182019039341261

theorem tailTrace_3396723 : CollatzResearch.WordTrace tailWord_3396723 prefixEnd_3396723 1744151549182019039341261 := by
  unfold tailWord_3396723
  simp only [CollatzResearch.WordTrace]
  refine ⟨123888665673260159948266823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82592443782173439965511215 123888665673260159948266823)
  ·
    refine ⟨185832998509890239922400235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123888665673260159948266823 185832998509890239922400235)
    ·
      refine ⟨278749497764835359883600353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185832998509890239922400235 278749497764835359883600353)
      ·
        refine ⟨209062123323626519912700265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278749497764835359883600353 209062123323626519912700265)
        ·
          refine ⟨156796592492719889934525199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209062123323626519912700265 156796592492719889934525199)
          ·
            refine ⟨235194888739079834901787799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156796592492719889934525199 235194888739079834901787799)
            ·
              refine ⟨352792333108619752352681699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235194888739079834901787799 352792333108619752352681699)
              ·
                refine ⟨529188499662929628529022549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352792333108619752352681699 529188499662929628529022549)
                ·
                  refine ⟨6201427730424956584324483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 529188499662929628529022549 6201427730424956584324483)
                  ·
                    refine ⟨9302141595637434876486725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201427730424956584324483 9302141595637434876486725)
                    ·
                      refine ⟨1744151549182019039341261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9302141595637434876486725 1744151549182019039341261)
                      ·
                        rfl

theorem cell23_3396723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_3396723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396723 prefixEnd_3396723 := by exact prefixLift 3396723
  have htrace : WordTrace (prefixWord ++ tailWord_3396723) baseStart_3396723 baseEnd_3396723 := by
    simpa [prefixWord, tailWord_3396723, baseEnd_3396723] using wordTrace_append hprefix tailTrace_3396723
  have hstable : (prefixWord ++ tailWord_3396723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396723).length < 2 ^ (prefixWord ++ tailWord_3396723).sum := by decide
  have hdescent : baseEnd_3396723 < baseStart_3396723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396740 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3396740 : Nat := 118140960795 + 3396740 * 2 ^ 59
def prefixEnd_3396740 : Nat := 4983230072969 + 3 ^ 40 * 3396740 * 2
def baseEnd_3396740 : Nat := 1744160278353145472828683

theorem tailTrace_3396740 : CollatzResearch.WordTrace tailWord_3396740 prefixEnd_3396740 1744160278353145472828683 := by
  unfold tailWord_3396740
  simp only [CollatzResearch.WordTrace]
  refine ⟨61944642857099285925817837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82592857142799047901090449 61944642857099285925817837)
  ·
    refine ⟨23229241071412232222181689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61944642857099285925817837 23229241071412232222181689)
    ·
      refine ⟨17421930803559174166636267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23229241071412232222181689 17421930803559174166636267)
      ·
        refine ⟨26132896205338761249954401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421930803559174166636267 26132896205338761249954401)
        ·
          refine ⟨19599672154004070937465801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26132896205338761249954401 19599672154004070937465801)
          ·
            refine ⟨14699754115503053203099351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19599672154004070937465801 14699754115503053203099351)
            ·
              refine ⟨22049631173254579804649027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699754115503053203099351 22049631173254579804649027)
              ·
                refine ⟨33074446759881869706973541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22049631173254579804649027 33074446759881869706973541)
                ·
                  refine ⟨6201458767477850570057539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33074446759881869706973541 6201458767477850570057539)
                  ·
                    refine ⟨9302188151216775855086309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201458767477850570057539 9302188151216775855086309)
                    ·
                      refine ⟨1744160278353145472828683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9302188151216775855086309 1744160278353145472828683)
                      ·
                        rfl

theorem cell23_3396740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3396740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396740 prefixEnd_3396740 := by exact prefixLift 3396740
  have htrace : WordTrace (prefixWord ++ tailWord_3396740) baseStart_3396740 baseEnd_3396740 := by
    simpa [prefixWord, tailWord_3396740, baseEnd_3396740] using wordTrace_append hprefix tailTrace_3396740
  have hstable : (prefixWord ++ tailWord_3396740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396740).length < 2 ^ (prefixWord ++ tailWord_3396740).sum := by decide
  have hdescent : baseEnd_3396740 < baseStart_3396740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396801 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3396801 : Nat := 118140960795 + 3396801 * 2 ^ 59
def prefixEnd_3396801 : Nat := 4983230072969 + 3 ^ 40 * 3396801 * 2
def baseEnd_3396801 : Nat := 581397200224356578055301

theorem tailTrace_3396801 : CollatzResearch.WordTrace tailWord_3396801 prefixEnd_3396801 581397200224356578055301 := by
  unfold tailWord_3396801
  simp only [CollatzResearch.WordTrace]
  refine ⟨123891510566977579269606257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82594340377985052846404171 123891510566977579269606257)
  ·
    refine ⟨92918632925233184452204693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123891510566977579269606257 92918632925233184452204693)
    ·
      refine ⟨4355560918370305521197095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92918632925233184452204693 4355560918370305521197095)
      ·
        refine ⟨6533341377555458281795643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355560918370305521197095 6533341377555458281795643)
        ·
          refine ⟨9800012066333187422693465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533341377555458281795643 9800012066333187422693465)
          ·
            refine ⟨7350009049749890567020099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9800012066333187422693465 7350009049749890567020099)
            ·
              refine ⟨11025013574624835850530149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350009049749890567020099 11025013574624835850530149)
              ·
                refine ⟨2067190045242156721974403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11025013574624835850530149 2067190045242156721974403)
                ·
                  refine ⟨3100785067863235082961605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067190045242156721974403 3100785067863235082961605)
                  ·
                    refine ⟨581397200224356578055301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100785067863235082961605 581397200224356578055301)
                    ·
                      rfl

theorem cell23_3396801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3396801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396801 prefixEnd_3396801 := by exact prefixLift 3396801
  have htrace : WordTrace (prefixWord ++ tailWord_3396801) baseStart_3396801 baseEnd_3396801 := by
    simpa [prefixWord, tailWord_3396801, baseEnd_3396801] using wordTrace_append hprefix tailTrace_3396801
  have hstable : (prefixWord ++ tailWord_3396801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396801).length < 2 ^ (prefixWord ++ tailWord_3396801).sum := by decide
  have hdescent : baseEnd_3396801 < baseStart_3396801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396810 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3396810 : Nat := 118140960795 + 3396810 * 2 ^ 59
def prefixEnd_3396810 : Nat := 4983230072969 + 3 ^ 40 * 3396810 * 2
def baseEnd_3396810 : Nat := 581398740666320066317787

theorem tailTrace_3396810 : CollatzResearch.WordTrace tailWord_3396810 prefixEnd_3396810 581398740666320066317787 := by
  unfold tailWord_3396810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30972959705986243451670971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82594559215963315871122589 30972959705986243451670971)
  ·
    refine ⟨46459439558979365177506457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30972959705986243451670971 46459439558979365177506457)
    ·
      refine ⟨34844579669234523883129843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46459439558979365177506457 34844579669234523883129843)
      ·
        refine ⟨52266869503851785824694765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34844579669234523883129843 52266869503851785824694765)
        ·
          refine ⟨19600076063944419684260537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52266869503851785824694765 19600076063944419684260537)
          ·
            refine ⟨14700057047958314763195403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19600076063944419684260537 14700057047958314763195403)
            ·
              refine ⟨22050085571937472144793105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700057047958314763195403 22050085571937472144793105)
              ·
                refine ⟨16537564178953104108594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22050085571937472144793105 16537564178953104108594829)
                ·
                  refine ⟨6201586567107414040723061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16537564178953104108594829 6201586567107414040723061)
                  ·
                    refine ⟨581398740666320066317787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6201586567107414040723061 581398740666320066317787)
                    ·
                      rfl

theorem cell23_3396810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3396810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396810 prefixEnd_3396810 := by exact prefixLift 3396810
  have htrace : WordTrace (prefixWord ++ tailWord_3396810) baseStart_3396810 baseEnd_3396810 := by
    simpa [prefixWord, tailWord_3396810, baseEnd_3396810] using wordTrace_append hprefix tailTrace_3396810
  have hstable : (prefixWord ++ tailWord_3396810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396810).length < 2 ^ (prefixWord ++ tailWord_3396810).sum := by decide
  have hdescent : baseEnd_3396810 < baseStart_3396810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396824 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_3396824 : Nat := 118140960795 + 3396824 * 2 ^ 59
def prefixEnd_3396824 : Nat := 4983230072969 + 3 ^ 40 * 3396824 * 2
def baseEnd_3396824 : Nat := 1744203410728123144178297

theorem tailTrace_3396824 : CollatzResearch.WordTrace tailWord_3396824 prefixEnd_3396824 1744203410728123144178297 := by
  unfold tailWord_3396824
  simp only [CollatzResearch.WordTrace]
  refine ⟨61946174722947127098846763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82594899630596169465129017 61946174722947127098846763)
  ·
    refine ⟨92919262084420690648270145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61946174722947127098846763 92919262084420690648270145)
    ·
      refine ⟨69689446563315517986202609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92919262084420690648270145 69689446563315517986202609)
      ·
        refine ⟨52267084922486638489651957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69689446563315517986202609 52267084922486638489651957)
        ·
          refine ⟨4900039211483122358404871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52267084922486638489651957 4900039211483122358404871)
          ·
            refine ⟨7350058817224683537607307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900039211483122358404871 7350058817224683537607307)
            ·
              refine ⟨11025088225837025306410961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350058817224683537607307 11025088225837025306410961)
              ·
                refine ⟨8268816169377768979808221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11025088225837025306410961 8268816169377768979808221)
                ·
                  refine ⟨3100806063516663367428083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8268816169377768979808221 3100806063516663367428083)
                  ·
                    refine ⟨4651209095274995051142125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100806063516663367428083 4651209095274995051142125)
                    ·
                      refine ⟨1744203410728123144178297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651209095274995051142125 1744203410728123144178297)
                      ·
                        rfl

theorem cell23_3396824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_3396824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396824 prefixEnd_3396824 := by exact prefixLift 3396824
  have htrace : WordTrace (prefixWord ++ tailWord_3396824) baseStart_3396824 baseEnd_3396824 := by
    simpa [prefixWord, tailWord_3396824, baseEnd_3396824] using wordTrace_append hprefix tailTrace_3396824
  have hstable : (prefixWord ++ tailWord_3396824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396824).length < 2 ^ (prefixWord ++ tailWord_3396824).sum := by decide
  have hdescent : baseEnd_3396824 < baseStart_3396824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396840 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_3396840 : Nat := 118140960795 + 3396840 * 2 ^ 59
def prefixEnd_3396840 : Nat := 4983230072969 + 3 ^ 40 * 3396840 * 2
def baseEnd_3396840 : Nat := 581403875472865027192741

theorem tailTrace_3396840 : CollatzResearch.WordTrace tailWord_3396840 prefixEnd_3396840 581403875472865027192741 := by
  unfold tailWord_3396840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61946466506918144465137987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82595288675890859286850649 61946466506918144465137987)
  ·
    refine ⟨92919699760377216697706981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61946466506918144465137987 92919699760377216697706981)
    ·
      refine ⟨17422443705070728130820059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92919699760377216697706981 17422443705070728130820059)
      ·
        refine ⟨26133665557606092196230089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17422443705070728130820059 26133665557606092196230089)
        ·
          refine ⟨19600249168204569147172567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26133665557606092196230089 19600249168204569147172567)
          ·
            refine ⟨29400373752306853720758851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19600249168204569147172567 29400373752306853720758851)
            ·
              refine ⟨44100560628460280581138277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29400373752306853720758851 44100560628460280581138277)
              ·
                refine ⟨8268855117836302608963427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44100560628460280581138277 8268855117836302608963427)
                ·
                  refine ⟨12403282676754453913445141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8268855117836302608963427 12403282676754453913445141)
                  ·
                    refine ⟨581403875472865027192741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12403282676754453913445141 581403875472865027192741)
                    ·
                      rfl

theorem cell23_3396840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_3396840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396840 prefixEnd_3396840 := by exact prefixLift 3396840
  have htrace : WordTrace (prefixWord ++ tailWord_3396840) baseStart_3396840 baseEnd_3396840 := by
    simpa [prefixWord, tailWord_3396840, baseEnd_3396840] using wordTrace_append hprefix tailTrace_3396840
  have hstable : (prefixWord ++ tailWord_3396840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396840).length < 2 ^ (prefixWord ++ tailWord_3396840).sum := by decide
  have hdescent : baseEnd_3396840 < baseStart_3396840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396844 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_3396844 : Nat := 118140960795 + 3396844 * 2 ^ 59
def prefixEnd_3396844 : Nat := 4983230072969 + 3 ^ 40 * 3396844 * 2
def baseEnd_3396844 : Nat := 581404560113737688642735

theorem tailTrace_3396844 : CollatzResearch.WordTrace tailWord_3396844 prefixEnd_3396844 581404560113737688642735 := by
  unfold tailWord_3396844
  simp only [CollatzResearch.WordTrace]
  refine ⟨61946539452910898806710793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82595385937214531742281057 61946539452910898806710793)
  ·
    refine ⟨46459904589683174105033095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61946539452910898806710793 46459904589683174105033095)
    ·
      refine ⟨69689856884524761157549643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46459904589683174105033095 69689856884524761157549643)
      ·
        refine ⟨104534785326787141736324465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69689856884524761157549643 104534785326787141736324465)
        ·
          refine ⟨78401088995090356302243349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104534785326787141736324465 78401088995090356302243349)
          ·
            refine ⟨3675051046644860451667657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78401088995090356302243349 3675051046644860451667657)
            ·
              refine ⟨2756288284983645338750743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675051046644860451667657 2756288284983645338750743)
              ·
                refine ⟨4134432427475468008126115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756288284983645338750743 4134432427475468008126115)
                ·
                  refine ⟨6201648641213202012189173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134432427475468008126115 6201648641213202012189173)
                  ·
                    refine ⟨581404560113737688642735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6201648641213202012189173 581404560113737688642735)
                    ·
                      rfl

theorem cell23_3396844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_3396844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396844 prefixEnd_3396844 := by exact prefixLift 3396844
  have htrace : WordTrace (prefixWord ++ tailWord_3396844) baseStart_3396844 baseEnd_3396844 := by
    simpa [prefixWord, tailWord_3396844, baseEnd_3396844] using wordTrace_append hprefix tailTrace_3396844
  have hstable : (prefixWord ++ tailWord_3396844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396844).length < 2 ^ (prefixWord ++ tailWord_3396844).sum := by decide
  have hdescent : baseEnd_3396844 < baseStart_3396844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396914 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_3396914 : Nat := 118140960795 + 3396914 * 2 ^ 59
def prefixEnd_3396914 : Nat := 4983230072969 + 3 ^ 40 * 3396914 * 2
def baseEnd_3396914 : Nat := 1744249623987027792052883

theorem tailTrace_3396914 : CollatzResearch.WordTrace tailWord_3396914 prefixEnd_3396914 1744249623987027792052883 := by
  unfold tailWord_3396914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30973908003892049892117449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82597088010378799712313197 30973908003892049892117449)
  ·
    refine ⟨23230431002919037419088087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30973908003892049892117449 23230431002919037419088087)
    ·
      refine ⟨34845646504378556128632131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23230431002919037419088087 34845646504378556128632131)
      ·
        refine ⟨52268469756567834192948197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34845646504378556128632131 52268469756567834192948197)
        ·
          refine ⟨9800338079356468911177787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52268469756567834192948197 9800338079356468911177787)
          ·
            refine ⟨14700507119034703366766681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800338079356468911177787 14700507119034703366766681)
            ·
              refine ⟨11025380339276027525075011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14700507119034703366766681 11025380339276027525075011)
              ·
                refine ⟨16538070508914041287612517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025380339276027525075011 16538070508914041287612517)
                ·
                  refine ⟨3100888220421382741427347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16538070508914041287612517 3100888220421382741427347)
                  ·
                    refine ⟨4651332330632074112141021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3100888220421382741427347 4651332330632074112141021)
                    ·
                      refine ⟨1744249623987027792052883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651332330632074112141021 1744249623987027792052883)
                      ·
                        rfl

theorem cell23_3396914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_3396914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396914 prefixEnd_3396914 := by exact prefixLift 3396914
  have htrace : WordTrace (prefixWord ++ tailWord_3396914) baseStart_3396914 baseEnd_3396914 := by
    simpa [prefixWord, tailWord_3396914, baseEnd_3396914] using wordTrace_append hprefix tailTrace_3396914
  have hstable : (prefixWord ++ tailWord_3396914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396914).length < 2 ^ (prefixWord ++ tailWord_3396914).sum := by decide
  have hdescent : baseEnd_3396914 < baseStart_3396914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396920 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_3396920 : Nat := 118140960795 + 3396920 * 2 ^ 59
def prefixEnd_3396920 : Nat := 4983230072969 + 3 ^ 40 * 3396920 * 2
def baseEnd_3396920 : Nat := 1744252704870954768577855

theorem tailTrace_3396920 : CollatzResearch.WordTrace tailWord_3396920 prefixEnd_3396920 1744252704870954768577855 := by
  unfold tailWord_3396920
  simp only [CollatzResearch.WordTrace]
  refine ⟨61947925426773231296594107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82597233902364308395458809 61947925426773231296594107)
  ·
    refine ⟨92921888140159846944891161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61947925426773231296594107 92921888140159846944891161)
    ·
      refine ⟨69691416105119885208668371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92921888140159846944891161 69691416105119885208668371)
      ·
        refine ⟨104537124157679827813002557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69691416105119885208668371 104537124157679827813002557)
        ·
          refine ⟨39201421559129935429875959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104537124157679827813002557 39201421559129935429875959)
          ·
            refine ⟨58802132338694903144813939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39201421559129935429875959 58802132338694903144813939)
            ·
              refine ⟨88203198508042354717220909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58802132338694903144813939 88203198508042354717220909)
              ·
                refine ⟨33076199440515883018957841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88203198508042354717220909 33076199440515883018957841)
                ·
                  refine ⟨24807149580386912264218381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33076199440515883018957841 24807149580386912264218381)
                  ·
                    refine ⟨9302681092645092099081893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24807149580386912264218381 9302681092645092099081893)
                    ·
                      refine ⟨1744252704870954768577855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9302681092645092099081893 1744252704870954768577855)
                      ·
                        rfl

theorem cell23_3396920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_3396920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396920 prefixEnd_3396920 := by exact prefixLift 3396920
  have htrace : WordTrace (prefixWord ++ tailWord_3396920) baseStart_3396920 baseEnd_3396920 := by
    simpa [prefixWord, tailWord_3396920, baseEnd_3396920] using wordTrace_append hprefix tailTrace_3396920
  have hstable : (prefixWord ++ tailWord_3396920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396920).length < 2 ^ (prefixWord ++ tailWord_3396920).sum := by decide
  have hdescent : baseEnd_3396920 < baseStart_3396920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396925 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_3396925 : Nat := 118140960795 + 3396925 * 2 ^ 59
def prefixEnd_3396925 : Nat := 4983230072969 + 3 ^ 40 * 3396925 * 2
def baseEnd_3396925 : Nat := 581418424091409083005111

theorem tailTrace_3396925 : CollatzResearch.WordTrace tailWord_3396925 prefixEnd_3396925 581418424091409083005111 := by
  unfold tailWord_3396925
  simp only [CollatzResearch.WordTrace]
  refine ⟨123896033218528348447120229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82597355479018898964746819 123896033218528348447120229)
  ·
    refine ⟨23230506228474065333835043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123896033218528348447120229 23230506228474065333835043)
    ·
      refine ⟨34845759342711098000752565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23230506228474065333835043 34845759342711098000752565)
      ·
        refine ⟨3266789938379165437570553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34845759342711098000752565 3266789938379165437570553)
        ·
          refine ⟨2450092453784374078177915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3266789938379165437570553 2450092453784374078177915)
          ·
            refine ⟨3675138680676561117266873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450092453784374078177915 3675138680676561117266873)
            ·
              refine ⟨2756354010507420837950155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675138680676561117266873 2756354010507420837950155)
              ·
                refine ⟨4134531015761131256925233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756354010507420837950155 4134531015761131256925233)
                ·
                  refine ⟨3100898261820848442693925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134531015761131256925233 3100898261820848442693925)
                  ·
                    refine ⟨581418424091409083005111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100898261820848442693925 581418424091409083005111)
                    ·
                      rfl

theorem cell23_3396925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_3396925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396925 prefixEnd_3396925 := by exact prefixLift 3396925
  have htrace : WordTrace (prefixWord ++ tailWord_3396925) baseStart_3396925 baseEnd_3396925 := by
    simpa [prefixWord, tailWord_3396925, baseEnd_3396925] using wordTrace_append hprefix tailTrace_3396925
  have hstable : (prefixWord ++ tailWord_3396925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396925).length < 2 ^ (prefixWord ++ tailWord_3396925).sum := by decide
  have hdescent : baseEnd_3396925 < baseStart_3396925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396954 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_3396954 : Nat := 118140960795 + 3396954 * 2 ^ 59
def prefixEnd_3396954 : Nat := 4983230072969 + 3 ^ 40 * 3396954 * 2
def baseEnd_3396954 : Nat := 1744270163213207635552699

theorem tailTrace_3396954 : CollatzResearch.WordTrace tailWord_3396954 prefixEnd_3396954 1744270163213207635552699 := by
  unfold tailWord_3396954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30974272733855821599981479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82598060623615524266617277 30974272733855821599981479)
  ·
    refine ⟨46461409100783732399972219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30974272733855821599981479 46461409100783732399972219)
    ·
      refine ⟨69692113651175598599958329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46461409100783732399972219 69692113651175598599958329)
      ·
        refine ⟨52269085238381698949968747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69692113651175598599958329 52269085238381698949968747)
        ·
          refine ⟨78403627857572548424953121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52269085238381698949968747 78403627857572548424953121)
          ·
            refine ⟨58802720893179411318714841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78403627857572548424953121 58802720893179411318714841)
            ·
              refine ⟨44102040669884558489036131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58802720893179411318714841 44102040669884558489036131)
              ·
                refine ⟨66153061004826837733554197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44102040669884558489036131 66153061004826837733554197)
                ·
                  refine ⟨3100924734601258018760353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66153061004826837733554197 3100924734601258018760353)
                  ·
                    refine ⟨2325693550950943514070265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3100924734601258018760353 2325693550950943514070265)
                    ·
                      refine ⟨1744270163213207635552699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325693550950943514070265 1744270163213207635552699)
                      ·
                        rfl

theorem cell23_3396954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_3396954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396954 prefixEnd_3396954 := by exact prefixLift 3396954
  have htrace : WordTrace (prefixWord ++ tailWord_3396954) baseStart_3396954 baseEnd_3396954 := by
    simpa [prefixWord, tailWord_3396954, baseEnd_3396954] using wordTrace_append hprefix tailTrace_3396954
  have hstable : (prefixWord ++ tailWord_3396954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396954).length < 2 ^ (prefixWord ++ tailWord_3396954).sum := by decide
  have hdescent : baseEnd_3396954 < baseStart_3396954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396987 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3]
def baseStart_3396987 : Nat := 118140960795 + 3396987 * 2 ^ 59
def prefixEnd_3396987 : Nat := 4983230072969 + 3 ^ 40 * 3396987 * 2
def baseEnd_3396987 : Nat := 1744287108074806006440047

theorem tailTrace_3396987 : CollatzResearch.WordTrace tailWord_3396987 prefixEnd_3396987 1744287108074806006440047 := by
  unfold tailWord_3396987
  simp only [CollatzResearch.WordTrace]
  refine ⟨123898294544303733035877215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82598863029535822023918143 123898294544303733035877215)
  ·
    refine ⟨185847441816455599553815823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123898294544303733035877215 185847441816455599553815823)
    ·
      refine ⟨278771162724683399330723735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185847441816455599553815823 278771162724683399330723735)
      ·
        refine ⟨418156744087025098996085603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278771162724683399330723735 418156744087025098996085603)
        ·
          refine ⟨627235116130537648494128405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418156744087025098996085603 627235116130537648494128405)
          ·
            refine ⟨29401646068618952273162269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 627235116130537648494128405 29401646068618952273162269)
            ·
              refine ⟨11025617275732107102435851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29401646068618952273162269 11025617275732107102435851)
              ·
                refine ⟨16538425913598160653653777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025617275732107102435851 16538425913598160653653777)
                ·
                  refine ⟨12403819435198620490240333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16538425913598160653653777 12403819435198620490240333)
                  ·
                    refine ⟨4651432288199482683840125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12403819435198620490240333 4651432288199482683840125)
                    ·
                      refine ⟨1744287108074806006440047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651432288199482683840125 1744287108074806006440047)
                      ·
                        rfl

theorem cell23_3396987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3].length) (baseStart_3396987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396987 prefixEnd_3396987 := by exact prefixLift 3396987
  have htrace : WordTrace (prefixWord ++ tailWord_3396987) baseStart_3396987 baseEnd_3396987 := by
    simpa [prefixWord, tailWord_3396987, baseEnd_3396987] using wordTrace_append hprefix tailTrace_3396987
  have hstable : (prefixWord ++ tailWord_3396987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396987).length < 2 ^ (prefixWord ++ tailWord_3396987).sum := by decide
  have hdescent : baseEnd_3396987 < baseStart_3396987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396994 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3396994 : Nat := 118140960795 + 3396994 * 2 ^ 59
def prefixEnd_3396994 : Nat := 4983230072969 + 3 ^ 40 * 3396994 * 2
def baseEnd_3396994 : Nat := 193810078048820831005835

theorem tailTrace_3396994 : CollatzResearch.WordTrace tailWord_3396994 prefixEnd_3396994 193810078048820831005835 := by
  unfold tailWord_3396994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30974637463819593307845509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82599033236852248820921357 30974637463819593307845509)
  ·
    refine ⟨5807744524466173745221033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30974637463819593307845509 5807744524466173745221033)
    ·
      refine ⟨4355808393349630308915775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5807744524466173745221033 4355808393349630308915775)
      ·
        refine ⟨6533712590024445463373663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355808393349630308915775 6533712590024445463373663)
        ·
          refine ⟨9800568885036668195060495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533712590024445463373663 9800568885036668195060495)
          ·
            refine ⟨14700853327555002292590743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800568885036668195060495 14700853327555002292590743)
            ·
              refine ⟨22051279991332503438886115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700853327555002292590743 22051279991332503438886115)
              ·
                refine ⟨33076919986998755158329173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22051279991332503438886115 33076919986998755158329173)
                ·
                  refine ⟨193810078048820831005835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33076919986998755158329173 193810078048820831005835)
                  ·
                    rfl

theorem cell23_3396994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3396994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3396994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3396994 prefixEnd_3396994 := by exact prefixLift 3396994
  have htrace : WordTrace (prefixWord ++ tailWord_3396994) baseStart_3396994 baseEnd_3396994 := by
    simpa [prefixWord, tailWord_3396994, baseEnd_3396994] using wordTrace_append hprefix tailTrace_3396994
  have hstable : (prefixWord ++ tailWord_3396994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396994).length < 2 ^ (prefixWord ++ tailWord_3396994).sum := by decide
  have hdescent : baseEnd_3396994 < baseStart_3396994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397022 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3397022 : Nat := 118140960795 + 3397022 * 2 ^ 59
def prefixEnd_3397022 : Nat := 4983230072969 + 3 ^ 40 * 3397022 * 2
def baseEnd_3397022 : Nat := 1744305079897713369502387

theorem tailTrace_3397022 : CollatzResearch.WordTrace tailWord_3397022 prefixEnd_3397022 1744305079897713369502387 := by
  unfold tailWord_3397022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487446387397116751675165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82599714066117956008934213 15487446387397116751675165)
  ·
    refine ⟨5807792395273918781878187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15487446387397116751675165 5807792395273918781878187)
    ·
      refine ⟨8711688592910878172817281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807792395273918781878187 8711688592910878172817281)
      ·
        refine ⟨6533766444683158629612961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8711688592910878172817281 6533766444683158629612961)
        ·
          refine ⟨4900324833512368972209721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533766444683158629612961 4900324833512368972209721)
          ·
            refine ⟨3675243625134276729157291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900324833512368972209721 3675243625134276729157291)
            ·
              refine ⟨5512865437701415093735937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675243625134276729157291 5512865437701415093735937)
              ·
                refine ⟨4134649078276061320301953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512865437701415093735937 4134649078276061320301953)
                ·
                  refine ⟨3100986808707045990226465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134649078276061320301953 3100986808707045990226465)
                  ·
                    refine ⟨2325740106530284492669849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3100986808707045990226465 2325740106530284492669849)
                    ·
                      refine ⟨1744305079897713369502387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325740106530284492669849 1744305079897713369502387)
                      ·
                        rfl

theorem cell23_3397022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3397022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397022 prefixEnd_3397022 := by exact prefixLift 3397022
  have htrace : WordTrace (prefixWord ++ tailWord_3397022) baseStart_3397022 baseEnd_3397022 := by
    simpa [prefixWord, tailWord_3397022, baseEnd_3397022] using wordTrace_append hprefix tailTrace_3397022
  have hstable : (prefixWord ++ tailWord_3397022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397022).length < 2 ^ (prefixWord ++ tailWord_3397022).sum := by decide
  have hdescent : baseEnd_3397022 < baseStart_3397022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397027 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4]
def baseStart_3397027 : Nat := 118140960795 + 3397027 * 2 ^ 59
def prefixEnd_3397027 : Nat := 4983230072969 + 3 ^ 40 * 3397027 * 2
def baseEnd_3397027 : Nat := 1744307647300985849939863

theorem tailTrace_3397027 : CollatzResearch.WordTrace tailWord_3397027 prefixEnd_3397027 1744307647300985849939863 := by
  unfold tailWord_3397027
  simp only [CollatzResearch.WordTrace]
  refine ⟨123899753464158819867333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82599835642772546578222223 123899753464158819867333335)
  ·
    refine ⟨185849630196238229801000003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123899753464158819867333335 185849630196238229801000003)
    ·
      refine ⟨278774445294357344701500005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185849630196238229801000003 278774445294357344701500005)
      ·
        refine ⟨52270208492692002131531251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278774445294357344701500005 52270208492692002131531251)
        ·
          refine ⟨78405312739038003197296877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52270208492692002131531251 78405312739038003197296877)
          ·
            refine ⟨29401992277139251198986329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78405312739038003197296877 29401992277139251198986329)
            ·
              refine ⟨22051494207854438399239747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29401992277139251198986329 22051494207854438399239747)
              ·
                refine ⟨33077241311781657598859621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22051494207854438399239747 33077241311781657598859621)
                ·
                  refine ⟨6201982745959060799786179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33077241311781657598859621 6201982745959060799786179)
                  ·
                    refine ⟨9302974118938591199679269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6201982745959060799786179 9302974118938591199679269)
                    ·
                      refine ⟨1744307647300985849939863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9302974118938591199679269 1744307647300985849939863)
                      ·
                        rfl

theorem cell23_3397027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_3397027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397027 prefixEnd_3397027 := by exact prefixLift 3397027
  have htrace : WordTrace (prefixWord ++ tailWord_3397027) baseStart_3397027 baseEnd_3397027 := by
    simpa [prefixWord, tailWord_3397027, baseEnd_3397027] using wordTrace_append hprefix tailTrace_3397027
  have hstable : (prefixWord ++ tailWord_3397027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397027).length < 2 ^ (prefixWord ++ tailWord_3397027).sum := by decide
  have hdescent : baseEnd_3397027 < baseStart_3397027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397047 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_3397047 : Nat := 118140960795 + 3397047 * 2 ^ 59
def prefixEnd_3397047 : Nat := 4983230072969 + 3 ^ 40 * 3397047 * 2
def baseEnd_3397047 : Nat := 1744317916914075771689771

theorem tailTrace_3397047 : CollatzResearch.WordTrace tailWord_3397047 prefixEnd_3397047 1744317916914075771689771 := by
  unfold tailWord_3397047
  simp only [CollatzResearch.WordTrace]
  refine ⟨123900482924086363283061395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82600321949390908855374263 123900482924086363283061395)
  ·
    refine ⟨185850724386129544924592093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123900482924086363283061395 185850724386129544924592093)
    ·
      refine ⟨69694021644798579346722035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185850724386129544924592093 69694021644798579346722035)
      ·
        refine ⟨104541032467197869020083053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69694021644798579346722035 104541032467197869020083053)
        ·
          refine ⟨39202887175199200882531145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104541032467197869020083053 39202887175199200882531145)
          ·
            refine ⟨29402165381399400661898359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39202887175199200882531145 29402165381399400661898359)
            ·
              refine ⟨44103248072099100992847539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29402165381399400661898359 44103248072099100992847539)
              ·
                refine ⟨66154872108148651489271309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44103248072099100992847539 66154872108148651489271309)
                ·
                  refine ⟨24808077040555744308476741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66154872108148651489271309 24808077040555744308476741)
                  ·
                    refine ⟨4651514445104202057839389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24808077040555744308476741 4651514445104202057839389)
                    ·
                      refine ⟨1744317916914075771689771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651514445104202057839389 1744317916914075771689771)
                      ·
                        rfl

theorem cell23_3397047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_3397047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397047 prefixEnd_3397047 := by exact prefixLift 3397047
  have htrace : WordTrace (prefixWord ++ tailWord_3397047) baseStart_3397047 baseEnd_3397047 := by
    simpa [prefixWord, tailWord_3397047, baseEnd_3397047] using wordTrace_append hprefix tailTrace_3397047
  have hstable : (prefixWord ++ tailWord_3397047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397047).length < 2 ^ (prefixWord ++ tailWord_3397047).sum := by decide
  have hdescent : baseEnd_3397047 < baseStart_3397047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397064 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_3397064 : Nat := 118140960795 + 3397064 * 2 ^ 59
def prefixEnd_3397064 : Nat := 4983230072969 + 3 ^ 40 * 3397064 * 2
def baseEnd_3397064 : Nat := 1744326646085202205177193

theorem tailTrace_3397064 : CollatzResearch.WordTrace tailWord_3397064 prefixEnd_3397064 1744326646085202205177193 := by
  unfold tailWord_3397064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61950551482512387593215123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82600735310016516790953497 61950551482512387593215123)
  ·
    refine ⟨92925827223768581389822685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61950551482512387593215123 92925827223768581389822685)
    ·
      refine ⟨34847185208913218021183507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92925827223768581389822685 34847185208913218021183507)
      ·
        refine ⟨52270777813369827031775261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34847185208913218021183507 52270777813369827031775261)
        ·
          refine ⟨19601541680013685136915723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52270777813369827031775261 19601541680013685136915723)
          ·
            refine ⟨29402312520020527705373585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19601541680013685136915723 29402312520020527705373585)
            ·
              refine ⟨22051734390015395779030189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29402312520020527705373585 22051734390015395779030189)
              ·
                refine ⟨8269400396255773417136321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22051734390015395779030189 8269400396255773417136321)
                ·
                  refine ⟨6202050297191830062852241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8269400396255773417136321 6202050297191830062852241)
                  ·
                    refine ⟨4651537722893872547139181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6202050297191830062852241 4651537722893872547139181)
                    ·
                      refine ⟨1744326646085202205177193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651537722893872547139181 1744326646085202205177193)
                      ·
                        rfl

theorem cell23_3397064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_3397064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397064 prefixEnd_3397064 := by exact prefixLift 3397064
  have htrace : WordTrace (prefixWord ++ tailWord_3397064) baseStart_3397064 baseEnd_3397064 := by
    simpa [prefixWord, tailWord_3397064, baseEnd_3397064] using wordTrace_append hprefix tailTrace_3397064
  have hstable : (prefixWord ++ tailWord_3397064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397064).length < 2 ^ (prefixWord ++ tailWord_3397064).sum := by decide
  have hdescent : baseEnd_3397064 < baseStart_3397064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397071 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 1, 4]
def baseStart_3397071 : Nat := 118140960795 + 3397071 * 2 ^ 59
def prefixEnd_3397071 : Nat := 4983230072969 + 3 ^ 40 * 3397071 * 2
def baseEnd_3397071 : Nat := 581443413483261225929887

theorem tailTrace_3397071 : CollatzResearch.WordTrace tailWord_3397071 prefixEnd_3397071 581443413483261225929887 := by
  unfold tailWord_3397071
  simp only [CollatzResearch.WordTrace]
  refine ⟨123901358275999415381935067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82600905517332943587956711 123901358275999415381935067)
  ·
    refine ⟨185852037413999123072902601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123901358275999415381935067 185852037413999123072902601)
    ·
      refine ⟨139389028060499342304676951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185852037413999123072902601 139389028060499342304676951)
      ·
        refine ⟨209083542090749013457015427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139389028060499342304676951 209083542090749013457015427)
        ·
          refine ⟨313625313136123520185523141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209083542090749013457015427 313625313136123520185523141)
          ·
            refine ⟨58804746213023160034785589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313625313136123520185523141 58804746213023160034785589)
            ·
              refine ⟨5512944957470921253261149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58804746213023160034785589 5512944957470921253261149)
              ·
                refine ⟨2067354359051595469972931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5512944957470921253261149 2067354359051595469972931)
                ·
                  refine ⟨3101031538577393204959397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067354359051595469972931 3101031538577393204959397)
                  ·
                    refine ⟨581443413483261225929887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101031538577393204959397 581443413483261225929887)
                    ·
                      rfl

theorem cell23_3397071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 4].length) (baseStart_3397071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397071 prefixEnd_3397071 := by exact prefixLift 3397071
  have htrace : WordTrace (prefixWord ++ tailWord_3397071) baseStart_3397071 baseEnd_3397071 := by
    simpa [prefixWord, tailWord_3397071, baseEnd_3397071] using wordTrace_append hprefix tailTrace_3397071
  have hstable : (prefixWord ++ tailWord_3397071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397071).length < 2 ^ (prefixWord ++ tailWord_3397071).sum := by decide
  have hdescent : baseEnd_3397071 < baseStart_3397071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397101 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3397101 : Nat := 118140960795 + 3397101 * 2 ^ 59
def prefixEnd_3397101 : Nat := 4983230072969 + 3 ^ 40 * 3397101 * 2
def baseEnd_3397101 : Nat := 193816182763268728934947

theorem tailTrace_3397101 : CollatzResearch.WordTrace tailWord_3397101 prefixEnd_3397101 193816182763268728934947 := by
  unfold tailWord_3397101
  simp only [CollatzResearch.WordTrace]
  refine ⟨123902452465890730505527157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82601634977260487003684771 123902452465890730505527157)
  ·
    refine ⟨11615854918677255984893171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123902452465890730505527157 11615854918677255984893171)
    ·
      refine ⟨17423782378015883977339757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615854918677255984893171 17423782378015883977339757)
      ·
        refine ⟨6533918391755956491502409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17423782378015883977339757 6533918391755956491502409)
        ·
          refine ⟨4900438793816967368626807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533918391755956491502409 4900438793816967368626807)
          ·
            refine ⟨7350658190725451052940211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900438793816967368626807 7350658190725451052940211)
            ·
              refine ⟨11025987286088176579410317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350658190725451052940211 11025987286088176579410317)
              ·
                refine ⟨4134745232283066217278869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11025987286088176579410317 4134745232283066217278869)
                ·
                  refine ⟨193816182763268728934947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4134745232283066217278869 193816182763268728934947)
                  ·
                    rfl

theorem cell23_3397101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3397101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397101 prefixEnd_3397101 := by exact prefixLift 3397101
  have htrace : WordTrace (prefixWord ++ tailWord_3397101) baseStart_3397101 baseEnd_3397101 := by
    simpa [prefixWord, tailWord_3397101, baseEnd_3397101] using wordTrace_append hprefix tailTrace_3397101
  have hstable : (prefixWord ++ tailWord_3397101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397101).length < 2 ^ (prefixWord ++ tailWord_3397101).sum := by decide
  have hdescent : baseEnd_3397101 < baseStart_3397101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397154 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3397154 : Nat := 118140960795 + 3397154 * 2 ^ 59
def prefixEnd_3397154 : Nat := 4983230072969 + 3 ^ 40 * 3397154 * 2
def baseEnd_3397154 : Nat := 1744372859344106853051779

theorem tailTrace_3397154 : CollatzResearch.WordTrace tailWord_3397154 prefixEnd_3397154 1744372859344106853051779 := by
  unfold tailWord_3397154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976096383674680139301629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82602923689799147038137677 30976096383674680139301629)
  ·
    refine ⟨11616036143878005052238111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30976096383674680139301629 11616036143878005052238111)
    ·
      refine ⟨17424054215817007578357167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11616036143878005052238111 17424054215817007578357167)
      ·
        refine ⟨26136081323725511367535751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17424054215817007578357167 26136081323725511367535751)
        ·
          refine ⟨39204121985588267051303627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26136081323725511367535751 39204121985588267051303627)
          ·
            refine ⟨58806182978382400576955441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39204121985588267051303627 58806182978382400576955441)
            ·
              refine ⟨44104637233786800432716581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58806182978382400576955441 44104637233786800432716581)
              ·
                refine ⟨8269619481335025081134359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44104637233786800432716581 8269619481335025081134359)
                ·
                  refine ⟨12404429222002537621701539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269619481335025081134359 12404429222002537621701539)
                  ·
                    refine ⟨18606643833003806432552309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12404429222002537621701539 18606643833003806432552309)
                    ·
                      refine ⟨1744372859344106853051779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18606643833003806432552309 1744372859344106853051779)
                      ·
                        rfl

theorem cell23_3397154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3397154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397154 prefixEnd_3397154 := by exact prefixLift 3397154
  have htrace : WordTrace (prefixWord ++ tailWord_3397154) baseStart_3397154 baseEnd_3397154 := by
    simpa [prefixWord, tailWord_3397154, baseEnd_3397154] using wordTrace_append hprefix tailTrace_3397154
  have hstable : (prefixWord ++ tailWord_3397154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397154).length < 2 ^ (prefixWord ++ tailWord_3397154).sum := by decide
  have hdescent : baseEnd_3397154 < baseStart_3397154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397201 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_3397201 : Nat := 118140960795 + 3397201 * 2 ^ 59
def prefixEnd_3397201 : Nat := 4983230072969 + 3 ^ 40 * 3397201 * 2
def baseEnd_3397201 : Nat := 1744396992934868169164063

theorem tailTrace_3397201 : CollatzResearch.WordTrace tailWord_3397201 prefixEnd_3397201 1744396992934868169164063 := by
  unfold tailWord_3397201
  simp only [CollatzResearch.WordTrace]
  refine ⟨123906099765528447584167457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82604066510352298389444971 123906099765528447584167457)
  ·
    refine ⟨92929574824146335688125593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123906099765528447584167457 92929574824146335688125593)
    ·
      refine ⟨69697181118109751766094195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92929574824146335688125593 69697181118109751766094195)
      ·
        refine ⟨104545771677164627649141293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69697181118109751766094195 104545771677164627649141293)
        ·
          refine ⟨39204664378936735368427985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104545771677164627649141293 39204664378936735368427985)
          ·
            refine ⟨29403498284202551526320989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39204664378936735368427985 29403498284202551526320989)
            ·
              refine ⟨11026311856575956822370371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29403498284202551526320989 11026311856575956822370371)
              ·
                refine ⟨16539467784863935233555557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026311856575956822370371 16539467784863935233555557)
                ·
                  refine ⟨3101150209661987856291667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16539467784863935233555557 3101150209661987856291667)
                  ·
                    refine ⟨4651725314492981784437501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3101150209661987856291667 4651725314492981784437501)
                    ·
                      refine ⟨1744396992934868169164063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651725314492981784437501 1744396992934868169164063)
                      ·
                        rfl

theorem cell23_3397201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_3397201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397201 prefixEnd_3397201 := by exact prefixLift 3397201
  have htrace : WordTrace (prefixWord ++ tailWord_3397201) baseStart_3397201 baseEnd_3397201 := by
    simpa [prefixWord, tailWord_3397201, baseEnd_3397201] using wordTrace_append hprefix tailTrace_3397201
  have hstable : (prefixWord ++ tailWord_3397201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397201).length < 2 ^ (prefixWord ++ tailWord_3397201).sum := by decide
  have hdescent : baseEnd_3397201 < baseStart_3397201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397241 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 3, 4, 2]
def baseStart_3397241 : Nat := 118140960795 + 3397241 * 2 ^ 59
def prefixEnd_3397241 : Nat := 4983230072969 + 3 ^ 40 * 3397241 * 2
def baseEnd_3397241 : Nat := 1744417532161048012663879

theorem tailTrace_3397241 : CollatzResearch.WordTrace tailWord_3397241 prefixEnd_3397241 1744417532161048012663879 := by
  unfold tailWord_3397241
  simp only [CollatzResearch.WordTrace]
  refine ⟨123907558685383534415623577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82605039123589022943749051 123907558685383534415623577)
  ·
    refine ⟨92930669014037650811717683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123907558685383534415623577 92930669014037650811717683)
    ·
      refine ⟨139396003521056476217576525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92930669014037650811717683 139396003521056476217576525)
      ·
        refine ⟨52273501320396178581591197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139396003521056476217576525 52273501320396178581591197)
        ·
          refine ⟨19602562995148566968096699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52273501320396178581591197 19602562995148566968096699)
          ·
            refine ⟨29403844492722850452145049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19602562995148566968096699 29403844492722850452145049)
            ·
              refine ⟨22052883369542137839108787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29403844492722850452145049 22052883369542137839108787)
              ·
                refine ⟨33079325054313206758663181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22052883369542137839108787 33079325054313206758663181)
                ·
                  refine ⟨12404746895367452534498693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33079325054313206758663181 12404746895367452534498693)
                  ·
                    refine ⟨2325890042881397350218505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12404746895367452534498693 2325890042881397350218505)
                    ·
                      refine ⟨1744417532161048012663879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325890042881397350218505 1744417532161048012663879)
                      ·
                        rfl

theorem cell23_3397241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_3397241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397241 prefixEnd_3397241 := by exact prefixLift 3397241
  have htrace : WordTrace (prefixWord ++ tailWord_3397241) baseStart_3397241 baseEnd_3397241 := by
    simpa [prefixWord, tailWord_3397241, baseEnd_3397241] using wordTrace_append hprefix tailTrace_3397241
  have hstable : (prefixWord ++ tailWord_3397241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397241).length < 2 ^ (prefixWord ++ tailWord_3397241).sum := by decide
  have hdescent : baseEnd_3397241 < baseStart_3397241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397244 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_3397244 : Nat := 118140960795 + 3397244 * 2 ^ 59
def prefixEnd_3397244 : Nat := 4983230072969 + 3 ^ 40 * 3397244 * 2
def baseEnd_3397244 : Nat := 1744419072603011500926365

theorem tailTrace_3397244 : CollatzResearch.WordTrace tailWord_3397244 prefixEnd_3397244 1744419072603011500926365 := by
  unfold tailWord_3397244
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953834052186332963991393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82605112069581777285321857 61953834052186332963991393)
  ·
    refine ⟨46465375539139749722993545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61953834052186332963991393 46465375539139749722993545)
    ·
      refine ⟨34849031654354812292245159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46465375539139749722993545 34849031654354812292245159)
      ·
        refine ⟨52273547481532218438367739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34849031654354812292245159 52273547481532218438367739)
        ·
          refine ⟨78410321222298327657551609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52273547481532218438367739 78410321222298327657551609)
          ·
            refine ⟨58807740916723745743163707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78410321222298327657551609 58807740916723745743163707)
            ·
              refine ⟨88211611375085618614745561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58807740916723745743163707 88211611375085618614745561)
              ·
                refine ⟨66158708531314213961059171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88211611375085618614745561 66158708531314213961059171)
                ·
                  refine ⟨99238062796971320941588757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66158708531314213961059171 99238062796971320941588757)
                  ·
                    refine ⟨4651784193608030669136973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99238062796971320941588757 4651784193608030669136973)
                    ·
                      refine ⟨1744419072603011500926365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651784193608030669136973 1744419072603011500926365)
                      ·
                        rfl

theorem cell23_3397244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_3397244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397244 prefixEnd_3397244 := by exact prefixLift 3397244
  have htrace : WordTrace (prefixWord ++ tailWord_3397244) baseStart_3397244 baseEnd_3397244 := by
    simpa [prefixWord, tailWord_3397244, baseEnd_3397244] using wordTrace_append hprefix tailTrace_3397244
  have hstable : (prefixWord ++ tailWord_3397244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397244).length < 2 ^ (prefixWord ++ tailWord_3397244).sum := by decide
  have hdescent : baseEnd_3397244 < baseStart_3397244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397279 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3397279 : Nat := 118140960795 + 3397279 * 2 ^ 59
def prefixEnd_3397279 : Nat := 4983230072969 + 3 ^ 40 * 3397279 * 2
def baseEnd_3397279 : Nat := 1744437044425918863988705

theorem tailTrace_3397279 : CollatzResearch.WordTrace tailWord_3397279 prefixEnd_3397279 1744437044425918863988705 := by
  unfold tailWord_3397279
  simp only [CollatzResearch.WordTrace]
  refine ⟨123908944659245866905506891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82605963106163911270337927 123908944659245866905506891)
  ·
    refine ⟨185863416988868800358260337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123908944659245866905506891 185863416988868800358260337)
    ·
      refine ⟨139397562741651600268695253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185863416988868800358260337 139397562741651600268695253)
      ·
        refine ⟨3267130376757459381297545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 139397562741651600268695253 3267130376757459381297545)
        ·
          refine ⟨2450347782568094535973159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267130376757459381297545 2450347782568094535973159)
          ·
            refine ⟨3675521673852141803959739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450347782568094535973159 3675521673852141803959739)
            ·
              refine ⟨5513282510778212705939609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675521673852141803959739 5513282510778212705939609)
              ·
                refine ⟨4134961883083659529454707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513282510778212705939609 4134961883083659529454707)
                ·
                  refine ⟨6202442824625489294182061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134961883083659529454707 6202442824625489294182061)
                  ·
                    refine ⟨2325916059234558485318273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6202442824625489294182061 2325916059234558485318273)
                    ·
                      refine ⟨1744437044425918863988705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2325916059234558485318273 1744437044425918863988705)
                      ·
                        rfl

theorem cell23_3397279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3397279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397279 prefixEnd_3397279 := by exact prefixLift 3397279
  have htrace : WordTrace (prefixWord ++ tailWord_3397279) baseStart_3397279 baseEnd_3397279 := by
    simpa [prefixWord, tailWord_3397279, baseEnd_3397279] using wordTrace_append hprefix tailTrace_3397279
  have hstable : (prefixWord ++ tailWord_3397279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397279).length < 2 ^ (prefixWord ++ tailWord_3397279).sum := by decide
  have hdescent : baseEnd_3397279 < baseStart_3397279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397325 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3397325 : Nat := 118140960795 + 3397325 * 2 ^ 59
def prefixEnd_3397325 : Nat := 4983230072969 + 3 ^ 40 * 3397325 * 2
def baseEnd_3397325 : Nat := 1744460664536025684013493

theorem tailTrace_3397325 : CollatzResearch.WordTrace tailWord_3397325 prefixEnd_3397325 1744460664536025684013493 := by
  unfold tailWord_3397325
  simp only [CollatzResearch.WordTrace]
  refine ⟨123910622417079216761681429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82607081611386144507787619 123910622417079216761681429)
  ·
    refine ⟨5808310425800588285703817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123910622417079216761681429 5808310425800588285703817)
    ·
      refine ⟨4356232819350441214277863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808310425800588285703817 4356232819350441214277863)
      ·
        refine ⟨6534349229025661821416795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356232819350441214277863 6534349229025661821416795)
        ·
          refine ⟨9801523843538492732125193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534349229025661821416795 9801523843538492732125193)
          ·
            refine ⟨7351142882653869549093895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9801523843538492732125193 7351142882653869549093895)
            ·
              refine ⟨11026714323980804323640843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351142882653869549093895 11026714323980804323640843)
              ·
                refine ⟨16540071485971206485461265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026714323980804323640843 16540071485971206485461265)
                ·
                  refine ⟨12405053614478404864095949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16540071485971206485461265 12405053614478404864095949)
                  ·
                    refine ⟨4651895105429401824035981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12405053614478404864095949 4651895105429401824035981)
                    ·
                      refine ⟨1744460664536025684013493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4651895105429401824035981 1744460664536025684013493)
                      ·
                        rfl

theorem cell23_3397325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3397325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397325 prefixEnd_3397325 := by exact prefixLift 3397325
  have htrace : WordTrace (prefixWord ++ tailWord_3397325) baseStart_3397325 baseEnd_3397325 := by
    simpa [prefixWord, tailWord_3397325, baseEnd_3397325] using wordTrace_append hprefix tailTrace_3397325
  have hstable : (prefixWord ++ tailWord_3397325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397325).length < 2 ^ (prefixWord ++ tailWord_3397325).sum := by decide
  have hdescent : baseEnd_3397325 < baseStart_3397325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397345 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 2, 5]
def baseStart_3397345 : Nat := 118140960795 + 3397345 * 2 ^ 59
def prefixEnd_3397345 : Nat := 4983230072969 + 3 ^ 40 * 3397345 * 2
def baseEnd_3397345 : Nat := 581490311383038535254467

theorem tailTrace_3397345 : CollatzResearch.WordTrace tailWord_3397345 prefixEnd_3397345 581490311383038535254467 := by
  unfold tailWord_3397345
  simp only [CollatzResearch.WordTrace]
  refine ⟨123911351877006760177409489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82607567918004506784939659 123911351877006760177409489)
  ·
    refine ⟨92933513907755070133057117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123911351877006760177409489 92933513907755070133057117)
    ·
      refine ⟨34850067715408151299896419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92933513907755070133057117 34850067715408151299896419)
      ·
        refine ⟨52275101573112226949844629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34850067715408151299896419 52275101573112226949844629)
        ·
          refine ⟨2450395386239635638273967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52275101573112226949844629 2450395386239635638273967)
          ·
            refine ⟨3675593079359453457410951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450395386239635638273967 3675593079359453457410951)
            ·
              refine ⟨5513389619039180186116427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675593079359453457410951 5513389619039180186116427)
              ·
                refine ⟨8270084428558770279174641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513389619039180186116427 8270084428558770279174641)
                ·
                  refine ⟨6202563321419077709380981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270084428558770279174641 6202563321419077709380981)
                  ·
                    refine ⟨581490311383038535254467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6202563321419077709380981 581490311383038535254467)
                    ·
                      rfl

theorem cell23_3397345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_3397345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397345 prefixEnd_3397345 := by exact prefixLift 3397345
  have htrace : WordTrace (prefixWord ++ tailWord_3397345) baseStart_3397345 baseEnd_3397345 := by
    simpa [prefixWord, tailWord_3397345, baseEnd_3397345] using wordTrace_append hprefix tailTrace_3397345
  have hstable : (prefixWord ++ tailWord_3397345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397345).length < 2 ^ (prefixWord ++ tailWord_3397345).sum := by decide
  have hdescent : baseEnd_3397345 < baseStart_3397345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397408 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3397408 : Nat := 118140960795 + 3397408 * 2 ^ 59
def prefixEnd_3397408 : Nat := 4983230072969 + 3 ^ 40 * 3397408 * 2
def baseEnd_3397408 : Nat := 1744503283430348859275611

theorem tailTrace_3397408 : CollatzResearch.WordTrace tailWord_3397408 prefixEnd_3397408 1744503283430348859275611 := by
  unfold tailWord_3397408
  simp only [CollatzResearch.WordTrace]
  refine ⟨61956824837889260968476439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82609099783852347957968585 61956824837889260968476439)
  ·
    refine ⟨92935237256833891452714659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61956824837889260968476439 92935237256833891452714659)
    ·
      refine ⟨139402855885250837179071989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92935237256833891452714659 139402855885250837179071989)
      ·
        refine ⟨13069017739242265985537999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139402855885250837179071989 13069017739242265985537999)
        ·
          refine ⟨19603526608863398978306999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069017739242265985537999 19603526608863398978306999)
          ·
            refine ⟨29405289913295098467460499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19603526608863398978306999 29405289913295098467460499)
            ·
              refine ⟨44107934869942647701190749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29405289913295098467460499 44107934869942647701190749)
              ·
                refine ⟨16540475576228492887946531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44107934869942647701190749 16540475576228492887946531)
                ·
                  refine ⟨24810713364342739331919797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16540475576228492887946531 24810713364342739331919797)
                  ·
                    refine ⟨2326004377907131812367481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24810713364342739331919797 2326004377907131812367481)
                    ·
                      refine ⟨1744503283430348859275611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326004377907131812367481 1744503283430348859275611)
                      ·
                        rfl

theorem cell23_3397408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3397408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397408 prefixEnd_3397408 := by exact prefixLift 3397408
  have htrace : WordTrace (prefixWord ++ tailWord_3397408) baseStart_3397408 baseEnd_3397408 := by
    simpa [prefixWord, tailWord_3397408, baseEnd_3397408] using wordTrace_append hprefix tailTrace_3397408
  have hstable : (prefixWord ++ tailWord_3397408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397408).length < 2 ^ (prefixWord ++ tailWord_3397408).sum := by decide
  have hdescent : baseEnd_3397408 < baseStart_3397408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397425 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_3397425 : Nat := 118140960795 + 3397425 * 2 ^ 59
def prefixEnd_3397425 : Nat := 4983230072969 + 3 ^ 40 * 3397425 * 2
def baseEnd_3397425 : Nat := 1744512012601475292763033

theorem tailTrace_3397425 : CollatzResearch.WordTrace tailWord_3397425 prefixEnd_3397425 1744512012601475292763033 := by
  unfold tailWord_3397425
  simp only [CollatzResearch.WordTrace]
  refine ⟨123914269716716933840321729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82609513144477955893547819 123914269716716933840321729)
  ·
    refine ⟨92935702287537700380241297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123914269716716933840321729 92935702287537700380241297)
    ·
      refine ⟨69701776715653275285180973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92935702287537700380241297 69701776715653275285180973)
      ·
        refine ⟨26138166268369978231942865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69701776715653275285180973 26138166268369978231942865)
        ·
          refine ⟨19603624701277483673957149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26138166268369978231942865 19603624701277483673957149)
          ·
            refine ⟨7351359262979056377733931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19603624701277483673957149 7351359262979056377733931)
            ·
              refine ⟨11027038894468584566600897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351359262979056377733931 11027038894468584566600897)
              ·
                refine ⟨8270279170851438424950673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11027038894468584566600897 8270279170851438424950673)
                ·
                  refine ⟨6202709378138578818713005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270279170851438424950673 6202709378138578818713005)
                  ·
                    refine ⟨2326016016801967057017377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6202709378138578818713005 2326016016801967057017377)
                    ·
                      refine ⟨1744512012601475292763033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326016016801967057017377 1744512012601475292763033)
                      ·
                        rfl

theorem cell23_3397425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_3397425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397425 prefixEnd_3397425 := by exact prefixLift 3397425
  have htrace : WordTrace (prefixWord ++ tailWord_3397425) baseStart_3397425 baseEnd_3397425 := by
    simpa [prefixWord, tailWord_3397425, baseEnd_3397425] using wordTrace_append hprefix tailTrace_3397425
  have hstable : (prefixWord ++ tailWord_3397425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397425).length < 2 ^ (prefixWord ++ tailWord_3397425).sum := by decide
  have hdescent : baseEnd_3397425 < baseStart_3397425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397452 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_3397452 : Nat := 118140960795 + 3397452 * 2 ^ 59
def prefixEnd_3397452 : Nat := 4983230072969 + 3 ^ 40 * 3397452 * 2
def baseEnd_3397452 : Nat := 581508625526382229041803

theorem tailTrace_3397452 : CollatzResearch.WordTrace tailWord_3397452 prefixEnd_3397452 581508625526382229041803 := by
  unfold tailWord_3397452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61957627243809558725777305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82610169658412744967703073 61957627243809558725777305)
  ·
    refine ⟨46468220432857169044332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61957627243809558725777305 46468220432857169044332979)
    ·
      refine ⟨69702330649285753566499469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46468220432857169044332979 69702330649285753566499469)
      ·
        refine ⟨26138373993482157587437301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69702330649285753566499469 26138373993482157587437301)
        ·
          refine ⟨2450472561888952273822247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26138373993482157587437301 2450472561888952273822247)
          ·
            refine ⟨3675708842833428410733371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450472561888952273822247 3675708842833428410733371)
            ·
              refine ⟨5513563264250142616100057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675708842833428410733371 5513563264250142616100057)
              ·
                refine ⟨4135172448187606962075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513563264250142616100057 4135172448187606962075043)
                ·
                  refine ⟨6202758672281410443112565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135172448187606962075043 6202758672281410443112565)
                  ·
                    refine ⟨581508625526382229041803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6202758672281410443112565 581508625526382229041803)
                    ·
                      rfl

theorem cell23_3397452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_3397452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397452 prefixEnd_3397452 := by exact prefixLift 3397452
  have htrace : WordTrace (prefixWord ++ tailWord_3397452) baseStart_3397452 baseEnd_3397452 := by
    simpa [prefixWord, tailWord_3397452, baseEnd_3397452] using wordTrace_append hprefix tailTrace_3397452
  have hstable : (prefixWord ++ tailWord_3397452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397452).length < 2 ^ (prefixWord ++ tailWord_3397452).sum := by decide
  have hdescent : baseEnd_3397452 < baseStart_3397452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397461 : List Nat := [1, 3, 2, 2, 2, 2, 2, 9]
def baseStart_3397461 : Nat := 118140960795 + 3397461 * 2 ^ 59
def prefixEnd_3397461 : Nat := 4983230072969 + 3 ^ 40 * 3397461 * 2
def baseEnd_3397461 : Nat := 64612240663149524144921

theorem tailTrace_3397461 : CollatzResearch.WordTrace tailWord_3397461 prefixEnd_3397461 64612240663149524144921 := by
  unfold tailWord_3397461
  simp only [CollatzResearch.WordTrace]
  refine ⟨123915582744586511988632237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82610388496391007992421491 123915582744586511988632237)
  ·
    refine ⟨46468343529219941995737089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123915582744586511988632237 46468343529219941995737089)
    ·
      refine ⟨34851257646914956496802817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46468343529219941995737089 34851257646914956496802817)
      ·
        refine ⟨26138443235186217372602113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34851257646914956496802817 26138443235186217372602113)
        ·
          refine ⟨19603832426389663029451585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26138443235186217372602113 19603832426389663029451585)
          ·
            refine ⟨14702874319792247272088689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19603832426389663029451585 14702874319792247272088689)
            ·
              refine ⟨11027155739844185454066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14702874319792247272088689 11027155739844185454066517)
              ·
                refine ⟨64612240663149524144921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11027155739844185454066517 64612240663149524144921)
                ·
                  rfl

theorem cell23_3397461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 9].length) (baseStart_3397461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397461 prefixEnd_3397461 := by exact prefixLift 3397461
  have htrace : WordTrace (prefixWord ++ tailWord_3397461) baseStart_3397461 baseEnd_3397461 := by
    simpa [prefixWord, tailWord_3397461, baseEnd_3397461] using wordTrace_append hprefix tailTrace_3397461
  have hstable : (prefixWord ++ tailWord_3397461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397461).length < 2 ^ (prefixWord ++ tailWord_3397461).sum := by decide
  have hdescent : baseEnd_3397461 < baseStart_3397461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397475 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 5]
def baseStart_3397475 : Nat := 118140960795 + 3397475 * 2 ^ 59
def prefixEnd_3397475 : Nat := 4983230072969 + 3 ^ 40 * 3397475 * 2
def baseEnd_3397475 : Nat := 1744537686634200097137803

theorem tailTrace_3397475 : CollatzResearch.WordTrace tailWord_3397475 prefixEnd_3397475 1744537686634200097137803 := by
  unfold tailWord_3397475
  simp only [CollatzResearch.WordTrace]
  refine ⟨123916093366535792379641879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82610728911023861586427919 123916093366535792379641879)
  ·
    refine ⟨185874140049803688569462819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123916093366535792379641879 185874140049803688569462819)
    ·
      refine ⟨278811210074705532854194229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185874140049803688569462819 278811210074705532854194229)
      ·
        refine ⟨26138550944503643705080709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278811210074705532854194229 26138550944503643705080709)
        ·
          refine ⟨4900978302094433194702633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26138550944503643705080709 4900978302094433194702633)
          ·
            refine ⟨3675733726570824896026975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900978302094433194702633 3675733726570824896026975)
            ·
              refine ⟨5513600589856237344040463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675733726570824896026975 5513600589856237344040463)
              ·
                refine ⟨8270400884784356016060695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513600589856237344040463 8270400884784356016060695)
                ·
                  refine ⟨12405601327176534024091043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270400884784356016060695 12405601327176534024091043)
                  ·
                    refine ⟨18608401990764801036136565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12405601327176534024091043 18608401990764801036136565)
                    ·
                      refine ⟨1744537686634200097137803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18608401990764801036136565 1744537686634200097137803)
                      ·
                        rfl

theorem cell23_3397475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_3397475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397475 prefixEnd_3397475 := by exact prefixLift 3397475
  have htrace : WordTrace (prefixWord ++ tailWord_3397475) baseStart_3397475 baseEnd_3397475 := by
    simpa [prefixWord, tailWord_3397475, baseEnd_3397475] using wordTrace_append hprefix tailTrace_3397475
  have hstable : (prefixWord ++ tailWord_3397475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397475).length < 2 ^ (prefixWord ++ tailWord_3397475).sum := by decide
  have hdescent : baseEnd_3397475 < baseStart_3397475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397501 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3397501 : Nat := 118140960795 + 3397501 * 2 ^ 59
def prefixEnd_3397501 : Nat := 4983230072969 + 3 ^ 40 * 3397501 * 2
def baseEnd_3397501 : Nat := 1744551037131216995412683

theorem tailTrace_3397501 : CollatzResearch.WordTrace tailWord_3397501 prefixEnd_3397501 1744551037131216995412683 := by
  unfold tailWord_3397501
  simp only [CollatzResearch.WordTrace]
  refine ⟨123917041664441598820088357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82611361109627732546725571 123917041664441598820088357)
  ·
    refine ⟨23234445312082799778766567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123917041664441598820088357 23234445312082799778766567)
    ·
      refine ⟨34851667968124199668149851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234445312082799778766567 34851667968124199668149851)
      ·
        refine ⟨52277501952186299502224777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34851667968124199668149851 52277501952186299502224777)
        ·
          refine ⟨39208126464139724626668583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52277501952186299502224777 39208126464139724626668583)
          ·
            refine ⟨58812189696209586940002875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39208126464139724626668583 58812189696209586940002875)
            ·
              refine ⟨88218284544314380410004313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58812189696209586940002875 88218284544314380410004313)
              ·
                refine ⟨66163713408235785307503235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88218284544314380410004313 66163713408235785307503235)
                ·
                  refine ⟨99245570112353677961254853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66163713408235785307503235 99245570112353677961254853)
                  ·
                    refine ⟨18608544396066314617735285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99245570112353677961254853 18608544396066314617735285)
                    ·
                      refine ⟨1744551037131216995412683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18608544396066314617735285 1744551037131216995412683)
                      ·
                        rfl

theorem cell23_3397501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3397501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397501 prefixEnd_3397501 := by exact prefixLift 3397501
  have htrace : WordTrace (prefixWord ++ tailWord_3397501) baseStart_3397501 baseEnd_3397501 := by
    simpa [prefixWord, tailWord_3397501, baseEnd_3397501] using wordTrace_append hprefix tailTrace_3397501
  have hstable : (prefixWord ++ tailWord_3397501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397501).length < 2 ^ (prefixWord ++ tailWord_3397501).sum := by decide
  have hdescent : baseEnd_3397501 < baseStart_3397501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397502 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3397502 : Nat := 118140960795 + 3397502 * 2 ^ 59
def prefixEnd_3397502 : Nat := 4983230072969 + 3 ^ 40 * 3397502 * 2
def baseEnd_3397502 : Nat := 1744551550611871491500179

theorem tailTrace_3397502 : CollatzResearch.WordTrace tailWord_3397502 prefixEnd_3397502 1744551550611871491500179 := by
  unfold tailWord_3397502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489634767179746998859345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82611385424958650660583173 15489634767179746998859345)
  ·
    refine ⟨11617226075384810249144509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15489634767179746998859345 11617226075384810249144509)
    ·
      refine ⟨4356459778269303843429191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11617226075384810249144509 4356459778269303843429191)
      ·
        refine ⟨6534689667403955765143787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356459778269303843429191 6534689667403955765143787)
        ·
          refine ⟨9802034501105933647715681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534689667403955765143787 9802034501105933647715681)
          ·
            refine ⟨7351525875829450235786761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9802034501105933647715681 7351525875829450235786761)
            ·
              refine ⟨5513644406872087676840071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351525875829450235786761 5513644406872087676840071)
              ·
                refine ⟨8270466610308131515260107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513644406872087676840071 8270466610308131515260107)
                ·
                  refine ⟨12405699915462197272890161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270466610308131515260107 12405699915462197272890161)
                  ·
                    refine ⟨9304274936596647954667621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12405699915462197272890161 9304274936596647954667621)
                    ·
                      refine ⟨1744551550611871491500179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9304274936596647954667621 1744551550611871491500179)
                      ·
                        rfl

theorem cell23_3397502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3397502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397502 prefixEnd_3397502 := by exact prefixLift 3397502
  have htrace : WordTrace (prefixWord ++ tailWord_3397502) baseStart_3397502 baseEnd_3397502 := by
    simpa [prefixWord, tailWord_3397502, baseEnd_3397502] using wordTrace_append hprefix tailTrace_3397502
  have hstable : (prefixWord ++ tailWord_3397502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397502).length < 2 ^ (prefixWord ++ tailWord_3397502).sum := by decide
  have hdescent : baseEnd_3397502 < baseStart_3397502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397515 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 1, 3, 2]
def baseStart_3397515 : Nat := 118140960795 + 3397515 * 2 ^ 59
def prefixEnd_3397515 : Nat := 4983230072969 + 3 ^ 40 * 3397515 * 2
def baseEnd_3397515 : Nat := 1744558225860379940637619

theorem tailTrace_3397515 : CollatzResearch.WordTrace tailWord_3397515 prefixEnd_3397515 1744558225860379940637619 := by
  unfold tailWord_3397515
  simp only [CollatzResearch.WordTrace]
  refine ⟨123917552286390879211097999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82611701524260586140731999 123917552286390879211097999)
  ·
    refine ⟨185876328429586318816646999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123917552286390879211097999 185876328429586318816646999)
    ·
      refine ⟨278814492644379478224970499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185876328429586318816646999 278814492644379478224970499)
      ·
        refine ⟨418221738966569217337455749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278814492644379478224970499 418221738966569217337455749)
        ·
          refine ⟨78416576056231728250772953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418221738966569217337455749 78416576056231728250772953)
          ·
            refine ⟨58812432042173796188079715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78416576056231728250772953 58812432042173796188079715)
            ·
              refine ⟨88218648063260694282119573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58812432042173796188079715 88218648063260694282119573)
              ·
                refine ⟨4135249127965345044474355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88218648063260694282119573 4135249127965345044474355)
                ·
                  refine ⟨6202873691948017566711533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135249127965345044474355 6202873691948017566711533)
                  ·
                    refine ⟨2326077634480506587516825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6202873691948017566711533 2326077634480506587516825)
                    ·
                      refine ⟨1744558225860379940637619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326077634480506587516825 1744558225860379940637619)
                      ·
                        rfl

theorem cell23_3397515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3, 2].length) (baseStart_3397515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397515 prefixEnd_3397515 := by exact prefixLift 3397515
  have htrace : WordTrace (prefixWord ++ tailWord_3397515) baseStart_3397515 baseEnd_3397515 := by
    simpa [prefixWord, tailWord_3397515, baseEnd_3397515] using wordTrace_append hprefix tailTrace_3397515
  have hstable : (prefixWord ++ tailWord_3397515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397515).length < 2 ^ (prefixWord ++ tailWord_3397515).sum := by decide
  have hdescent : baseEnd_3397515 < baseStart_3397515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397526 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3397526 : Nat := 118140960795 + 3397526 * 2 ^ 59
def prefixEnd_3397526 : Nat := 4983230072969 + 3 ^ 40 * 3397526 * 2
def baseEnd_3397526 : Nat := 1744563874147579397600069

theorem tailTrace_3397526 : CollatzResearch.WordTrace tailWord_3397526 prefixEnd_3397526 1744563874147579397600069 := by
  unfold tailWord_3397526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744872093084439255609277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82611968992900685393165621 7744872093084439255609277)
  ·
    refine ⟨2904327034906664720853479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7744872093084439255609277 2904327034906664720853479)
    ·
      refine ⟨4356490552359997081280219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904327034906664720853479 4356490552359997081280219)
      ·
        refine ⟨6534735828539995621920329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356490552359997081280219 6534735828539995621920329)
        ·
          refine ⟨4901051871404996716440247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6534735828539995621920329 4901051871404996716440247)
          ·
            refine ⟨7351577807107495074660371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901051871404996716440247 7351577807107495074660371)
            ·
              refine ⟨11027366710661242611990557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351577807107495074660371 11027366710661242611990557)
              ·
                refine ⟨4135262516497965979496459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11027366710661242611990557 4135262516497965979496459)
                ·
                  refine ⟨6202893774746948969244689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135262516497965979496459 6202893774746948969244689)
                  ·
                    refine ⟨4652170331060211726933517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6202893774746948969244689 4652170331060211726933517)
                    ·
                      refine ⟨1744563874147579397600069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652170331060211726933517 1744563874147579397600069)
                      ·
                        rfl

theorem cell23_3397526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3397526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397526 prefixEnd_3397526 := by exact prefixLift 3397526
  have htrace : WordTrace (prefixWord ++ tailWord_3397526) baseStart_3397526 baseEnd_3397526 := by
    simpa [prefixWord, tailWord_3397526, baseEnd_3397526] using wordTrace_append hprefix tailTrace_3397526
  have hstable : (prefixWord ++ tailWord_3397526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397526).length < 2 ^ (prefixWord ++ tailWord_3397526).sum := by decide
  have hdescent : baseEnd_3397526 < baseStart_3397526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397556 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3397556 : Nat := 118140960795 + 3397556 * 2 ^ 59
def prefixEnd_3397556 : Nat := 4983230072969 + 3 ^ 40 * 3397556 * 2
def baseEnd_3397556 : Nat := 1744579278567214280224931

theorem tailTrace_3397556 : CollatzResearch.WordTrace tailWord_3397556 prefixEnd_3397556 1744579278567214280224931 := by
  unfold tailWord_3397556
  simp only [CollatzResearch.WordTrace]
  refine ⟨61959523839621171606670261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82612698452828228808893681 61959523839621171606670261)
  ·
    refine ⟨5808705359964484838125337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61959523839621171606670261 5808705359964484838125337)
    ·
      refine ⟨4356529019973363628594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808705359964484838125337 4356529019973363628594003)
      ·
        refine ⟨6534793529960045442891005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356529019973363628594003 6534793529960045442891005)
        ·
          refine ⟨2450547573735017041084127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6534793529960045442891005 2450547573735017041084127)
          ·
            refine ⟨3675821360602525561626191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450547573735017041084127 3675821360602525561626191)
            ·
              refine ⟨5513732040903788342439287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675821360602525561626191 5513732040903788342439287)
              ·
                refine ⟨8270598061355682513658931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513732040903788342439287 8270598061355682513658931)
                ·
                  refine ⟨12405897092033523770488397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270598061355682513658931 12405897092033523770488397)
                  ·
                    refine ⟨4652211409512571413933149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12405897092033523770488397 4652211409512571413933149)
                    ·
                      refine ⟨1744579278567214280224931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652211409512571413933149 1744579278567214280224931)
                      ·
                        rfl

theorem cell23_3397556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3397556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397556 prefixEnd_3397556 := by exact prefixLift 3397556
  have htrace : WordTrace (prefixWord ++ tailWord_3397556) baseStart_3397556 baseEnd_3397556 := by
    simpa [prefixWord, tailWord_3397556, baseEnd_3397556] using wordTrace_append hprefix tailTrace_3397556
  have hstable : (prefixWord ++ tailWord_3397556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397556).length < 2 ^ (prefixWord ++ tailWord_3397556).sum := by decide
  have hdescent : baseEnd_3397556 < baseStart_3397556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397578 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_3397578 : Nat := 118140960795 + 3397578 * 2 ^ 59
def prefixEnd_3397578 : Nat := 4983230072969 + 3 ^ 40 * 3397578 * 2
def baseEnd_3397578 : Nat := 1744590575141613194149829

theorem tailTrace_3397578 : CollatzResearch.WordTrace tailWord_3397578 prefixEnd_3397578 1744590575141613194149829 := by
  unfold tailWord_3397578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979962521290660242660347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82613233390108427313760925 30979962521290660242660347)
  ·
    refine ⟨46469943781935990363990521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30979962521290660242660347 46469943781935990363990521)
    ·
      refine ⟨34852457836451992772992891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46469943781935990363990521 34852457836451992772992891)
      ·
        refine ⟨52278686754677989159489337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34852457836451992772992891 52278686754677989159489337)
        ·
          refine ⟨39209015066008491869617003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52278686754677989159489337 39209015066008491869617003)
          ·
            refine ⟨58813522599012737804425505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39209015066008491869617003 58813522599012737804425505)
            ·
              refine ⟨44110141949259553353319129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58813522599012737804425505 44110141949259553353319129)
              ·
                refine ⟨33082606461944665014989347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44110141949259553353319129 33082606461944665014989347)
                ·
                  refine ⟨49623909692916997522484021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33082606461944665014989347 49623909692916997522484021)
                  ·
                    refine ⟨4652241533710968517732877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49623909692916997522484021 4652241533710968517732877)
                    ·
                      refine ⟨1744590575141613194149829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652241533710968517732877 1744590575141613194149829)
                      ·
                        rfl

theorem cell23_3397578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_3397578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397578 prefixEnd_3397578 := by exact prefixLift 3397578
  have htrace : WordTrace (prefixWord ++ tailWord_3397578) baseStart_3397578 baseEnd_3397578 := by
    simpa [prefixWord, tailWord_3397578, baseEnd_3397578] using wordTrace_append hprefix tailTrace_3397578
  have hstable : (prefixWord ++ tailWord_3397578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397578).length < 2 ^ (prefixWord ++ tailWord_3397578).sum := by decide
  have hdescent : baseEnd_3397578 < baseStart_3397578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397689 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3397689 : Nat := 118140960795 + 3397689 * 2 ^ 59
def prefixEnd_3397689 : Nat := 4983230072969 + 3 ^ 40 * 3397689 * 2
def baseEnd_3397689 : Nat := 1744647571494262259861819

theorem tailTrace_3397689 : CollatzResearch.WordTrace tailWord_3397689 prefixEnd_3397689 1744647571494262259861819 := by
  unfold tailWord_3397689
  simp only [CollatzResearch.WordTrace]
  refine ⟨123923898587760506927932121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82615932391840337951954747 123923898587760506927932121)
  ·
    refine ⟨92942923940820380195949091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123923898587760506927932121 92942923940820380195949091)
    ·
      refine ⟨139414385911230570293923637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92942923940820380195949091 139414385911230570293923637)
      ·
        refine ⟨13070098679177865965055341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139414385911230570293923637 13070098679177865965055341)
        ·
          refine ⟨4901287004691699736895753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13070098679177865965055341 4901287004691699736895753)
          ·
            refine ⟨3675965253518774802671815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901287004691699736895753 3675965253518774802671815)
            ·
              refine ⟨5513947880278162204007723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675965253518774802671815 5513947880278162204007723)
              ·
                refine ⟨8270921820417243306011585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513947880278162204007723 8270921820417243306011585)
                ·
                  refine ⟨6203191365312932479508689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270921820417243306011585 6203191365312932479508689)
                  ·
                    refine ⟨4652393523984699359631517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203191365312932479508689 4652393523984699359631517)
                    ·
                      refine ⟨1744647571494262259861819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652393523984699359631517 1744647571494262259861819)
                      ·
                        rfl

theorem cell23_3397689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3397689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397689 prefixEnd_3397689 := by exact prefixLift 3397689
  have htrace : WordTrace (prefixWord ++ tailWord_3397689) baseStart_3397689 baseEnd_3397689 := by
    simpa [prefixWord, tailWord_3397689, baseEnd_3397689] using wordTrace_append hprefix tailTrace_3397689
  have hstable : (prefixWord ++ tailWord_3397689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397689).length < 2 ^ (prefixWord ++ tailWord_3397689).sum := by decide
  have hdescent : baseEnd_3397689 < baseStart_3397689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397705 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_3397705 : Nat := 118140960795 + 3397705 * 2 ^ 59
def prefixEnd_3397705 : Nat := 4983230072969 + 3 ^ 40 * 3397705 * 2
def baseEnd_3397705 : Nat := 581551929061578065753915

theorem tailTrace_3397705 : CollatzResearch.WordTrace tailWord_3397705 prefixEnd_3397705 581551929061578065753915 := by
  unfold tailWord_3397705
  simp only [CollatzResearch.WordTrace]
  refine ⟨123924482155702541660514569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82616321437135027773676379 123924482155702541660514569)
  ·
    refine ⟨92943361616776906245385927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123924482155702541660514569 92943361616776906245385927)
    ·
      refine ⟨139415042425165359368078891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92943361616776906245385927 139415042425165359368078891)
      ·
        refine ⟨209122563637748039052118337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139415042425165359368078891 209122563637748039052118337)
        ·
          refine ⟨156841922728311029289088753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209122563637748039052118337 156841922728311029289088753)
          ·
            refine ⟨117631442046233271966816565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156841922728311029289088753 117631442046233271966816565)
            ·
              refine ⟨11027947691834369246889053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117631442046233271966816565 11027947691834369246889053)
              ·
                refine ⟨4135480384437888467583395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11027947691834369246889053 4135480384437888467583395)
                ·
                  refine ⟨6203220576656832701375093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135480384437888467583395 6203220576656832701375093)
                  ·
                    refine ⟨581551929061578065753915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6203220576656832701375093 581551929061578065753915)
                    ·
                      rfl

theorem cell23_3397705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_3397705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397705 prefixEnd_3397705 := by exact prefixLift 3397705
  have htrace : WordTrace (prefixWord ++ tailWord_3397705) baseStart_3397705 baseEnd_3397705 := by
    simpa [prefixWord, tailWord_3397705, baseEnd_3397705] using wordTrace_append hprefix tailTrace_3397705
  have hstable : (prefixWord ++ tailWord_3397705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397705).length < 2 ^ (prefixWord ++ tailWord_3397705).sum := by decide
  have hdescent : baseEnd_3397705 < baseStart_3397705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397719 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 1, 1, 3]
def baseStart_3397719 : Nat := 118140960795 + 3397719 * 2 ^ 59
def prefixEnd_3397719 : Nat := 4983230072969 + 3 ^ 40 * 3397719 * 2
def baseEnd_3397719 : Nat := 1744662975913897142486681

theorem tailTrace_3397719 : CollatzResearch.WordTrace tailWord_3397719 prefixEnd_3397719 1744662975913897142486681 := by
  unfold tailWord_3397719
  simp only [CollatzResearch.WordTrace]
  refine ⟨123924992777651822051524211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82616661851767881367682807 123924992777651822051524211)
  ·
    refine ⟨185887489166477733077286317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123924992777651822051524211 185887489166477733077286317)
    ·
      refine ⟨69707808437429149903982369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185887489166477733077286317 69707808437429149903982369)
      ·
        refine ⟨52280856328071862427986777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69707808437429149903982369 52280856328071862427986777)
        ·
          refine ⟨39210642246053896820990083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52280856328071862427986777 39210642246053896820990083)
          ·
            refine ⟨58815963369080845231485125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39210642246053896820990083 58815963369080845231485125)
            ·
              refine ⟨11027993131702658480903461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58815963369080845231485125 11027993131702658480903461)
              ·
                refine ⟨2067748712194248465169399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11027993131702658480903461 2067748712194248465169399)
                ·
                  refine ⟨3101623068291372697754099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067748712194248465169399 3101623068291372697754099)
                  ·
                    refine ⟨4652434602437059046631149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3101623068291372697754099 4652434602437059046631149)
                    ·
                      refine ⟨1744662975913897142486681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652434602437059046631149 1744662975913897142486681)
                      ·
                        rfl

theorem cell23_3397719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_3397719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397719 prefixEnd_3397719 := by exact prefixLift 3397719
  have htrace : WordTrace (prefixWord ++ tailWord_3397719) baseStart_3397719 baseEnd_3397719 := by
    simpa [prefixWord, tailWord_3397719, baseEnd_3397719] using wordTrace_append hprefix tailTrace_3397719
  have hstable : (prefixWord ++ tailWord_3397719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397719).length < 2 ^ (prefixWord ++ tailWord_3397719).sum := by decide
  have hdescent : baseEnd_3397719 < baseStart_3397719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397742 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3397742 : Nat := 118140960795 + 3397742 * 2 ^ 59
def prefixEnd_3397742 : Nat := 4983230072969 + 3 ^ 40 * 3397742 * 2
def baseEnd_3397742 : Nat := 1744674785968950552499075

theorem tailTrace_3397742 : CollatzResearch.WordTrace tailWord_3397742 prefixEnd_3397742 1744674785968950552499075 := by
  unfold tailWord_3397742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490728957071062122451435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82617221104378997986407653 15490728957071062122451435)
  ·
    refine ⟨23236093435606593183677153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15490728957071062122451435 23236093435606593183677153)
    ·
      refine ⟨17427070076704944887757865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23236093435606593183677153 17427070076704944887757865)
      ·
        refine ⟨13070302557528708665818399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17427070076704944887757865 13070302557528708665818399)
        ·
          refine ⟨19605453836293062998727599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13070302557528708665818399 19605453836293062998727599)
          ·
            refine ⟨29408180754439594498091399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19605453836293062998727599 29408180754439594498091399)
            ·
              refine ⟨44112271131659391747137099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29408180754439594498091399 44112271131659391747137099)
              ·
                refine ⟨66168406697489087620705649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44112271131659391747137099 66168406697489087620705649)
                ·
                  refine ⟨49626305023116815715529237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66168406697489087620705649 49626305023116815715529237)
                  ·
                    refine ⟨2326233047958600736665433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49626305023116815715529237 2326233047958600736665433)
                    ·
                      refine ⟨1744674785968950552499075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326233047958600736665433 1744674785968950552499075)
                      ·
                        rfl

theorem cell23_3397742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3397742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397742 prefixEnd_3397742 := by exact prefixLift 3397742
  have htrace : WordTrace (prefixWord ++ tailWord_3397742) baseStart_3397742 baseEnd_3397742 := by
    simpa [prefixWord, tailWord_3397742, baseEnd_3397742] using wordTrace_append hprefix tailTrace_3397742
  have hstable : (prefixWord ++ tailWord_3397742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397742).length < 2 ^ (prefixWord ++ tailWord_3397742).sum := by decide
  have hdescent : baseEnd_3397742 < baseStart_3397742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397765 : List Nat := [1, 3, 1, 1, 5, 3, 9]
def baseStart_3397765 : Nat := 118140960795 + 3397765 * 2 ^ 59
def prefixEnd_3397765 : Nat := 4983230072969 + 3 ^ 40 * 3397765 * 2
def baseEnd_3397765 : Nat := 21539340691654369907549

theorem tailTrace_3397765 : CollatzResearch.WordTrace tailWord_3397765 prefixEnd_3397765 21539340691654369907549 := by
  unfold tailWord_3397765
  simp only [CollatzResearch.WordTrace]
  refine ⟨123926670535485171907698749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82617780356990114605132499 123926670535485171907698749)
  ·
    refine ⟨46472501450806939465387031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123926670535485171907698749 46472501450806939465387031)
    ·
      refine ⟨69708752176210409198080547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46472501450806939465387031 69708752176210409198080547)
      ·
        refine ⟨104563128264315613797120821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69708752176210409198080547 104563128264315613797120821)
        ·
          refine ⟨9802793274779588793480077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104563128264315613797120821 9802793274779588793480077)
          ·
            refine ⟨3676047478042345797555029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9802793274779588793480077 3676047478042345797555029)
            ·
              refine ⟨21539340691654369907549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3676047478042345797555029 21539340691654369907549)
              ·
                rfl

theorem cell23_3397765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 9].length) (baseStart_3397765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397765 prefixEnd_3397765 := by exact prefixLift 3397765
  have htrace : WordTrace (prefixWord ++ tailWord_3397765) baseStart_3397765 baseEnd_3397765 := by
    simpa [prefixWord, tailWord_3397765, baseEnd_3397765] using wordTrace_append hprefix tailTrace_3397765
  have hstable : (prefixWord ++ tailWord_3397765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397765).length < 2 ^ (prefixWord ++ tailWord_3397765).sum := by decide
  have hdescent : baseEnd_3397765 < baseStart_3397765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397796 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_3397796 : Nat := 118140960795 + 3397796 * 2 ^ 59
def prefixEnd_3397796 : Nat := 4983230072969 + 3 ^ 40 * 3397796 * 2
def baseEnd_3397796 : Nat := 1744702513924293341223827

theorem tailTrace_3397796 : CollatzResearch.WordTrace tailWord_3397796 prefixEnd_3397796 1744702513924293341223827 := by
  unfold tailWord_3397796
  simp only [CollatzResearch.WordTrace]
  refine ⟨61963900599186432101038621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82618534132248576134718161 61963900599186432101038621)
  ·
    refine ⟨23236462724694912037889483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61963900599186432101038621 23236462724694912037889483)
    ·
      refine ⟨34854694087042368056834225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23236462724694912037889483 34854694087042368056834225)
      ·
        refine ⟨26141020565281776042625669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34854694087042368056834225 26141020565281776042625669)
        ·
          refine ⟨4901441355990333007992313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26141020565281776042625669 4901441355990333007992313)
          ·
            refine ⟨3676081016992749755994235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901441355990333007992313 3676081016992749755994235)
            ·
              refine ⟨5514121525489124633991353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676081016992749755994235 5514121525489124633991353)
              ·
                refine ⟨4135591144116843475493515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514121525489124633991353 4135591144116843475493515)
                ·
                  refine ⟨6203386716175265213240273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135591144116843475493515 6203386716175265213240273)
                  ·
                    refine ⟨4652540037131448909930205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203386716175265213240273 4652540037131448909930205)
                    ·
                      refine ⟨1744702513924293341223827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652540037131448909930205 1744702513924293341223827)
                      ·
                        rfl

theorem cell23_3397796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_3397796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397796 prefixEnd_3397796 := by exact prefixLift 3397796
  have htrace : WordTrace (prefixWord ++ tailWord_3397796) baseStart_3397796 baseEnd_3397796 := by
    simpa [prefixWord, tailWord_3397796, baseEnd_3397796] using wordTrace_append hprefix tailTrace_3397796
  have hstable : (prefixWord ++ tailWord_3397796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397796).length < 2 ^ (prefixWord ++ tailWord_3397796).sum := by decide
  have hdescent : baseEnd_3397796 < baseStart_3397796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397806 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3397806 : Nat := 118140960795 + 3397806 * 2 ^ 59
def prefixEnd_3397806 : Nat := 4983230072969 + 3 ^ 40 * 3397806 * 2
def baseEnd_3397806 : Nat := 1744707648730838302098781

theorem tailTrace_3397806 : CollatzResearch.WordTrace tailWord_3397806 prefixEnd_3397806 1744707648730838302098781 := by
  unfold tailWord_3397806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491020741042079488742659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82618777285557757273294181 15491020741042079488742659)
  ·
    refine ⟨23236531111563119233113989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15491020741042079488742659 23236531111563119233113989)
    ·
      refine ⟨4356849583418084856208873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23236531111563119233113989 4356849583418084856208873)
      ·
        refine ⟨3267637187563563642156655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4356849583418084856208873 3267637187563563642156655)
        ·
          refine ⟨4901455781345345463234983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267637187563563642156655 4901455781345345463234983)
          ·
            refine ⟨7352183672018018194852475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901455781345345463234983 7352183672018018194852475)
            ·
              refine ⟨11028275508027027292278713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352183672018018194852475 11028275508027027292278713)
              ·
                refine ⟨8271206631020270469209035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028275508027027292278713 8271206631020270469209035)
                ·
                  refine ⟨12406809946530405703813553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271206631020270469209035 12406809946530405703813553)
                  ·
                    refine ⟨9305107459897804277860165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12406809946530405703813553 9305107459897804277860165)
                    ·
                      refine ⟨1744707648730838302098781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9305107459897804277860165 1744707648730838302098781)
                      ·
                        rfl

theorem cell23_3397806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3397806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397806 prefixEnd_3397806 := by exact prefixLift 3397806
  have htrace : WordTrace (prefixWord ++ tailWord_3397806) baseStart_3397806 baseEnd_3397806 := by
    simpa [prefixWord, tailWord_3397806, baseEnd_3397806] using wordTrace_append hprefix tailTrace_3397806
  have hstable : (prefixWord ++ tailWord_3397806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397806).length < 2 ^ (prefixWord ++ tailWord_3397806).sum := by decide
  have hdescent : baseEnd_3397806 < baseStart_3397806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397809 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3397809 : Nat := 118140960795 + 3397809 * 2 ^ 59
def prefixEnd_3397809 : Nat := 4983230072969 + 3 ^ 40 * 3397809 * 2
def baseEnd_3397809 : Nat := 1744709189172801790361267

theorem tailTrace_3397809 : CollatzResearch.WordTrace tailWord_3397809 prefixEnd_3397809 1744709189172801790361267 := by
  unfold tailWord_3397809
  simp only [CollatzResearch.WordTrace]
  refine ⟨123928275347325767422300481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82618850231550511614866987 123928275347325767422300481)
  ·
    refine ⟨92946206510494325566725361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123928275347325767422300481 92946206510494325566725361)
    ·
      refine ⟨69709654882870744175044021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92946206510494325566725361 69709654882870744175044021)
      ·
        refine ⟨6535280145269132266410377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69709654882870744175044021 6535280145269132266410377)
        ·
          refine ⟨4901460108951849199807783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535280145269132266410377 4901460108951849199807783)
          ·
            refine ⟨7352190163427773799711675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901460108951849199807783 7352190163427773799711675)
            ·
              refine ⟨11028285245141660699567513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352190163427773799711675 11028285245141660699567513)
              ·
                refine ⟨8271213933856245524675635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028285245141660699567513 8271213933856245524675635)
                ·
                  refine ⟨12406820900784368287013453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271213933856245524675635 12406820900784368287013453)
                  ·
                    refine ⟨4652557837794138107630045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12406820900784368287013453 4652557837794138107630045)
                    ·
                      refine ⟨1744709189172801790361267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652557837794138107630045 1744709189172801790361267)
                      ·
                        rfl

theorem cell23_3397809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3397809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397809 prefixEnd_3397809 := by exact prefixLift 3397809
  have htrace : WordTrace (prefixWord ++ tailWord_3397809) baseStart_3397809 baseEnd_3397809 := by
    simpa [prefixWord, tailWord_3397809, baseEnd_3397809] using wordTrace_append hprefix tailTrace_3397809
  have hstable : (prefixWord ++ tailWord_3397809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397809).length < 2 ^ (prefixWord ++ tailWord_3397809).sum := by decide
  have hdescent : baseEnd_3397809 < baseStart_3397809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397813 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3397813 : Nat := 118140960795 + 3397813 * 2 ^ 59
def prefixEnd_3397813 : Nat := 4983230072969 + 3 ^ 40 * 3397813 * 2
def baseEnd_3397813 : Nat := 1744711243095419774711249

theorem tailTrace_3397813 : CollatzResearch.WordTrace tailWord_3397813 prefixEnd_3397813 1744711243095419774711249 := by
  unfold tailWord_3397813
  simp only [CollatzResearch.WordTrace]
  refine ⟨123928421239311276105446093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82618947492874184070297395 123928421239311276105446093)
  ·
    refine ⟨46473157964741728539542285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123928421239311276105446093 46473157964741728539542285)
    ·
      refine ⟨17427434236778148202328357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46473157964741728539542285 17427434236778148202328357)
      ·
        refine ⟨3267643919395902787936567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17427434236778148202328357 3267643919395902787936567)
        ·
          refine ⟨4901465879093854181904851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267643919395902787936567 4901465879093854181904851)
          ·
            refine ⟨7352198818640781272857277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901465879093854181904851 7352198818640781272857277)
            ·
              refine ⟨2757074556990292977321479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352198818640781272857277 2757074556990292977321479)
              ·
                refine ⟨4135611835485439465982219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757074556990292977321479 4135611835485439465982219)
                ·
                  refine ⟨6203417753228159198973329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135611835485439465982219 6203417753228159198973329)
                  ·
                    refine ⟨4652563314921119399229997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203417753228159198973329 4652563314921119399229997)
                    ·
                      refine ⟨1744711243095419774711249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652563314921119399229997 1744711243095419774711249)
                      ·
                        rfl

theorem cell23_3397813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3397813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397813 prefixEnd_3397813 := by exact prefixLift 3397813
  have htrace : WordTrace (prefixWord ++ tailWord_3397813) baseStart_3397813 baseEnd_3397813 := by
    simpa [prefixWord, tailWord_3397813, baseEnd_3397813] using wordTrace_append hprefix tailTrace_3397813
  have hstable : (prefixWord ++ tailWord_3397813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397813).length < 2 ^ (prefixWord ++ tailWord_3397813).sum := by decide
  have hdescent : baseEnd_3397813 < baseStart_3397813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397832 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_3397832 : Nat := 118140960795 + 3397832 * 2 ^ 59
def prefixEnd_3397832 : Nat := 4983230072969 + 3 ^ 40 * 3397832 * 2
def baseEnd_3397832 : Nat := 1744720999227855200373661

theorem tailTrace_3397832 : CollatzResearch.WordTrace tailWord_3397832 prefixEnd_3397832 1744720999227855200373661 := by
  unfold tailWord_3397832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61964557113121221175193875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82619409484161628233591833 61964557113121221175193875)
  ·
    refine ⟨92946835669681831762790813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61964557113121221175193875 92946835669681831762790813)
    ·
      refine ⟨34855063376130686911046555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92946835669681831762790813 34855063376130686911046555)
      ·
        refine ⟨52282595064196030366569833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34855063376130686911046555 52282595064196030366569833)
        ·
          refine ⟨39211946298147022774927375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52282595064196030366569833 39211946298147022774927375)
          ·
            refine ⟨58817919447220534162391063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39211946298147022774927375 58817919447220534162391063)
            ·
              refine ⟨88226879170830801243586595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58817919447220534162391063 88226879170830801243586595)
              ·
                refine ⟨132340318756246201865379893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88226879170830801243586595 132340318756246201865379893)
                ·
                  refine ⟨12406904883398081424879365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132340318756246201865379893 12406904883398081424879365)
                  ·
                    refine ⟨2326294665637140267164881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12406904883398081424879365 2326294665637140267164881)
                    ·
                      refine ⟨1744720999227855200373661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326294665637140267164881 1744720999227855200373661)
                      ·
                        rfl

theorem cell23_3397832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_3397832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397832 prefixEnd_3397832 := by exact prefixLift 3397832
  have htrace : WordTrace (prefixWord ++ tailWord_3397832) baseStart_3397832 baseEnd_3397832 := by
    simpa [prefixWord, tailWord_3397832, baseEnd_3397832] using wordTrace_append hprefix tailTrace_3397832
  have hstable : (prefixWord ++ tailWord_3397832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397832).length < 2 ^ (prefixWord ++ tailWord_3397832).sum := by decide
  have hdescent : baseEnd_3397832 < baseStart_3397832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397835 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3]
def baseStart_3397835 : Nat := 118140960795 + 3397835 * 2 ^ 59
def prefixEnd_3397835 : Nat := 4983230072969 + 3 ^ 40 * 3397835 * 2
def baseEnd_3397835 : Nat := 1744722539669818688636147

theorem tailTrace_3397835 : CollatzResearch.WordTrace tailWord_3397835 prefixEnd_3397835 1744722539669818688636147 := by
  unfold tailWord_3397835
  simp only [CollatzResearch.WordTrace]
  refine ⟨123929223645231573862746959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82619482430154382575164639 123929223645231573862746959)
  ·
    refine ⟨185893835467847360794120439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123929223645231573862746959 185893835467847360794120439)
    ·
      refine ⟨278840753201771041191180659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185893835467847360794120439 278840753201771041191180659)
      ·
        refine ⟨418261129802656561786770989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278840753201771041191180659 418261129802656561786770989)
        ·
          refine ⟨156847923675996210670039121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418261129802656561786770989 156847923675996210670039121)
          ·
            refine ⟨117635942756997158002529341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156847923675996210670039121 117635942756997158002529341)
            ·
              refine ⟨44113478533873934250948503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117635942756997158002529341 44113478533873934250948503)
              ·
                refine ⟨66170217800810901376422755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44113478533873934250948503 66170217800810901376422755)
                ·
                  refine ⟨99255326701216352064634133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66170217800810901376422755 99255326701216352064634133)
                  ·
                    refine ⟨4652593439119516503029725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99255326701216352064634133 4652593439119516503029725)
                    ·
                      refine ⟨1744722539669818688636147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652593439119516503029725 1744722539669818688636147)
                      ·
                        rfl

theorem cell23_3397835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3].length) (baseStart_3397835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397835 prefixEnd_3397835 := by exact prefixLift 3397835
  have htrace : WordTrace (prefixWord ++ tailWord_3397835) baseStart_3397835 baseEnd_3397835 := by
    simpa [prefixWord, tailWord_3397835, baseEnd_3397835] using wordTrace_append hprefix tailTrace_3397835
  have hstable : (prefixWord ++ tailWord_3397835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397835).length < 2 ^ (prefixWord ++ tailWord_3397835).sum := by decide
  have hdescent : baseEnd_3397835 < baseStart_3397835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397842 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3397842 : Nat := 118140960795 + 3397842 * 2 ^ 59
def prefixEnd_3397842 : Nat := 4983230072969 + 3 ^ 40 * 3397842 * 2
def baseEnd_3397842 : Nat := 581575378011466720416205

theorem tailTrace_3397842 : CollatzResearch.WordTrace tailWord_3397842 prefixEnd_3397842 581575378011466720416205 := by
  unfold tailWord_3397842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30982369739051553514562945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82619652637470809372167853 30982369739051553514562945)
  ·
    refine ⟨23236777304288665135922209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30982369739051553514562945 23236777304288665135922209)
    ·
      refine ⟨17427582978216498851941657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23236777304288665135922209 17427582978216498851941657)
      ·
        refine ⟨13070687233662374138956243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17427582978216498851941657 13070687233662374138956243)
        ·
          refine ⟨19606030850493561208434365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13070687233662374138956243 19606030850493561208434365)
          ·
            refine ⟨7352261568935085453162887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19606030850493561208434365 7352261568935085453162887)
            ·
              refine ⟨11028392353402628179744331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352261568935085453162887 11028392353402628179744331)
              ·
                refine ⟨16542588530103942269616497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11028392353402628179744331 16542588530103942269616497)
                ·
                  refine ⟨12406941397577956702212373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16542588530103942269616497 12406941397577956702212373)
                  ·
                    refine ⟨581575378011466720416205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12406941397577956702212373 581575378011466720416205)
                    ·
                      rfl

theorem cell23_3397842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3397842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397842 prefixEnd_3397842 := by exact prefixLift 3397842
  have htrace : WordTrace (prefixWord ++ tailWord_3397842) baseStart_3397842 baseEnd_3397842 := by
    simpa [prefixWord, tailWord_3397842, baseEnd_3397842] using wordTrace_append hprefix tailTrace_3397842
  have hstable : (prefixWord ++ tailWord_3397842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397842).length < 2 ^ (prefixWord ++ tailWord_3397842).sum := by decide
  have hdescent : baseEnd_3397842 < baseStart_3397842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397882 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_3397882 : Nat := 118140960795 + 3397882 * 2 ^ 59
def prefixEnd_3397882 : Nat := 4983230072969 + 3 ^ 40 * 3397882 * 2
def baseEnd_3397882 : Nat := 1744746673260580004748431

theorem tailTrace_3397882 : CollatzResearch.WordTrace tailWord_3397882 prefixEnd_3397882 1744746673260580004748431 := by
  unfold tailWord_3397882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30982734469015325222426975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82620625250707533926471933 30982734469015325222426975)
  ·
    refine ⟨46474101703522987833640463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30982734469015325222426975 46474101703522987833640463)
    ·
      refine ⟨69711152555284481750460695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46474101703522987833640463 69711152555284481750460695)
      ·
        refine ⟨104566728832926722625691043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69711152555284481750460695 104566728832926722625691043)
        ·
          refine ⟨156850093249390083938536565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104566728832926722625691043 156850093249390083938536565)
          ·
            refine ⟨14704696242130320369237803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156850093249390083938536565 14704696242130320369237803)
            ·
              refine ⟨22057044363195480553856705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14704696242130320369237803 22057044363195480553856705)
              ·
                refine ⟨16542783272396610415392529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22057044363195480553856705 16542783272396610415392529)
                ·
                  refine ⟨12407087454297457811544397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16542783272396610415392529 12407087454297457811544397)
                  ·
                    refine ⟨4652657795361546679329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12407087454297457811544397 4652657795361546679329149)
                    ·
                      refine ⟨1744746673260580004748431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652657795361546679329149 1744746673260580004748431)
                      ·
                        rfl

theorem cell23_3397882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_3397882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397882 prefixEnd_3397882 := by exact prefixLift 3397882
  have htrace : WordTrace (prefixWord ++ tailWord_3397882) baseStart_3397882 baseEnd_3397882 := by
    simpa [prefixWord, tailWord_3397882, baseEnd_3397882] using wordTrace_append hprefix tailTrace_3397882
  have hstable : (prefixWord ++ tailWord_3397882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397882).length < 2 ^ (prefixWord ++ tailWord_3397882).sum := by decide
  have hdescent : baseEnd_3397882 < baseStart_3397882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397932 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_3397932 : Nat := 118140960795 + 3397932 * 2 ^ 59
def prefixEnd_3397932 : Nat := 4983230072969 + 3 ^ 40 * 3397932 * 2
def baseEnd_3397932 : Nat := 581590782431101603041067

theorem tailTrace_3397932 : CollatzResearch.WordTrace tailWord_3397932 prefixEnd_3397932 581590782431101603041067 := by
  unfold tailWord_3397932
  simp only [CollatzResearch.WordTrace]
  refine ⟨61966380762940079714514025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82621841017253439619352033 61966380762940079714514025)
  ·
    refine ⟨46474785572205059785885519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61966380762940079714514025 46474785572205059785885519)
    ·
      refine ⟨69712178358307589678828279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46474785572205059785885519 69712178358307589678828279)
      ·
        refine ⟨104568267537461384518242419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69712178358307589678828279 104568267537461384518242419)
        ·
          refine ⟨156852401306192076777363629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104568267537461384518242419 156852401306192076777363629)
          ·
            refine ⟨58819650489822028791511361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156852401306192076777363629 58819650489822028791511361)
            ·
              refine ⟨44114737867366521593633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58819650489822028791511361 44114737867366521593633521)
              ·
                refine ⟨33086053400524891195225141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44114737867366521593633521 33086053400524891195225141)
                ·
                  refine ⟨3101817506299208549552357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33086053400524891195225141 3101817506299208549552357)
                  ·
                    refine ⟨581590782431101603041067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101817506299208549552357 581590782431101603041067)
                    ·
                      rfl

theorem cell23_3397932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_3397932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397932 prefixEnd_3397932 := by exact prefixLift 3397932
  have htrace : WordTrace (prefixWord ++ tailWord_3397932) baseStart_3397932 baseEnd_3397932 := by
    simpa [prefixWord, tailWord_3397932, baseEnd_3397932] using wordTrace_append hprefix tailTrace_3397932
  have hstable : (prefixWord ++ tailWord_3397932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397932).length < 2 ^ (prefixWord ++ tailWord_3397932).sum := by decide
  have hdescent : baseEnd_3397932 < baseStart_3397932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397935 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_3397935 : Nat := 118140960795 + 3397935 * 2 ^ 59
def prefixEnd_3397935 : Nat := 4983230072969 + 3 ^ 40 * 3397935 * 2
def baseEnd_3397935 : Nat := 1744773887735268297385687

theorem tailTrace_3397935 : CollatzResearch.WordTrace tailWord_3397935 prefixEnd_3397935 1744773887735268297385687 := by
  unfold tailWord_3397935
  simp only [CollatzResearch.WordTrace]
  refine ⟨123932870944869290941387259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82621913963246193960924839 123932870944869290941387259)
  ·
    refine ⟨185899306417303936412080889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123932870944869290941387259 185899306417303936412080889)
    ·
      refine ⟨139424479812977952309060667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185899306417303936412080889 139424479812977952309060667)
      ·
        refine ⟨209136719719466928463591001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139424479812977952309060667 209136719719466928463591001)
        ·
          refine ⟨156852539789600196347693251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209136719719466928463591001 156852539789600196347693251)
          ·
            refine ⟨235278809684400294521539877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156852539789600196347693251 235278809684400294521539877)
            ·
              refine ⟨44114776815825055222788727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235278809684400294521539877 44114776815825055222788727)
              ·
                refine ⟨66172165223737582834183091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44114776815825055222788727 66172165223737582834183091)
                ·
                  refine ⟨99258247835606374251274637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66172165223737582834183091 99258247835606374251274637)
                  ·
                    refine ⟨37221842938352390344227989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99258247835606374251274637 37221842938352390344227989)
                    ·
                      refine ⟨1744773887735268297385687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37221842938352390344227989 1744773887735268297385687)
                      ·
                        rfl

theorem cell23_3397935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_3397935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397935 prefixEnd_3397935 := by exact prefixLift 3397935
  have htrace : WordTrace (prefixWord ++ tailWord_3397935) baseStart_3397935 baseEnd_3397935 := by
    simpa [prefixWord, tailWord_3397935, baseEnd_3397935] using wordTrace_append hprefix tailTrace_3397935
  have hstable : (prefixWord ++ tailWord_3397935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397935).length < 2 ^ (prefixWord ++ tailWord_3397935).sum := by decide
  have hdescent : baseEnd_3397935 < baseStart_3397935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397999 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 4, 3, 2]
def baseStart_3397999 : Nat := 118140960795 + 3397999 * 2 ^ 59
def prefixEnd_3397999 : Nat := 4983230072969 + 3 ^ 40 * 3397999 * 2
def baseEnd_3397999 : Nat := 1744806750497156046985393

theorem tailTrace_3397999 : CollatzResearch.WordTrace tailWord_3397999 prefixEnd_3397999 1744806750497156046985393 := by
  unfold tailWord_3397999
  simp only [CollatzResearch.WordTrace]
  refine ⟨123935205216637429871717051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82623470144424953247811367 123935205216637429871717051)
  ·
    refine ⟨185902807824956144807575577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123935205216637429871717051 185902807824956144807575577)
    ·
      refine ⟨139427105868717108605681683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185902807824956144807575577 139427105868717108605681683)
      ·
        refine ⟨209140658803075662908522525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139427105868717108605681683 209140658803075662908522525)
        ·
          refine ⟨78427747051153373590695947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209140658803075662908522525 78427747051153373590695947)
          ·
            refine ⟨117641620576730060386043921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78427747051153373590695947 117641620576730060386043921)
            ·
              refine ⟨88231215432547545289532941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117641620576730060386043921 88231215432547545289532941)
              ·
                refine ⟨33086705787205329483574853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88231215432547545289532941 33086705787205329483574853)
                ·
                  refine ⟨6203757335100999278170285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33086705787205329483574853 6203757335100999278170285)
                  ·
                    refine ⟨2326409000662874729313857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6203757335100999278170285 2326409000662874729313857)
                    ·
                      refine ⟨1744806750497156046985393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326409000662874729313857 1744806750497156046985393)
                      ·
                        rfl

theorem cell23_3397999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3, 2].length) (baseStart_3397999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3397999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3397999 prefixEnd_3397999 := by exact prefixLift 3397999
  have htrace : WordTrace (prefixWord ++ tailWord_3397999) baseStart_3397999 baseEnd_3397999 := by
    simpa [prefixWord, tailWord_3397999, baseEnd_3397999] using wordTrace_append hprefix tailTrace_3397999
  have hstable : (prefixWord ++ tailWord_3397999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397999).length < 2 ^ (prefixWord ++ tailWord_3397999).sum := by decide
  have hdescent : baseEnd_3397999 < baseStart_3397999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_3398032 : Nat := 118140960795 + 3398032 * 2 ^ 59
def prefixEnd_3398032 : Nat := 4983230072969 + 3 ^ 40 * 3398032 * 2
def baseEnd_3398032 : Nat := 1744823695358754417872741

theorem tailTrace_3398032 : CollatzResearch.WordTrace tailWord_3398032 prefixEnd_3398032 1744823695358754417872741 := by
  unfold tailWord_3398032
  simp only [CollatzResearch.WordTrace]
  refine ⟨61968204412758938253834175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82624272550345251005112233 61968204412758938253834175)
  ·
    refine ⟨92952306619138407380751263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61968204412758938253834175 92952306619138407380751263)
    ·
      refine ⟨139428459928707611071126895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92952306619138407380751263 139428459928707611071126895)
      ·
        refine ⟨209142689893061416606690343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139428459928707611071126895 209142689893061416606690343)
        ·
          refine ⟨313714034839592124910035515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209142689893061416606690343 313714034839592124910035515)
          ·
            refine ⟨470571052259388187365053273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313714034839592124910035515 470571052259388187365053273)
            ·
              refine ⟨352928289194541140523789955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470571052259388187365053273 352928289194541140523789955)
              ·
                refine ⟨529392433791811710785684933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352928289194541140523789955 529392433791811710785684933)
                ·
                  refine ⟨99261081335964695772315925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529392433791811710785684933 99261081335964695772315925)
                  ·
                    refine ⟨4652863187623345114327309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99261081335964695772315925 4652863187623345114327309)
                    ·
                      refine ⟨1744823695358754417872741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652863187623345114327309 1744823695358754417872741)
                      ·
                        rfl

theorem cell23_3398032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_3398032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398032 prefixEnd_3398032 := by exact prefixLift 3398032
  have htrace : WordTrace (prefixWord ++ tailWord_3398032) baseStart_3398032 baseEnd_3398032 := by
    simpa [prefixWord, tailWord_3398032, baseEnd_3398032] using wordTrace_append hprefix tailTrace_3398032
  have hstable : (prefixWord ++ tailWord_3398032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398032).length < 2 ^ (prefixWord ++ tailWord_3398032).sum := by decide
  have hdescent : baseEnd_3398032 < baseStart_3398032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398040 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3398040 : Nat := 118140960795 + 3398040 * 2 ^ 59
def prefixEnd_3398040 : Nat := 4983230072969 + 3 ^ 40 * 3398040 * 2
def baseEnd_3398040 : Nat := 1744827803203990386572705

theorem tailTrace_3398040 : CollatzResearch.WordTrace tailWord_3398040 prefixEnd_3398040 1744827803203990386572705 := by
  unfold tailWord_3398040
  simp only [CollatzResearch.WordTrace]
  refine ⟨61968350304744446936979787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82624467072992595915973049 61968350304744446936979787)
  ·
    refine ⟨92952525457116670405469681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61968350304744446936979787 92952525457116670405469681)
    ·
      refine ⟨69714394092837502804102261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92952525457116670405469681 69714394092837502804102261)
      ·
        refine ⟨6535724446203515887884587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69714394092837502804102261 6535724446203515887884587)
        ·
          refine ⟨9803586669305273831826881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535724446203515887884587 9803586669305273831826881)
          ·
            refine ⟨7352690001978955373870161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9803586669305273831826881 7352690001978955373870161)
            ·
              refine ⟨5514517501484216530402621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7352690001978955373870161 5514517501484216530402621)
              ·
                refine ⟨2067944063056581198900983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5514517501484216530402621 2067944063056581198900983)
                ·
                  refine ⟨3101916094584871798351475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067944063056581198900983 3101916094584871798351475)
                  ·
                    refine ⟨4652874141877307697527213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3101916094584871798351475 4652874141877307697527213)
                    ·
                      refine ⟨1744827803203990386572705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652874141877307697527213 1744827803203990386572705)
                      ·
                        rfl

theorem cell23_3398040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3398040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398040 prefixEnd_3398040 := by exact prefixLift 3398040
  have htrace : WordTrace (prefixWord ++ tailWord_3398040) baseStart_3398040 baseEnd_3398040 := by
    simpa [prefixWord, tailWord_3398040, baseEnd_3398040] using wordTrace_append hprefix tailTrace_3398040
  have hstable : (prefixWord ++ tailWord_3398040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398040).length < 2 ^ (prefixWord ++ tailWord_3398040).sum := by decide
  have hdescent : baseEnd_3398040 < baseStart_3398040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398073 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 2, 4]
def baseStart_3398073 : Nat := 118140960795 + 3398073 * 2 ^ 59
def prefixEnd_3398073 : Nat := 4983230072969 + 3 ^ 40 * 3398073 * 2
def baseEnd_3398073 : Nat := 581614916021862919153351

theorem tailTrace_3398073 : CollatzResearch.WordTrace tailWord_3398073 prefixEnd_3398073 581614916021862919153351 := by
  unfold tailWord_3398073
  simp only [CollatzResearch.WordTrace]
  refine ⟨123937904218369340509910873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82625269478912893673273915 123937904218369340509910873)
  ·
    refine ⟨92953428163777005382433155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123937904218369340509910873 92953428163777005382433155)
    ·
      refine ⟨139430142245665508073649733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92953428163777005382433155 139430142245665508073649733)
      ·
        refine ⟨26143151671062282763809325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139430142245665508073649733 26143151671062282763809325)
        ·
          refine ⟨9803681876648356036428497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26143151671062282763809325 9803681876648356036428497)
          ·
            refine ⟨7352761407486267027321373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9803681876648356036428497 7352761407486267027321373)
            ·
              refine ⟨2757285527807350135245515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352761407486267027321373 2757285527807350135245515)
              ·
                refine ⟨4135928291711025202868273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757285527807350135245515 4135928291711025202868273)
                ·
                  refine ⟨3101946218783268902151205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4135928291711025202868273 3101946218783268902151205)
                  ·
                    refine ⟨581614916021862919153351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101946218783268902151205 581614916021862919153351)
                    ·
                      rfl

theorem cell23_3398073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_3398073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398073 prefixEnd_3398073 := by exact prefixLift 3398073
  have htrace : WordTrace (prefixWord ++ tailWord_3398073) baseStart_3398073 baseEnd_3398073 := by
    simpa [prefixWord, tailWord_3398073, baseEnd_3398073] using wordTrace_append hprefix tailTrace_3398073
  have hstable : (prefixWord ++ tailWord_3398073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398073).length < 2 ^ (prefixWord ++ tailWord_3398073).sum := by decide
  have hdescent : baseEnd_3398073 < baseStart_3398073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398076 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3398076 : Nat := 118140960795 + 3398076 * 2 ^ 59
def prefixEnd_3398076 : Nat := 4983230072969 + 3 ^ 40 * 3398076 * 2
def baseEnd_3398076 : Nat := 1744846288507552245722539

theorem tailTrace_3398076 : CollatzResearch.WordTrace tailWord_3398076 prefixEnd_3398076 1744846288507552245722539 := by
  unfold tailWord_3398076
  simp only [CollatzResearch.WordTrace]
  refine ⟨61969006818679236011135041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82625342424905648014846721 61969006818679236011135041)
  ·
    refine ⟨46476755114009427008351281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61969006818679236011135041 46476755114009427008351281)
    ·
      refine ⟨34857566335507070256263461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46476755114009427008351281 34857566335507070256263461)
      ·
        refine ⟨6535793687907575673049399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34857566335507070256263461 6535793687907575673049399)
        ·
          refine ⟨9803690531861363509574099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535793687907575673049399 9803690531861363509574099)
          ·
            refine ⟨14705535797792045264361149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803690531861363509574099 14705535797792045264361149)
            ·
              refine ⟨5514575924172016974135431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14705535797792045264361149 5514575924172016974135431)
              ·
                refine ⟨8271863886258025461203147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5514575924172016974135431 8271863886258025461203147)
                ·
                  refine ⟨12407795829387038191804721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271863886258025461203147 12407795829387038191804721)
                  ·
                    refine ⟨9305846872040278643853541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12407795829387038191804721 9305846872040278643853541)
                    ·
                      refine ⟨1744846288507552245722539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9305846872040278643853541 1744846288507552245722539)
                      ·
                        rfl

theorem cell23_3398076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3398076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398076 prefixEnd_3398076 := by exact prefixLift 3398076
  have htrace : WordTrace (prefixWord ++ tailWord_3398076) baseStart_3398076 baseEnd_3398076 := by
    simpa [prefixWord, tailWord_3398076, baseEnd_3398076] using wordTrace_append hprefix tailTrace_3398076
  have hstable : (prefixWord ++ tailWord_3398076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398076).length < 2 ^ (prefixWord ++ tailWord_3398076).sum := by decide
  have hdescent : baseEnd_3398076 < baseStart_3398076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398109 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3398109 : Nat := 118140960795 + 3398109 * 2 ^ 59
def prefixEnd_3398109 : Nat := 4983230072969 + 3 ^ 40 * 3398109 * 2
def baseEnd_3398109 : Nat := 1744863233369150616609887

theorem tailTrace_3398109 : CollatzResearch.WordTrace tailWord_3398109 prefixEnd_3398109 1744863233369150616609887 := by
  unfold tailWord_3398109
  simp only [CollatzResearch.WordTrace]
  refine ⟨123939217246238918658221381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82626144830825945772147587 123939217246238918658221381)
  ·
    refine ⟨23238603233669797248416509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123939217246238918658221381 23238603233669797248416509)
    ·
      refine ⟨8714476212626173968156191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23238603233669797248416509 8714476212626173968156191)
      ·
        refine ⟨13071714318939260952234287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714476212626173968156191 13071714318939260952234287)
        ·
          refine ⟨19607571478408891428351431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071714318939260952234287 19607571478408891428351431)
          ·
            refine ⟨29411357217613337142527147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607571478408891428351431 29411357217613337142527147)
            ·
              refine ⟨44117035826420005713790721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29411357217613337142527147 44117035826420005713790721)
              ·
                refine ⟨33087776869815004285343041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44117035826420005713790721 33087776869815004285343041)
                ·
                  refine ⟨24815832652361253214007281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33087776869815004285343041 24815832652361253214007281)
                  ·
                    refine ⟨18611874489270939910505461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24815832652361253214007281 18611874489270939910505461)
                    ·
                      refine ⟨1744863233369150616609887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18611874489270939910505461 1744863233369150616609887)
                      ·
                        rfl

theorem cell23_3398109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3398109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398109 prefixEnd_3398109 := by exact prefixLift 3398109
  have htrace : WordTrace (prefixWord ++ tailWord_3398109) baseStart_3398109 baseEnd_3398109 := by
    simpa [prefixWord, tailWord_3398109, baseEnd_3398109] using wordTrace_append hprefix tailTrace_3398109
  have hstable : (prefixWord ++ tailWord_3398109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398109).length < 2 ^ (prefixWord ++ tailWord_3398109).sum := by decide
  have hdescent : baseEnd_3398109 < baseStart_3398109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398114 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3398114 : Nat := 118140960795 + 3398114 * 2 ^ 59
def prefixEnd_3398114 : Nat := 4983230072969 + 3 ^ 40 * 3398114 * 2
def baseEnd_3398114 : Nat := 1744865800772423097047365

theorem tailTrace_3398114 : CollatzResearch.WordTrace tailWord_3398114 prefixEnd_3398114 1744865800772423097047365 := by
  unfold tailWord_3398114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30984849902805201128038349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82626266407480536341435597 30984849902805201128038349)
  ·
    refine ⟨11619318713551950423014381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30984849902805201128038349 11619318713551950423014381)
    ·
      refine ⟨4357244517581981408630393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11619318713551950423014381 4357244517581981408630393)
      ·
        refine ⟨3267933388186486056472795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357244517581981408630393 3267933388186486056472795)
        ·
          refine ⟨4901900082279729084709193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267933388186486056472795 4901900082279729084709193)
          ·
            refine ⟨3676425061709796813531895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901900082279729084709193 3676425061709796813531895)
            ·
              refine ⟨5514637592564695220297843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676425061709796813531895 5514637592564695220297843)
              ·
                refine ⟨8271956388847042830446765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5514637592564695220297843 8271956388847042830446765)
                ·
                  refine ⟨3101983645817641061417537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8271956388847042830446765 3101983645817641061417537)
                  ·
                    refine ⟨2326487734363230796063153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3101983645817641061417537 2326487734363230796063153)
                    ·
                      refine ⟨1744865800772423097047365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326487734363230796063153 1744865800772423097047365)
                      ·
                        rfl

theorem cell23_3398114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3398114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398114 prefixEnd_3398114 := by exact prefixLift 3398114
  have htrace : WordTrace (prefixWord ++ tailWord_3398114) baseStart_3398114 baseEnd_3398114 := by
    simpa [prefixWord, tailWord_3398114, baseEnd_3398114] using wordTrace_append hprefix tailTrace_3398114
  have hstable : (prefixWord ++ tailWord_3398114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398114).length < 2 ^ (prefixWord ++ tailWord_3398114).sum := by decide
  have hdescent : baseEnd_3398114 < baseStart_3398114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398119 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3398119 : Nat := 118140960795 + 3398119 * 2 ^ 59
def prefixEnd_3398119 : Nat := 4983230072969 + 3 ^ 40 * 3398119 * 2
def baseEnd_3398119 : Nat := 1744868368175695577484841

theorem tailTrace_3398119 : CollatzResearch.WordTrace tailWord_3398119 prefixEnd_3398119 1744868368175695577484841 := by
  unfold tailWord_3398119
  simp only [CollatzResearch.WordTrace]
  refine ⟨123939581976202690366085411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82626387984135126910723607 123939581976202690366085411)
  ·
    refine ⟨185909372964304035549128117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123939581976202690366085411 185909372964304035549128117)
    ·
      refine ⟨17429003715403503332730761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185909372964304035549128117 17429003715403503332730761)
      ·
        refine ⟨13071752786552627499548071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17429003715403503332730761 13071752786552627499548071)
        ·
          refine ⟨19607629179828941249322107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071752786552627499548071 19607629179828941249322107)
          ·
            refine ⟨29411443769743411873983161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607629179828941249322107 29411443769743411873983161)
            ·
              refine ⟨22058582827307558905487371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29411443769743411873983161 22058582827307558905487371)
              ·
                refine ⟨33087874240961338358231057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22058582827307558905487371 33087874240961338358231057)
                ·
                  refine ⟨24815905680721003768673293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33087874240961338358231057 24815905680721003768673293)
                  ·
                    refine ⟨9305964630270376413252485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24815905680721003768673293 9305964630270376413252485)
                    ·
                      refine ⟨1744868368175695577484841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9305964630270376413252485 1744868368175695577484841)
                      ·
                        rfl

theorem cell23_3398119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3398119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398119 prefixEnd_3398119 := by exact prefixLift 3398119
  have htrace : WordTrace (prefixWord ++ tailWord_3398119) baseStart_3398119 baseEnd_3398119 := by
    simpa [prefixWord, tailWord_3398119, baseEnd_3398119] using wordTrace_append hprefix tailTrace_3398119
  have hstable : (prefixWord ++ tailWord_3398119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398119).length < 2 ^ (prefixWord ++ tailWord_3398119).sum := by decide
  have hdescent : baseEnd_3398119 < baseStart_3398119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398130 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3398130 : Nat := 118140960795 + 3398130 * 2 ^ 59
def prefixEnd_3398130 : Nat := 4983230072969 + 3 ^ 40 * 3398130 * 2
def baseEnd_3398130 : Nat := 1744874016462895034447291

theorem tailTrace_3398130 : CollatzResearch.WordTrace tailWord_3398130 prefixEnd_3398130 1744874016462895034447291 := by
  unfold tailWord_3398130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30984995794790709811183961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82626655452775226163157229 30984995794790709811183961)
  ·
    refine ⟨23238746846093032358387971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30984995794790709811183961 23238746846093032358387971)
    ·
      refine ⟨34858120269139548537581957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23238746846093032358387971 34858120269139548537581957)
      ·
        refine ⟨6535897550463665350796617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34858120269139548537581957 6535897550463665350796617)
        ·
          refine ⟨4901923162847749013097463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535897550463665350796617 4901923162847749013097463)
          ·
            refine ⟨7352884744271623519646195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901923162847749013097463 7352884744271623519646195)
            ·
              refine ⟨11029327116407435279469293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352884744271623519646195 11029327116407435279469293)
              ·
                refine ⟨4135997668652788229800985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11029327116407435279469293 4135997668652788229800985)
                ·
                  refine ⟨3101998251489591172350739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4135997668652788229800985 3101998251489591172350739)
                  ·
                    refine ⟨4652997377234386758526109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3101998251489591172350739 4652997377234386758526109)
                    ·
                      refine ⟨1744874016462895034447291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4652997377234386758526109 1744874016462895034447291)
                      ·
                        rfl

theorem cell23_3398130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3398130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398130 prefixEnd_3398130 := by exact prefixLift 3398130
  have htrace : WordTrace (prefixWord ++ tailWord_3398130) baseStart_3398130 baseEnd_3398130 := by
    simpa [prefixWord, tailWord_3398130, baseEnd_3398130] using wordTrace_append hprefix tailTrace_3398130
  have hstable : (prefixWord ++ tailWord_3398130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398130).length < 2 ^ (prefixWord ++ tailWord_3398130).sum := by decide
  have hdescent : baseEnd_3398130 < baseStart_3398130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398136 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_3398136 : Nat := 118140960795 + 3398136 * 2 ^ 59
def prefixEnd_3398136 : Nat := 4983230072969 + 3 ^ 40 * 3398136 * 2
def baseEnd_3398136 : Nat := 1744877097346822010972263

theorem tailTrace_3398136 : CollatzResearch.WordTrace tailWord_3398136 prefixEnd_3398136 1744877097346822010972263 := by
  unfold tailWord_3398136
  simp only [CollatzResearch.WordTrace]
  refine ⟨61970101008570551134727131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82626801344760734846302841 61970101008570551134727131)
  ·
    refine ⟨92955151512855826702090697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61970101008570551134727131 92955151512855826702090697)
    ·
      refine ⟨69716363634641870026568023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92955151512855826702090697 69716363634641870026568023)
      ·
        refine ⟨104574545451962805039852035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69716363634641870026568023 104574545451962805039852035)
        ·
          refine ⟨156861818177944207559778053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104574545451962805039852035 156861818177944207559778053)
          ·
            refine ⟨29411590908364538917458385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156861818177944207559778053 29411590908364538917458385)
            ·
              refine ⟨22058693181273404188093789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29411590908364538917458385 22058693181273404188093789)
              ·
                refine ⟨8272009942977526570535171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22058693181273404188093789 8272009942977526570535171)
                ·
                  refine ⟨12408014914466289855802757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8272009942977526570535171 12408014914466289855802757)
                  ·
                    refine ⟨2326502796462429347963017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12408014914466289855802757 2326502796462429347963017)
                    ·
                      refine ⟨1744877097346822010972263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326502796462429347963017 1744877097346822010972263)
                      ·
                        rfl

theorem cell23_3398136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_3398136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398136 prefixEnd_3398136 := by exact prefixLift 3398136
  have htrace : WordTrace (prefixWord ++ tailWord_3398136) baseStart_3398136 baseEnd_3398136 := by
    simpa [prefixWord, tailWord_3398136, baseEnd_3398136] using wordTrace_append hprefix tailTrace_3398136
  have hstable : (prefixWord ++ tailWord_3398136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398136).length < 2 ^ (prefixWord ++ tailWord_3398136).sum := by decide
  have hdescent : baseEnd_3398136 < baseStart_3398136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398169 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_3398169 : Nat := 118140960795 + 3398169 * 2 ^ 59
def prefixEnd_3398169 : Nat := 4983230072969 + 3 ^ 40 * 3398169 * 2
def baseEnd_3398169 : Nat := 1744894042208420381859611

theorem tailTrace_3398169 : CollatzResearch.WordTrace tailWord_3398169 prefixEnd_3398169 1744894042208420381859611 := by
  unfold tailWord_3398169
  simp only [CollatzResearch.WordTrace]
  refine ⟨123941405626021548905405561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82627603750681032603603707 123941405626021548905405561)
  ·
    refine ⟨92956054219516161679054171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123941405626021548905405561 92956054219516161679054171)
    ·
      refine ⟨139434081329274242518581257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92956054219516161679054171 139434081329274242518581257)
      ·
        refine ⟨104575560996955681888935943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139434081329274242518581257 104575560996955681888935943)
        ·
          refine ⟨156863341495433522833403915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104575560996955681888935943 156863341495433522833403915)
          ·
            refine ⟨235295012243150284250105873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156863341495433522833403915 235295012243150284250105873)
            ·
              refine ⟨176471259182362713187579405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235295012243150284250105873 176471259182362713187579405)
              ·
                refine ⟨66176722193386017445342277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176471259182362713187579405 66176722193386017445342277)
                ·
                  refine ⟨12408135411259878271001677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66176722193386017445342277 12408135411259878271001677)
                  ·
                    refine ⟨4653050779222454351625629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12408135411259878271001677 4653050779222454351625629)
                    ·
                      refine ⟨1744894042208420381859611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653050779222454351625629 1744894042208420381859611)
                      ·
                        rfl

theorem cell23_3398169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_3398169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398169 prefixEnd_3398169 := by exact prefixLift 3398169
  have htrace : WordTrace (prefixWord ++ tailWord_3398169) baseStart_3398169 baseEnd_3398169 := by
    simpa [prefixWord, tailWord_3398169, baseEnd_3398169] using wordTrace_append hprefix tailTrace_3398169
  have hstable : (prefixWord ++ tailWord_3398169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398169).length < 2 ^ (prefixWord ++ tailWord_3398169).sum := by decide
  have hdescent : baseEnd_3398169 < baseStart_3398169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398186 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3398186 : Nat := 118140960795 + 3398186 * 2 ^ 59
def prefixEnd_3398186 : Nat := 4983230072969 + 3 ^ 40 * 3398186 * 2
def baseEnd_3398186 : Nat := 1744902771379546815347033

theorem tailTrace_3398186 : CollatzResearch.WordTrace tailWord_3398186 prefixEnd_3398186 1744902771379546815347033 := by
  unfold tailWord_3398186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30985506416739990202193603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82628017111306640539182941 30985506416739990202193603)
  ·
    refine ⟨46478259625109985303290405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30985506416739990202193603 46478259625109985303290405)
    ·
      refine ⟨8714673679708122244366951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46478259625109985303290405 8714673679708122244366951)
      ·
        refine ⟨13072010519562183366550427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714673679708122244366951 13072010519562183366550427)
        ·
          refine ⟨19608015779343275049825641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072010519562183366550427 19608015779343275049825641)
          ·
            refine ⟨14706011834507456287369231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19608015779343275049825641 14706011834507456287369231)
            ·
              refine ⟨22059017751761184431053847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14706011834507456287369231 22059017751761184431053847)
              ·
                refine ⟨33088526627641776646580771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22059017751761184431053847 33088526627641776646580771)
                ·
                  refine ⟨49632789941462664969871157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33088526627641776646580771 49632789941462664969871157)
                  ·
                    refine ⟨4653074057012124840925421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49632789941462664969871157 4653074057012124840925421)
                    ·
                      refine ⟨1744902771379546815347033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653074057012124840925421 1744902771379546815347033)
                      ·
                        rfl

theorem cell23_3398186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3398186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398186 prefixEnd_3398186 := by exact prefixLift 3398186
  have htrace : WordTrace (prefixWord ++ tailWord_3398186) baseStart_3398186 baseEnd_3398186 := by
    simpa [prefixWord, tailWord_3398186, baseEnd_3398186] using wordTrace_append hprefix tailTrace_3398186
  have hstable : (prefixWord ++ tailWord_3398186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398186).length < 2 ^ (prefixWord ++ tailWord_3398186).sum := by decide
  have hdescent : baseEnd_3398186 < baseStart_3398186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398226 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3398226 : Nat := 118140960795 + 3398226 * 2 ^ 59
def prefixEnd_3398226 : Nat := 4983230072969 + 3 ^ 40 * 3398226 * 2
def baseEnd_3398226 : Nat := 1744923310605726658846849

theorem tailTrace_3398226 : CollatzResearch.WordTrace tailWord_3398226 prefixEnd_3398226 1744923310605726658846849 := by
  unfold tailWord_3398226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30985871146703761910057633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82628989724543365093487021 30985871146703761910057633)
  ·
    refine ⟨23239403360027821432543225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30985871146703761910057633 23239403360027821432543225)
    ·
      refine ⟨17429552520020866074407419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23239403360027821432543225 17429552520020866074407419)
      ·
        refine ⟨26144328780031299111611129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17429552520020866074407419 26144328780031299111611129)
        ·
          refine ⟨19608246585023474333708347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26144328780031299111611129 19608246585023474333708347)
          ·
            refine ⟨29412369877535211500562521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19608246585023474333708347 29412369877535211500562521)
            ·
              refine ⟨22059277408151408625421891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29412369877535211500562521 22059277408151408625421891)
              ·
                refine ⟨33088916112227112938132837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22059277408151408625421891 33088916112227112938132837)
                ·
                  refine ⟨6204171771042583675899907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33088916112227112938132837 6204171771042583675899907)
                  ·
                    refine ⟨9306257656563875513849861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6204171771042583675899907 9306257656563875513849861)
                    ·
                      refine ⟨1744923310605726658846849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9306257656563875513849861 1744923310605726658846849)
                      ·
                        rfl

theorem cell23_3398226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3398226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398226 prefixEnd_3398226 := by exact prefixLift 3398226
  have htrace : WordTrace (prefixWord ++ tailWord_3398226) baseStart_3398226 baseEnd_3398226 := by
    simpa [prefixWord, tailWord_3398226, baseEnd_3398226] using wordTrace_append hprefix tailTrace_3398226
  have hstable : (prefixWord ++ tailWord_3398226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398226).length < 2 ^ (prefixWord ++ tailWord_3398226).sum := by decide
  have hdescent : baseEnd_3398226 < baseStart_3398226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398229 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3398229 : Nat := 118140960795 + 3398229 * 2 ^ 59
def prefixEnd_3398229 : Nat := 4983230072969 + 3 ^ 40 * 3398229 * 2
def baseEnd_3398229 : Nat := 1744924851047690147109335

theorem tailTrace_3398229 : CollatzResearch.WordTrace tailWord_3398229 prefixEnd_3398229 1744924851047690147109335 := by
  unfold tailWord_3398229
  simp only [CollatzResearch.WordTrace]
  refine ⟨123943594005804179152589741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82629062670536119435059827 123943594005804179152589741)
  ·
    refine ⟨46478847752176567182221153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123943594005804179152589741 46478847752176567182221153)
    ·
      refine ⟨34859135814132425386665865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46478847752176567182221153 34859135814132425386665865)
      ·
        refine ⟨26144351860599319039999399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34859135814132425386665865 26144351860599319039999399)
        ·
          refine ⟨39216527790898978559999099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26144351860599319039999399 39216527790898978559999099)
          ·
            refine ⟨58824791686348467839998649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39216527790898978559999099 58824791686348467839998649)
            ·
              refine ⟨44118593764761350879998987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58824791686348467839998649 44118593764761350879998987)
              ·
                refine ⟨66177890647142026319998481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44118593764761350879998987 66177890647142026319998481)
                ·
                  refine ⟨49633417985356519739998861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66177890647142026319998481 49633417985356519739998861)
                  ·
                    refine ⟨18612531744508694902499573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49633417985356519739998861 18612531744508694902499573)
                    ·
                      refine ⟨1744924851047690147109335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18612531744508694902499573 1744924851047690147109335)
                      ·
                        rfl

theorem cell23_3398229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3398229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398229 prefixEnd_3398229 := by exact prefixLift 3398229
  have htrace : WordTrace (prefixWord ++ tailWord_3398229) baseStart_3398229 baseEnd_3398229 := by
    simpa [prefixWord, tailWord_3398229, baseEnd_3398229] using wordTrace_append hprefix tailTrace_3398229
  have hstable : (prefixWord ++ tailWord_3398229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398229).length < 2 ^ (prefixWord ++ tailWord_3398229).sum := by decide
  have hdescent : baseEnd_3398229 < baseStart_3398229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398238 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3398238 : Nat := 118140960795 + 3398238 * 2 ^ 59
def prefixEnd_3398238 : Nat := 4983230072969 + 3 ^ 40 * 3398238 * 2
def baseEnd_3398238 : Nat := 1744929472373580611896795

theorem tailTrace_3398238 : CollatzResearch.WordTrace tailWord_3398238 prefixEnd_3398238 1744929472373580611896795 := by
  unfold tailWord_3398238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15492990282846446711208421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82629281508514382459778245 15492990282846446711208421)
  ·
    refine ⟨2904935678033708758351579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15492990282846446711208421 2904935678033708758351579)
    ·
      refine ⟨4357403517050563137527369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904935678033708758351579 4357403517050563137527369)
      ·
        refine ⟨3268052637787922353145527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357403517050563137527369 3268052637787922353145527)
        ·
          refine ⟨4902078956681883529718291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268052637787922353145527 4902078956681883529718291)
          ·
            refine ⟨7353118435022825294577437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902078956681883529718291 7353118435022825294577437)
            ·
              refine ⟨2757419413133559485466539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7353118435022825294577437 2757419413133559485466539)
              ·
                refine ⟨4136129119700339228199809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757419413133559485466539 4136129119700339228199809)
                ·
                  refine ⟨3102096839775254421149857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4136129119700339228199809 3102096839775254421149857)
                  ·
                    refine ⟨2326572629831440815862393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3102096839775254421149857 2326572629831440815862393)
                    ·
                      refine ⟨1744929472373580611896795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326572629831440815862393 1744929472373580611896795)
                      ·
                        rfl

theorem cell23_3398238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3398238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398238 prefixEnd_3398238 := by exact prefixLift 3398238
  have htrace : WordTrace (prefixWord ++ tailWord_3398238) baseStart_3398238 baseEnd_3398238 := by
    simpa [prefixWord, tailWord_3398238, baseEnd_3398238] using wordTrace_append hprefix tailTrace_3398238
  have hstable : (prefixWord ++ tailWord_3398238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398238).length < 2 ^ (prefixWord ++ tailWord_3398238).sum := by decide
  have hdescent : baseEnd_3398238 < baseStart_3398238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398253 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3398253 : Nat := 118140960795 + 3398253 * 2 ^ 59
def prefixEnd_3398253 : Nat := 4983230072969 + 3 ^ 40 * 3398253 * 2
def baseEnd_3398253 : Nat := 581645724861132684403075

theorem tailTrace_3398253 : CollatzResearch.WordTrace tailWord_3398253 prefixEnd_3398253 581645724861132684403075 := by
  unfold tailWord_3398253
  simp only [CollatzResearch.WordTrace]
  refine ⟨123944469357717231251463413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82629646238478154167642275 123944469357717231251463413)
  ·
    refine ⟨11619794002285990429824695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123944469357717231251463413 11619794002285990429824695)
    ·
      refine ⟨17429691003428985644737043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11619794002285990429824695 17429691003428985644737043)
      ·
        refine ⟨26144536505143478467105565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17429691003428985644737043 26144536505143478467105565)
        ·
          refine ⟨9804201189428804425164587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26144536505143478467105565 9804201189428804425164587)
          ·
            refine ⟨14706301784143206637746881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804201189428804425164587 14706301784143206637746881)
            ·
              refine ⟨11029726338107404978310161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706301784143206637746881 11029726338107404978310161)
              ·
                refine ⟨8272294753580553733732621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11029726338107404978310161 8272294753580553733732621)
                ·
                  refine ⟨3102110532592707650149733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8272294753580553733732621 3102110532592707650149733)
                  ·
                    refine ⟨581645724861132684403075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3102110532592707650149733 581645724861132684403075)
                    ·
                      rfl

theorem cell23_3398253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3398253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398253 prefixEnd_3398253 := by exact prefixLift 3398253
  have htrace : WordTrace (prefixWord ++ tailWord_3398253) baseStart_3398253 baseEnd_3398253 := by
    simpa [prefixWord, tailWord_3398253, baseEnd_3398253] using wordTrace_append hprefix tailTrace_3398253
  have hstable : (prefixWord ++ tailWord_3398253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398253).length < 2 ^ (prefixWord ++ tailWord_3398253).sum := by decide
  have hdescent : baseEnd_3398253 < baseStart_3398253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398296 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_3398296 : Nat := 118140960795 + 3398296 * 2 ^ 59
def prefixEnd_3398296 : Nat := 4983230072969 + 3 ^ 40 * 3398296 * 2
def baseEnd_3398296 : Nat := 581653084750513794990509

theorem tailTrace_3398296 : CollatzResearch.WordTrace tailWord_3398296 prefixEnd_3398296 581653084750513794990509 := by
  unfold tailWord_3398296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61973018848280724797639371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82630691797707633063519161 61973018848280724797639371)
  ·
    refine ⟨92959528272421087196459057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61973018848280724797639371 92959528272421087196459057)
    ·
      refine ⟨69719646204315815397344293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92959528272421087196459057 69719646204315815397344293)
      ·
        refine ⟨13072433663309215387002055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69719646204315815397344293 13072433663309215387002055)
        ·
          refine ⟨19608650494963823080503083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072433663309215387002055 19608650494963823080503083)
          ·
            refine ⟨29412975742445734620754625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19608650494963823080503083 29412975742445734620754625)
            ·
              refine ⟨22059731806834300965565969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29412975742445734620754625 22059731806834300965565969)
              ·
                refine ⟨16544798855125725724174477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22059731806834300965565969 16544798855125725724174477)
                ·
                  refine ⟨6204299570672147146565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16544798855125725724174477 6204299570672147146565429)
                  ·
                    refine ⟨581653084750513794990509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6204299570672147146565429 581653084750513794990509)
                    ·
                      rfl

theorem cell23_3398296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_3398296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398296 prefixEnd_3398296 := by exact prefixLift 3398296
  have htrace : WordTrace (prefixWord ++ tailWord_3398296) baseStart_3398296 baseEnd_3398296 := by
    simpa [prefixWord, tailWord_3398296, baseEnd_3398296] using wordTrace_append hprefix tailTrace_3398296
  have hstable : (prefixWord ++ tailWord_3398296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398296).length < 2 ^ (prefixWord ++ tailWord_3398296).sum := by decide
  have hdescent : baseEnd_3398296 < baseStart_3398296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398300 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 6]
def baseStart_3398300 : Nat := 118140960795 + 3398300 * 2 ^ 59
def prefixEnd_3398300 : Nat := 4983230072969 + 3 ^ 40 * 3398300 * 2
def baseEnd_3398300 : Nat := 193884589797128818813501

theorem tailTrace_3398300 : CollatzResearch.WordTrace tailWord_3398300 prefixEnd_3398300 193884589797128818813501 := by
  unfold tailWord_3398300
  simp only [CollatzResearch.WordTrace]
  refine ⟨61973091794273479139212177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82630789059031305518949569 61973091794273479139212177)
  ·
    refine ⟨46479818845705109354409133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61973091794273479139212177 46479818845705109354409133)
    ·
      refine ⟨17429932067139416007903425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46479818845705109354409133 17429932067139416007903425)
      ·
        refine ⟨13072449050354562005927569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17429932067139416007903425 13072449050354562005927569)
        ·
          refine ⟨9804336787765921504445677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13072449050354562005927569 9804336787765921504445677)
          ·
            refine ⟨3676626295412220564167129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9804336787765921504445677 3676626295412220564167129)
            ·
              refine ⟨2757469721559165423125347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676626295412220564167129 2757469721559165423125347)
              ·
                refine ⟨4136204582338748134688021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757469721559165423125347 4136204582338748134688021)
                ·
                  refine ⟨193884589797128818813501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4136204582338748134688021 193884589797128818813501)
                  ·
                    rfl

theorem cell23_3398300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_3398300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398300 prefixEnd_3398300 := by exact prefixLift 3398300
  have htrace : WordTrace (prefixWord ++ tailWord_3398300) baseStart_3398300 baseEnd_3398300 := by
    simpa [prefixWord, tailWord_3398300, baseEnd_3398300] using wordTrace_append hprefix tailTrace_3398300
  have hstable : (prefixWord ++ tailWord_3398300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398300).length < 2 ^ (prefixWord ++ tailWord_3398300).sum := by decide
  have hdescent : baseEnd_3398300 < baseStart_3398300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398344 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_3398344 : Nat := 118140960795 + 3398344 * 2 ^ 59
def prefixEnd_3398344 : Nat := 4983230072969 + 3 ^ 40 * 3398344 * 2
def baseEnd_3398344 : Nat := 1744983901322957197171307

theorem tailTrace_3398344 : CollatzResearch.WordTrace tailWord_3398344 prefixEnd_3398344 1744983901322957197171307 := by
  unfold tailWord_3398344
  simp only [CollatzResearch.WordTrace]
  refine ⟨61973894200193776896513043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82631858933591702528684057 61973894200193776896513043)
  ·
    refine ⟨92960841300290665344769565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61973894200193776896513043 92960841300290665344769565)
    ·
      refine ⟨34860315487608999504288587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92960841300290665344769565 34860315487608999504288587)
      ·
        refine ⟨52290473231413499256432881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34860315487608999504288587 52290473231413499256432881)
        ·
          refine ⟨39217854923560124442324661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52290473231413499256432881 39217854923560124442324661)
          ·
            refine ⟨3676673899083761666467937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39217854923560124442324661 3676673899083761666467937)
            ·
              refine ⟨2757505424312821249850953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676673899083761666467937 2757505424312821249850953)
              ·
                refine ⟨2068129068234615937388215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757505424312821249850953 2068129068234615937388215)
                ·
                  refine ⟨3102193602351923906082323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068129068234615937388215 3102193602351923906082323)
                  ·
                    refine ⟨4653290403527885859123485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3102193602351923906082323 4653290403527885859123485)
                    ·
                      refine ⟨1744983901322957197171307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653290403527885859123485 1744983901322957197171307)
                      ·
                        rfl

theorem cell23_3398344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_3398344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398344 prefixEnd_3398344 := by exact prefixLift 3398344
  have htrace : WordTrace (prefixWord ++ tailWord_3398344) baseStart_3398344 baseEnd_3398344 := by
    simpa [prefixWord, tailWord_3398344, baseEnd_3398344] using wordTrace_append hprefix tailTrace_3398344
  have hstable : (prefixWord ++ tailWord_3398344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398344).length < 2 ^ (prefixWord ++ tailWord_3398344).sum := by decide
  have hdescent : baseEnd_3398344 < baseStart_3398344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398373 : List Nat := [1, 3, 1, 4, 1, 3, 3, 7]
def baseStart_3398373 : Nat := 118140960795 + 3398373 * 2 ^ 59
def prefixEnd_3398373 : Nat := 4983230072969 + 3 ^ 40 * 3398373 * 2
def baseEnd_3398373 : Nat := 64629584898590280878099

theorem tailTrace_3398373 : CollatzResearch.WordTrace tailWord_3398373 prefixEnd_3398373 64629584898590280878099 := by
  unfold tailWord_3398373
  simp only [CollatzResearch.WordTrace]
  refine ⟨123948846117282491745831773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82632564078188327830554515 123948846117282491745831773)
  ·
    refine ⟨46480817293980934404686915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123948846117282491745831773 46480817293980934404686915)
    ·
      refine ⟨69721225940971401607030373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46480817293980934404686915 69721225940971401607030373)
      ·
        refine ⟨13072729863932137801318195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69721225940971401607030373 13072729863932137801318195)
        ·
          refine ⟨19609094795898206701977293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072729863932137801318195 19609094795898206701977293)
          ·
            refine ⟨7353410548461827513241485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19609094795898206701977293 7353410548461827513241485)
            ·
              refine ⟨2757528955673185317465557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7353410548461827513241485 2757528955673185317465557)
              ·
                refine ⟨64629584898590280878099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2757528955673185317465557 64629584898590280878099)
                ·
                  rfl

theorem cell23_3398373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 7].length) (baseStart_3398373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398373 prefixEnd_3398373 := by exact prefixLift 3398373
  have htrace : WordTrace (prefixWord ++ tailWord_3398373) baseStart_3398373 baseEnd_3398373 := by
    simpa [prefixWord, tailWord_3398373, baseEnd_3398373] using wordTrace_append hprefix tailTrace_3398373
  have hstable : (prefixWord ++ tailWord_3398373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398373).length < 2 ^ (prefixWord ++ tailWord_3398373).sum := by decide
  have hdescent : baseEnd_3398373 < baseStart_3398373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398383 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_3398383 : Nat := 118140960795 + 3398383 * 2 ^ 59
def prefixEnd_3398383 : Nat := 4983230072969 + 3 ^ 40 * 3398383 * 2
def baseEnd_3398383 : Nat := 1745003927068482544583627

theorem tailTrace_3398383 : CollatzResearch.WordTrace tailWord_3398383 prefixEnd_3398383 1745003927068482544583627 := by
  unfold tailWord_3398383
  simp only [CollatzResearch.WordTrace]
  refine ⟨123949210847246263453695803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82632807231497508969130535 123949210847246263453695803)
  ·
    refine ⟨185923816270869395180543705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123949210847246263453695803 185923816270869395180543705)
    ·
      refine ⟨139442862203152046385407779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185923816270869395180543705 139442862203152046385407779)
      ·
        refine ⟨209164293304728069578111669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139442862203152046385407779 209164293304728069578111669)
        ·
          refine ⟨19609152497318256522947969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209164293304728069578111669 19609152497318256522947969)
          ·
            refine ⟨14706864372988692392210977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19609152497318256522947969 14706864372988692392210977)
            ·
              refine ⟨11030148279741519294158233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706864372988692392210977 11030148279741519294158233)
              ·
                refine ⟨8272611209806139470618675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11030148279741519294158233 8272611209806139470618675)
                ·
                  refine ⟨12408916814709209205928013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8272611209806139470618675 12408916814709209205928013)
                  ·
                    refine ⟨4653343805515953452223005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12408916814709209205928013 4653343805515953452223005)
                    ·
                      refine ⟨1745003927068482544583627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653343805515953452223005 1745003927068482544583627)
                      ·
                        rfl

theorem cell23_3398383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_3398383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398383 prefixEnd_3398383 := by exact prefixLift 3398383
  have htrace : WordTrace (prefixWord ++ tailWord_3398383) baseStart_3398383 baseEnd_3398383 := by
    simpa [prefixWord, tailWord_3398383, baseEnd_3398383] using wordTrace_append hprefix tailTrace_3398383
  have hstable : (prefixWord ++ tailWord_3398383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398383).length < 2 ^ (prefixWord ++ tailWord_3398383).sum := by decide
  have hdescent : baseEnd_3398383 < baseStart_3398383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398440 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_3398440 : Nat := 118140960795 + 3398440 * 2 ^ 59
def prefixEnd_3398440 : Nat := 4983230072969 + 3 ^ 40 * 3398440 * 2
def baseEnd_3398440 : Nat := 1745033195465788821570865

theorem tailTrace_3398440 : CollatzResearch.WordTrace tailWord_3398440 prefixEnd_3398440 1745033195465788821570865 := by
  unfold tailWord_3398440
  simp only [CollatzResearch.WordTrace]
  refine ⟨61975644904019881094260387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82634193205359841459013849 61975644904019881094260387)
  ·
    refine ⟨92963467356029821641390581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61975644904019881094260387 92963467356029821641390581)
    ·
      refine ⟨8715325064627795778880367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92963467356029821641390581 8715325064627795778880367)
      ·
        refine ⟨13072987596941693668320551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715325064627795778880367 13072987596941693668320551)
        ·
          refine ⟨19609481395412540502480827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072987596941693668320551 19609481395412540502480827)
          ·
            refine ⟨29414222093118810753721241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19609481395412540502480827 29414222093118810753721241)
            ·
              refine ⟨22060666569839108065290931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29414222093118810753721241 22060666569839108065290931)
              ·
                refine ⟨33090999854758662097936397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22060666569839108065290931 33090999854758662097936397)
                ·
                  refine ⟨12409124945534498286726149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33090999854758662097936397 12409124945534498286726149)
                  ·
                    refine ⟨2326710927287718428761153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12409124945534498286726149 2326710927287718428761153)
                    ·
                      refine ⟨1745033195465788821570865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326710927287718428761153 1745033195465788821570865)
                      ·
                        rfl

theorem cell23_3398440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_3398440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398440 prefixEnd_3398440 := by exact prefixLift 3398440
  have htrace : WordTrace (prefixWord ++ tailWord_3398440) baseStart_3398440 baseEnd_3398440 := by
    simpa [prefixWord, tailWord_3398440, baseEnd_3398440] using wordTrace_append hprefix tailTrace_3398440
  have hstable : (prefixWord ++ tailWord_3398440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398440).length < 2 ^ (prefixWord ++ tailWord_3398440).sum := by decide
  have hdescent : baseEnd_3398440 < baseStart_3398440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398456 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_3398456 : Nat := 118140960795 + 3398456 * 2 ^ 59
def prefixEnd_3398456 : Nat := 4983230072969 + 3 ^ 40 * 3398456 * 2
def baseEnd_3398456 : Nat := 1745041411156260758970791

theorem tailTrace_3398456 : CollatzResearch.WordTrace tailWord_3398456 prefixEnd_3398456 1745041411156260758970791 := by
  unfold tailWord_3398456
  simp only [CollatzResearch.WordTrace]
  refine ⟨61975936687990898460551611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82634582250654531280735481 61975936687990898460551611)
  ·
    refine ⟨92963905031986347690827417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61975936687990898460551611 92963905031986347690827417)
    ·
      refine ⟨69722928773989760768120563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92963905031986347690827417 69722928773989760768120563)
      ·
        refine ⟨104584393160984641152180845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69722928773989760768120563 104584393160984641152180845)
        ·
          refine ⟨39219147435369240432067817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104584393160984641152180845 39219147435369240432067817)
          ·
            refine ⟨29414360576526930324050863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39219147435369240432067817 29414360576526930324050863)
            ·
              refine ⟨44121540864790395486076295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29414360576526930324050863 44121540864790395486076295)
              ·
                refine ⟨66182311297185593229114443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44121540864790395486076295 66182311297185593229114443)
                ·
                  refine ⟨99273466945778389843671665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66182311297185593229114443 99273466945778389843671665)
                  ·
                    refine ⟨74455100209333792382753749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99273466945778389843671665 74455100209333792382753749)
                    ·
                      refine ⟨1745041411156260758970791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74455100209333792382753749 1745041411156260758970791)
                      ·
                        rfl

theorem cell23_3398456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_3398456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398456 prefixEnd_3398456 := by exact prefixLift 3398456
  have htrace : WordTrace (prefixWord ++ tailWord_3398456) baseStart_3398456 baseEnd_3398456 := by
    simpa [prefixWord, tailWord_3398456, baseEnd_3398456] using wordTrace_append hprefix tailTrace_3398456
  have hstable : (prefixWord ++ tailWord_3398456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398456).length < 2 ^ (prefixWord ++ tailWord_3398456).sum := by decide
  have hdescent : baseEnd_3398456 < baseStart_3398456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398463 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 7]
def baseStart_3398463 : Nat := 118140960795 + 3398463 * 2 ^ 59
def prefixEnd_3398463 : Nat := 4983230072969 + 3 ^ 40 * 3398463 * 2
def baseEnd_3398463 : Nat := 193893889502315803509251

theorem tailTrace_3398463 : CollatzResearch.WordTrace tailWord_3398463 prefixEnd_3398463 193893889502315803509251 := by
  unfold tailWord_3398463
  simp only [CollatzResearch.WordTrace]
  refine ⟨123952128686956437116608043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82634752457970958077738695 123952128686956437116608043)
  ·
    refine ⟨185928193030434655674912065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123952128686956437116608043 185928193030434655674912065)
    ·
      refine ⟨139446144772825991756184049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185928193030434655674912065 139446144772825991756184049)
      ·
        refine ⟨104584608579619493817138037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139446144772825991756184049 104584608579619493817138037)
        ·
          refine ⟨9804807054339327545356691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104584608579619493817138037 9804807054339327545356691)
          ·
            refine ⟨14707210581508991318035037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804807054339327545356691 14707210581508991318035037)
            ·
              refine ⟨5515203968065871744263139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14707210581508991318035037 5515203968065871744263139)
              ·
                refine ⟨8272805952098807616394709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515203968065871744263139 8272805952098807616394709)
                ·
                  refine ⟨193893889502315803509251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8272805952098807616394709 193893889502315803509251)
                  ·
                    rfl

theorem cell23_3398463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 7].length) (baseStart_3398463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398463 prefixEnd_3398463 := by exact prefixLift 3398463
  have htrace : WordTrace (prefixWord ++ tailWord_3398463) baseStart_3398463 baseEnd_3398463 := by
    simpa [prefixWord, tailWord_3398463, baseEnd_3398463] using wordTrace_append hprefix tailTrace_3398463
  have hstable : (prefixWord ++ tailWord_3398463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398463).length < 2 ^ (prefixWord ++ tailWord_3398463).sum := by decide
  have hdescent : baseEnd_3398463 < baseStart_3398463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398468 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3398468 : Nat := 118140960795 + 3398468 * 2 ^ 59
def prefixEnd_3398468 : Nat := 4983230072969 + 3 ^ 40 * 3398468 * 2
def baseEnd_3398468 : Nat := 1745047572924114712020737

theorem tailTrace_3398468 : CollatzResearch.WordTrace tailWord_3398468 prefixEnd_3398468 1745047572924114712020737 := by
  unfold tailWord_3398468
  simp only [CollatzResearch.WordTrace]
  refine ⟨61976155525969161485270029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82634874034625548647026705 61976155525969161485270029)
  ·
    refine ⟨23241058322238435556976261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61976155525969161485270029 23241058322238435556976261)
    ·
      refine ⟨4357698435419706666933049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23241058322238435556976261 4357698435419706666933049)
      ·
        refine ⟨3268273826564780000199787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357698435419706666933049 3268273826564780000199787)
        ·
          refine ⟨4902410739847170000299681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268273826564780000199787 4902410739847170000299681)
          ·
            refine ⟨3676808054885377500224761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4902410739847170000299681 3676808054885377500224761)
            ·
              refine ⟨2757606041164033125168571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676808054885377500224761 2757606041164033125168571)
              ·
                refine ⟨4136409061746049687752857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757606041164033125168571 4136409061746049687752857)
                ·
                  refine ⟨3102306796309537265814643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4136409061746049687752857 3102306796309537265814643)
                  ·
                    refine ⟨4653460194464305898721965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3102306796309537265814643 4653460194464305898721965)
                    ·
                      refine ⟨1745047572924114712020737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653460194464305898721965 1745047572924114712020737)
                      ·
                        rfl

theorem cell23_3398468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3398468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398468 prefixEnd_3398468 := by exact prefixLift 3398468
  have htrace : WordTrace (prefixWord ++ tailWord_3398468) baseStart_3398468 baseEnd_3398468 := by
    simpa [prefixWord, tailWord_3398468, baseEnd_3398468] using wordTrace_append hprefix tailTrace_3398468
  have hstable : (prefixWord ++ tailWord_3398468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398468).length < 2 ^ (prefixWord ++ tailWord_3398468).sum := by decide
  have hdescent : baseEnd_3398468 < baseStart_3398468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398503 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3398503 : Nat := 118140960795 + 3398503 * 2 ^ 59
def prefixEnd_3398503 : Nat := 4983230072969 + 3 ^ 40 * 3398503 * 2
def baseEnd_3398503 : Nat := 1745065544747022075083075

theorem tailTrace_3398503 : CollatzResearch.WordTrace tailWord_3398503 prefixEnd_3398503 1745065544747022075083075 := by
  unfold tailWord_3398503
  simp only [CollatzResearch.WordTrace]
  refine ⟨123953587606811523948064163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82635725071207682632042775 123953587606811523948064163)
  ·
    refine ⟨185930381410217285922096245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123953587606811523948064163 185930381410217285922096245)
    ·
      refine ⟨17430973257207870555196523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185930381410217285922096245 17430973257207870555196523)
      ·
        refine ⟨26146459885811805832794785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17430973257207870555196523 26146459885811805832794785)
        ·
          refine ⟨19609844914358854374596089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26146459885811805832794785 19609844914358854374596089)
          ·
            refine ⟨14707383685769140780947067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19609844914358854374596089 14707383685769140780947067)
            ·
              refine ⟨22061075528653711171420601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14707383685769140780947067 22061075528653711171420601)
              ·
                refine ⟨16545806646490283378565451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22061075528653711171420601 16545806646490283378565451)
                ·
                  refine ⟨24818709969735425067848177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545806646490283378565451 24818709969735425067848177)
                  ·
                    refine ⟨18614032477301568800886133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24818709969735425067848177 18614032477301568800886133)
                    ·
                      refine ⟨1745065544747022075083075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18614032477301568800886133 1745065544747022075083075)
                      ·
                        rfl

theorem cell23_3398503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3398503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398503 prefixEnd_3398503 := by exact prefixLift 3398503
  have htrace : WordTrace (prefixWord ++ tailWord_3398503) baseStart_3398503 baseEnd_3398503 := by
    simpa [prefixWord, tailWord_3398503, baseEnd_3398503] using wordTrace_append hprefix tailTrace_3398503
  have hstable : (prefixWord ++ tailWord_3398503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398503).length < 2 ^ (prefixWord ++ tailWord_3398503).sum := by decide
  have hdescent : baseEnd_3398503 < baseStart_3398503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398583 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 5, 5]
def baseStart_3398583 : Nat := 118140960795 + 3398583 * 2 ^ 59
def prefixEnd_3398583 : Nat := 4983230072969 + 3 ^ 40 * 3398583 * 2
def baseEnd_3398583 : Nat := 581702207733127254027569

theorem tailTrace_3398583 : CollatzResearch.WordTrace tailWord_3398583 prefixEnd_3398583 581702207733127254027569 := by
  unfold tailWord_3398583
  simp only [CollatzResearch.WordTrace]
  refine ⟨123956505446521697610976403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82637670297681131740650935 123956505446521697610976403)
  ·
    refine ⟨185934758169782546416464605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123956505446521697610976403 185934758169782546416464605)
    ·
      refine ⟨69725534313668454906174227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185934758169782546416464605 69725534313668454906174227)
      ·
        refine ⟨104588301470502682359261341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69725534313668454906174227 104588301470502682359261341)
        ·
          refine ⟨39220613051438505884723003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104588301470502682359261341 39220613051438505884723003)
          ·
            refine ⟨58830919577157758827084505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39220613051438505884723003 58830919577157758827084505)
            ·
              refine ⟨44123189682868319120313379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58830919577157758827084505 44123189682868319120313379)
              ·
                refine ⟨66184784524302478680470069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44123189682868319120313379 66184784524302478680470069)
                ·
                  refine ⟨6204823549153357376294069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66184784524302478680470069 6204823549153357376294069)
                  ·
                    refine ⟨581702207733127254027569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6204823549153357376294069 581702207733127254027569)
                    ·
                      rfl

theorem cell23_3398583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_3398583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398583 prefixEnd_3398583 := by exact prefixLift 3398583
  have htrace : WordTrace (prefixWord ++ tailWord_3398583) baseStart_3398583 baseEnd_3398583 := by
    simpa [prefixWord, tailWord_3398583, baseEnd_3398583] using wordTrace_append hprefix tailTrace_3398583
  have hstable : (prefixWord ++ tailWord_3398583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398583).length < 2 ^ (prefixWord ++ tailWord_3398583).sum := by decide
  have hdescent : baseEnd_3398583 < baseStart_3398583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398640 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_3398640 : Nat := 118140960795 + 3398640 * 2 ^ 59
def prefixEnd_3398640 : Nat := 4983230072969 + 3 ^ 40 * 3398640 * 2
def baseEnd_3398640 : Nat := 1745135891596688039069945

theorem tailTrace_3398640 : CollatzResearch.WordTrace tailWord_3398640 prefixEnd_3398640 1745135891596688039069945 := by
  unfold tailWord_3398640
  simp only [CollatzResearch.WordTrace]
  refine ⟨61979292203657598172900687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82639056271543464230534249 61979292203657598172900687)
  ·
    refine ⟨92968938305486397259351031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61979292203657598172900687 92968938305486397259351031)
    ·
      refine ⟨139453407458229595889026547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92968938305486397259351031 139453407458229595889026547)
      ·
        refine ⟨209180111187344393833539821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139453407458229595889026547 209180111187344393833539821)
        ·
          refine ⟨78442541695254147687577433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209180111187344393833539821 78442541695254147687577433)
          ·
            refine ⟨58831906271440610765683075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78442541695254147687577433 58831906271440610765683075)
            ·
              refine ⟨88247859407160916148524613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58831906271440610765683075 88247859407160916148524613)
              ·
                refine ⟨16546473638842671777848365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88247859407160916148524613 16546473638842671777848365)
                ·
                  refine ⟨6204927614566001916693137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16546473638842671777848365 6204927614566001916693137)
                  ·
                    refine ⟨4653695710924501437519853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204927614566001916693137 4653695710924501437519853)
                    ·
                      refine ⟨1745135891596688039069945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653695710924501437519853 1745135891596688039069945)
                      ·
                        rfl

theorem cell23_3398640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_3398640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398640 prefixEnd_3398640 := by exact prefixLift 3398640
  have htrace : WordTrace (prefixWord ++ tailWord_3398640) baseStart_3398640 baseEnd_3398640 := by
    simpa [prefixWord, tailWord_3398640, baseEnd_3398640] using wordTrace_append hprefix tailTrace_3398640
  have hstable : (prefixWord ++ tailWord_3398640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398640).length < 2 ^ (prefixWord ++ tailWord_3398640).sum := by decide
  have hdescent : baseEnd_3398640 < baseStart_3398640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398654 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3398654 : Nat := 118140960795 + 3398654 * 2 ^ 59
def prefixEnd_3398654 : Nat := 4983230072969 + 3 ^ 40 * 3398654 * 2
def baseEnd_3398654 : Nat := 1745143080325850984294881

theorem tailTrace_3398654 : CollatzResearch.WordTrace tailWord_3398654 prefixEnd_3398654 1745143080325850984294881 := by
  unfold tailWord_3398654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15494886878658059592101377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82639396686176317824540677 15494886878658059592101377)
  ·
    refine ⟨11621165158993544694076033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15494886878658059592101377 11621165158993544694076033)
    ·
      refine ⟨8715873869245158520557025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11621165158993544694076033 8715873869245158520557025)
      ·
        refine ⟨6536905401933868890417769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8715873869245158520557025 6536905401933868890417769)
        ·
          refine ⟨4902679051450401667813327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6536905401933868890417769 4902679051450401667813327)
          ·
            refine ⟨7354018577175602501719991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902679051450401667813327 7354018577175602501719991)
            ·
              refine ⟨11031027865763403752579987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354018577175602501719991 11031027865763403752579987)
              ·
                refine ⟨16546541798645105628869981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031027865763403752579987 16546541798645105628869981)
                ·
                  refine ⟨6204953174491914610826243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16546541798645105628869981 6204953174491914610826243)
                  ·
                    refine ⟨9307429761737871916239365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6204953174491914610826243 9307429761737871916239365)
                    ·
                      refine ⟨1745143080325850984294881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9307429761737871916239365 1745143080325850984294881)
                      ·
                        rfl

theorem cell23_3398654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3398654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398654 prefixEnd_3398654 := by exact prefixLift 3398654
  have htrace : WordTrace (prefixWord ++ tailWord_3398654) baseStart_3398654 baseEnd_3398654 := by
    simpa [prefixWord, tailWord_3398654, baseEnd_3398654] using wordTrace_append hprefix tailTrace_3398654
  have hstable : (prefixWord ++ tailWord_3398654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398654).length < 2 ^ (prefixWord ++ tailWord_3398654).sum := by decide
  have hdescent : baseEnd_3398654 < baseStart_3398654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398657 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3398657 : Nat := 118140960795 + 3398657 * 2 ^ 59
def prefixEnd_3398657 : Nat := 4983230072969 + 3 ^ 40 * 3398657 * 2
def baseEnd_3398657 : Nat := 1745144620767814472557367

theorem tailTrace_3398657 : CollatzResearch.WordTrace tailWord_3398657 prefixEnd_3398657 1745144620767814472557367 := by
  unfold tailWord_3398657
  simp only [CollatzResearch.WordTrace]
  refine ⟨123959204448253608249170225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82639469632169072166113483 123959204448253608249170225)
  ·
    refine ⟨92969403336190206186877669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123959204448253608249170225 92969403336190206186877669)
    ·
      refine ⟨17431763125535663660039563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92969403336190206186877669 17431763125535663660039563)
      ·
        refine ⟨26147644688303495490059345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17431763125535663660039563 26147644688303495490059345)
        ·
          refine ⟨19610733516227621617544509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26147644688303495490059345 19610733516227621617544509)
          ·
            refine ⟨7354025068585358106579191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19610733516227621617544509 7354025068585358106579191)
            ·
              refine ⟨11031037602878037159868787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354025068585358106579191 11031037602878037159868787)
              ·
                refine ⟨16546556404317055739803181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031037602878037159868787 16546556404317055739803181)
                ·
                  refine ⟨6204958651618895902426193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16546556404317055739803181 6204958651618895902426193)
                  ·
                    refine ⟨4653718988714171926819645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204958651618895902426193 4653718988714171926819645)
                    ·
                      refine ⟨1745144620767814472557367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4653718988714171926819645 1745144620767814472557367)
                      ·
                        rfl

theorem cell23_3398657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3398657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398657 prefixEnd_3398657 := by exact prefixLift 3398657
  have htrace : WordTrace (prefixWord ++ tailWord_3398657) baseStart_3398657 baseEnd_3398657 := by
    simpa [prefixWord, tailWord_3398657, baseEnd_3398657] using wordTrace_append hprefix tailTrace_3398657
  have hstable : (prefixWord ++ tailWord_3398657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398657).length < 2 ^ (prefixWord ++ tailWord_3398657).sum := by decide
  have hdescent : baseEnd_3398657 < baseStart_3398657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398658 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3398658 : Nat := 118140960795 + 3398658 * 2 ^ 59
def prefixEnd_3398658 : Nat := 4983230072969 + 3 ^ 40 * 3398658 * 2
def baseEnd_3398658 : Nat := 1745145134248468968644863

theorem tailTrace_3398658 : CollatzResearch.WordTrace tailWord_3398658 prefixEnd_3398658 1745145134248468968644863 := by
  unfold tailWord_3398658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30989810230312496354989157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82639493947499990279971085 30989810230312496354989157)
  ·
    refine ⟨5810589418183593066560467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30989810230312496354989157 5810589418183593066560467)
    ·
      refine ⟨8715884127275389599840701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810589418183593066560467 8715884127275389599840701)
      ·
        refine ⟨3268456547728271099940263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8715884127275389599840701 3268456547728271099940263)
        ·
          refine ⟨4902684821592406649910395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268456547728271099940263 4902684821592406649910395)
          ·
            refine ⟨7354027232388609974865593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902684821592406649910395 7354027232388609974865593)
            ·
              refine ⟨5515520424291457481149195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354027232388609974865593 5515520424291457481149195)
              ·
                refine ⟨8273280636437186221723793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515520424291457481149195 8273280636437186221723793)
                ·
                  refine ⟨6204960477327889666292845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273280636437186221723793 6204960477327889666292845)
                  ·
                    refine ⟨2326860178997958624859817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6204960477327889666292845 2326860178997958624859817)
                    ·
                      refine ⟨1745145134248468968644863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326860178997958624859817 1745145134248468968644863)
                      ·
                        rfl

theorem cell23_3398658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3398658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398658 prefixEnd_3398658 := by exact prefixLift 3398658
  have htrace : WordTrace (prefixWord ++ tailWord_3398658) baseStart_3398658 baseEnd_3398658 := by
    simpa [prefixWord, tailWord_3398658, baseEnd_3398658] using wordTrace_append hprefix tailTrace_3398658
  have hstable : (prefixWord ++ tailWord_3398658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398658).length < 2 ^ (prefixWord ++ tailWord_3398658).sum := by decide
  have hdescent : baseEnd_3398658 < baseStart_3398658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398673 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_3398673 : Nat := 118140960795 + 3398673 * 2 ^ 59
def prefixEnd_3398673 : Nat := 4983230072969 + 3 ^ 40 * 3398673 * 2
def baseEnd_3398673 : Nat := 581717612152762136652431

theorem tailTrace_3398673 : CollatzResearch.WordTrace tailWord_3398673 prefixEnd_3398673 581717612152762136652431 := by
  unfold tailWord_3398673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123959788016195642981752673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82639858677463761987835115 123959788016195642981752673)
  ·
    refine ⟨92969841012146732236314505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123959788016195642981752673 92969841012146732236314505)
    ·
      refine ⟨69727380759110049177235879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92969841012146732236314505 69727380759110049177235879)
      ·
        refine ⟨104591071138665073765853819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69727380759110049177235879 104591071138665073765853819)
        ·
          refine ⟨156886606707997610648780729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104591071138665073765853819 156886606707997610648780729)
          ·
            refine ⟨117664955030998207986585547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156886606707997610648780729 117664955030998207986585547)
            ·
              refine ⟨176497432546497311979878321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117664955030998207986585547 176497432546497311979878321)
              ·
                refine ⟨132373074409872983984908741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176497432546497311979878321 132373074409872983984908741)
                ·
                  refine ⟨24819951451851184497170389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132373074409872983984908741 24819951451851184497170389)
                  ·
                    refine ⟨581717612152762136652431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24819951451851184497170389 581717612152762136652431)
                    ·
                      rfl

theorem cell23_3398673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_3398673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398673 prefixEnd_3398673 := by exact prefixLift 3398673
  have htrace : WordTrace (prefixWord ++ tailWord_3398673) baseStart_3398673 baseEnd_3398673 := by
    simpa [prefixWord, tailWord_3398673, baseEnd_3398673] using wordTrace_append hprefix tailTrace_3398673
  have hstable : (prefixWord ++ tailWord_3398673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398673).length < 2 ^ (prefixWord ++ tailWord_3398673).sum := by decide
  have hdescent : baseEnd_3398673 < baseStart_3398673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398683 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_3398683 : Nat := 118140960795 + 3398683 * 2 ^ 59
def prefixEnd_3398683 : Nat := 4983230072969 + 3 ^ 40 * 3398683 * 2
def baseEnd_3398683 : Nat := 1745157971264831370832247

theorem tailTrace_3398683 : CollatzResearch.WordTrace tailWord_3398683 prefixEnd_3398683 1745157971264831370832247 := by
  unfold tailWord_3398683
  simp only [CollatzResearch.WordTrace]
  refine ⟨123960152746159414689616703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82640101830772943126411135 123960152746159414689616703)
  ·
    refine ⟨185940229119239122034425055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123960152746159414689616703 185940229119239122034425055)
    ·
      refine ⟨278910343678858683051637583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185940229119239122034425055 278910343678858683051637583)
      ·
        refine ⟨418365515518288024577456375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278910343678858683051637583 418365515518288024577456375)
        ·
          refine ⟨627548273277432036866184563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418365515518288024577456375 627548273277432036866184563)
          ·
            refine ⟨941322409916148055299276845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627548273277432036866184563 941322409916148055299276845)
            ·
              refine ⟨352995903718555520737228817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941322409916148055299276845 352995903718555520737228817)
              ·
                refine ⟨264746927788916640552921613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352995903718555520737228817 264746927788916640552921613)
                ·
                  refine ⟨99280097920843740207345605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264746927788916640552921613 99280097920843740207345605)
                  ·
                    refine ⟨18615018360158201288877301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99280097920843740207345605 18615018360158201288877301)
                    ·
                      refine ⟨1745157971264831370832247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18615018360158201288877301 1745157971264831370832247)
                      ·
                        rfl

theorem cell23_3398683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_3398683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398683 prefixEnd_3398683 := by exact prefixLift 3398683
  have htrace : WordTrace (prefixWord ++ tailWord_3398683) baseStart_3398683 baseEnd_3398683 := by
    simpa [prefixWord, tailWord_3398683, baseEnd_3398683] using wordTrace_append hprefix tailTrace_3398683
  have hstable : (prefixWord ++ tailWord_3398683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398683).length < 2 ^ (prefixWord ++ tailWord_3398683).sum := by decide
  have hdescent : baseEnd_3398683 < baseStart_3398683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398690 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3398690 : Nat := 118140960795 + 3398690 * 2 ^ 59
def prefixEnd_3398690 : Nat := 4983230072969 + 3 ^ 40 * 3398690 * 2
def baseEnd_3398690 : Nat := 581720521876470947814905

theorem tailTrace_3398690 : CollatzResearch.WordTrace tailWord_3398690 prefixEnd_3398690 581720521876470947814905 := by
  unfold tailWord_3398690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30990102014283513721280381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82640272038089369923414349 30990102014283513721280381)
  ·
    refine ⟨11621288255356317645480143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30990102014283513721280381 11621288255356317645480143)
    ·
      refine ⟨17431932383034476468220215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11621288255356317645480143 17431932383034476468220215)
      ·
        refine ⟨26147898574551714702330323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17431932383034476468220215 26147898574551714702330323)
        ·
          refine ⟨39221847861827572053495485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26147898574551714702330323 39221847861827572053495485)
          ·
            refine ⟨14708192948185339520060807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39221847861827572053495485 14708192948185339520060807)
            ·
              refine ⟨22062289422278009280091211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14708192948185339520060807 22062289422278009280091211)
              ·
                refine ⟨33093434133417013920136817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22062289422278009280091211 33093434133417013920136817)
                ·
                  refine ⟨24820075600062760440102613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33093434133417013920136817 24820075600062760440102613)
                  ·
                    refine ⟨581720521876470947814905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24820075600062760440102613 581720521876470947814905)
                    ·
                      rfl

theorem cell23_3398690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3398690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398690 prefixEnd_3398690 := by exact prefixLift 3398690
  have htrace : WordTrace (prefixWord ++ tailWord_3398690) baseStart_3398690 baseEnd_3398690 := by
    simpa [prefixWord, tailWord_3398690, baseEnd_3398690] using wordTrace_append hprefix tailTrace_3398690
  have hstable : (prefixWord ++ tailWord_3398690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398690).length < 2 ^ (prefixWord ++ tailWord_3398690).sum := by decide
  have hdescent : baseEnd_3398690 < baseStart_3398690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398730 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3398730 : Nat := 118140960795 + 3398730 * 2 ^ 59
def prefixEnd_3398730 : Nat := 4983230072969 + 3 ^ 40 * 3398730 * 2
def baseEnd_3398730 : Nat := 1745182104855592686944531

theorem tailTrace_3398730 : CollatzResearch.WordTrace tailWord_3398730 prefixEnd_3398730 1745182104855592686944531 := by
  unfold tailWord_3398730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30990466744247285429144411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82641244651326094477718429 30990466744247285429144411)
  ·
    refine ⟨46485700116370928143716617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30990466744247285429144411 46485700116370928143716617)
    ·
      refine ⟨34864275087278196107787463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46485700116370928143716617 34864275087278196107787463)
      ·
        refine ⟨52296412630917294161681195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34864275087278196107787463 52296412630917294161681195)
        ·
          refine ⟨78444618946375941242521793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52296412630917294161681195 78444618946375941242521793)
          ·
            refine ⟨58833464209781955931891345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78444618946375941242521793 58833464209781955931891345)
            ·
              refine ⟨44125098157336466948918509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58833464209781955931891345 44125098157336466948918509)
              ·
                refine ⟨16546911809001175105844441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44125098157336466948918509 16546911809001175105844441)
                ·
                  refine ⟨12410183856750881329383331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16546911809001175105844441 12410183856750881329383331)
                  ·
                    refine ⟨18615275785126321994074997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12410183856750881329383331 18615275785126321994074997)
                    ·
                      refine ⟨1745182104855592686944531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18615275785126321994074997 1745182104855592686944531)
                      ·
                        rfl

theorem cell23_3398730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3398730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398730 prefixEnd_3398730 := by exact prefixLift 3398730
  have htrace : WordTrace (prefixWord ++ tailWord_3398730) baseStart_3398730 baseEnd_3398730 := by
    simpa [prefixWord, tailWord_3398730, baseEnd_3398730] using wordTrace_append hprefix tailTrace_3398730
  have hstable : (prefixWord ++ tailWord_3398730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398730).length < 2 ^ (prefixWord ++ tailWord_3398730).sum := by decide
  have hdescent : baseEnd_3398730 < baseStart_3398730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398744 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_3398744 : Nat := 118140960795 + 3398744 * 2 ^ 59
def prefixEnd_3398744 : Nat := 4983230072969 + 3 ^ 40 * 3398744 * 2
def baseEnd_3398744 : Nat := 1745189293584755632169467

theorem tailTrace_3398744 : CollatzResearch.WordTrace tailWord_3398744 prefixEnd_3398744 1745189293584755632169467 := by
  unfold tailWord_3398744
  simp only [CollatzResearch.WordTrace]
  refine ⟨61981188799469211053793643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82641585065958948071724857 61981188799469211053793643)
  ·
    refine ⟨92971783199203816580690465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61981188799469211053793643 92971783199203816580690465)
    ·
      refine ⟨69728837399402862435517849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92971783199203816580690465 69728837399402862435517849)
      ·
        refine ⟨52296628049552146826638387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69728837399402862435517849 52296628049552146826638387)
        ·
          refine ⟨78444942074328220239957581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52296628049552146826638387 78444942074328220239957581)
          ·
            refine ⟨29416853277873082589984093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78444942074328220239957581 29416853277873082589984093)
            ·
              refine ⟨11031319979202405971244035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29416853277873082589984093 11031319979202405971244035)
              ·
                refine ⟨16546979968803608956866053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031319979202405971244035 16546979968803608956866053)
                ·
                  refine ⟨3102558744150676679412385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16546979968803608956866053 3102558744150676679412385)
                  ·
                    refine ⟨2326919058113007509559289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3102558744150676679412385 2326919058113007509559289)
                    ·
                      refine ⟨1745189293584755632169467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2326919058113007509559289 1745189293584755632169467)
                      ·
                        rfl

theorem cell23_3398744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_3398744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398744 prefixEnd_3398744 := by exact prefixLift 3398744
  have htrace : WordTrace (prefixWord ++ tailWord_3398744) baseStart_3398744 baseEnd_3398744 := by
    simpa [prefixWord, tailWord_3398744, baseEnd_3398744] using wordTrace_append hprefix tailTrace_3398744
  have hstable : (prefixWord ++ tailWord_3398744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398744).length < 2 ^ (prefixWord ++ tailWord_3398744).sum := by decide
  have hdescent : baseEnd_3398744 < baseStart_3398744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398780 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3398780 : Nat := 118140960795 + 3398780 * 2 ^ 59
def prefixEnd_3398780 : Nat := 4983230072969 + 3 ^ 40 * 3398780 * 2
def baseEnd_3398780 : Nat := 581735926296105830439767

theorem tailTrace_3398780 : CollatzResearch.WordTrace tailWord_3398780 prefixEnd_3398780 581735926296105830439767 := by
  unfold tailWord_3398780
  simp only [CollatzResearch.WordTrace]
  refine ⟨61981845313404000127948897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82642460417872000170598529 61981845313404000127948897)
  ·
    refine ⟨46486383985053000095961673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61981845313404000127948897 46486383985053000095961673)
    ·
      refine ⟨34864787988789750071971255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46486383985053000095961673 34864787988789750071971255)
      ·
        refine ⟨52297181983184625107956883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34864787988789750071971255 52297181983184625107956883)
        ·
          refine ⟨78445772974776937661935325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52297181983184625107956883 78445772974776937661935325)
          ·
            refine ⟨29417164865541351623225747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78445772974776937661935325 29417164865541351623225747)
            ·
              refine ⟨44125747298312027434838621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29417164865541351623225747 44125747298312027434838621)
              ·
                refine ⟨16547155236867010288064483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44125747298312027434838621 16547155236867010288064483)
                ·
                  refine ⟨24820732855300515432096725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16547155236867010288064483 24820732855300515432096725)
                  ·
                    refine ⟨581735926296105830439767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24820732855300515432096725 581735926296105830439767)
                    ·
                      rfl

theorem cell23_3398780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3398780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398780 prefixEnd_3398780 := by exact prefixLift 3398780
  have htrace : WordTrace (prefixWord ++ tailWord_3398780) baseStart_3398780 baseEnd_3398780 := by
    simpa [prefixWord, tailWord_3398780, baseEnd_3398780] using wordTrace_append hprefix tailTrace_3398780
  have hstable : (prefixWord ++ tailWord_3398780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398780).length < 2 ^ (prefixWord ++ tailWord_3398780).sum := by decide
  have hdescent : baseEnd_3398780 < baseStart_3398780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398800 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_3398800 : Nat := 118140960795 + 3398800 * 2 ^ 59
def prefixEnd_3398800 : Nat := 4983230072969 + 3 ^ 40 * 3398800 * 2
def baseEnd_3398800 : Nat := 1745218048501407413069209

theorem tailTrace_3398800 : CollatzResearch.WordTrace tailWord_3398800 prefixEnd_3398800 1745218048501407413069209 := by
  unfold tailWord_3398800
  simp only [CollatzResearch.WordTrace]
  refine ⟨61982210043367771835812927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82642946724490362447750569 61982210043367771835812927)
  ·
    refine ⟨92973315065051657753719391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61982210043367771835812927 92973315065051657753719391)
    ·
      refine ⟨139459972597577486630579087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92973315065051657753719391 139459972597577486630579087)
      ·
        refine ⟨209189958896366229945868631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139459972597577486630579087 209189958896366229945868631)
        ·
          refine ⟨313784938344549344918802947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209189958896366229945868631 313784938344549344918802947)
          ·
            refine ⟨470677407516824017378204421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313784938344549344918802947 470677407516824017378204421)
            ·
              refine ⟨88252013909404503258413329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 470677407516824017378204421 88252013909404503258413329)
              ·
                refine ⟨66189010432053377443809997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88252013909404503258413329 66189010432053377443809997)
                ·
                  refine ⟨24820878912020016541428749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66189010432053377443809997 24820878912020016541428749)
                  ·
                    refine ⟨9307829592007506203035781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24820878912020016541428749 9307829592007506203035781)
                    ·
                      refine ⟨1745218048501407413069209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9307829592007506203035781 1745218048501407413069209)
                      ·
                        rfl

theorem cell23_3398800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_3398800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398800 prefixEnd_3398800 := by exact prefixLift 3398800
  have htrace : WordTrace (prefixWord ++ tailWord_3398800) baseStart_3398800 baseEnd_3398800 := by
    simpa [prefixWord, tailWord_3398800, baseEnd_3398800] using wordTrace_append hprefix tailTrace_3398800
  have hstable : (prefixWord ++ tailWord_3398800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398800).length < 2 ^ (prefixWord ++ tailWord_3398800).sum := by decide
  have hdescent : baseEnd_3398800 < baseStart_3398800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398807 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3398807 : Nat := 118140960795 + 3398807 * 2 ^ 59
def prefixEnd_3398807 : Nat := 4983230072969 + 3 ^ 40 * 3398807 * 2
def baseEnd_3398807 : Nat := 1745221642865988885681677

theorem tailTrace_3398807 : CollatzResearch.WordTrace tailWord_3398807 prefixEnd_3398807 1745221642865988885681677 := by
  unfold tailWord_3398807
  simp only [CollatzResearch.WordTrace]
  refine ⟨123964675397710183867130675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82643116931806789244753783 123964675397710183867130675)
  ·
    refine ⟨185947013096565275800696013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123964675397710183867130675 185947013096565275800696013)
    ·
      refine ⟨69730129911211978425261005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185947013096565275800696013 69730129911211978425261005)
      ·
        refine ⟨26148798716704491909472877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69730129911211978425261005 26148798716704491909472877)
        ·
          refine ⟨9805799518764184466052329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26148798716704491909472877 9805799518764184466052329)
          ·
            refine ⟨7354349639073138349539247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9805799518764184466052329 7354349639073138349539247)
            ·
              refine ⟨11031524458609707524308871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354349639073138349539247 11031524458609707524308871)
              ·
                refine ⟨16547286687914561286463307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031524458609707524308871 16547286687914561286463307)
                ·
                  refine ⟨24820930031871841929694961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16547286687914561286463307 24820930031871841929694961)
                  ·
                    refine ⟨18615697523903881447271221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24820930031871841929694961 18615697523903881447271221)
                    ·
                      refine ⟨1745221642865988885681677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18615697523903881447271221 1745221642865988885681677)
                      ·
                        rfl

theorem cell23_3398807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3398807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398807 prefixEnd_3398807 := by exact prefixLift 3398807
  have htrace : WordTrace (prefixWord ++ tailWord_3398807) baseStart_3398807 baseEnd_3398807 := by
    simpa [prefixWord, tailWord_3398807, baseEnd_3398807] using wordTrace_append hprefix tailTrace_3398807
  have hstable : (prefixWord ++ tailWord_3398807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398807).length < 2 ^ (prefixWord ++ tailWord_3398807).sum := by decide
  have hdescent : baseEnd_3398807 < baseStart_3398807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398817 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3398817 : Nat := 118140960795 + 3398817 * 2 ^ 59
def prefixEnd_3398817 : Nat := 4983230072969 + 3 ^ 40 * 3398817 * 2
def baseEnd_3398817 : Nat := 1745226777672533846556631

theorem tailTrace_3398817 : CollatzResearch.WordTrace tailWord_3398817 prefixEnd_3398817 1745226777672533846556631 := by
  unfold tailWord_3398817
  simp only [CollatzResearch.WordTrace]
  refine ⟨123965040127673955574994705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82643360085115970383329803 123965040127673955574994705)
  ·
    refine ⟨92973780095755466681246029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123965040127673955574994705 92973780095755466681246029)
    ·
      refine ⟨34865167535908300005467261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92973780095755466681246029 34865167535908300005467261)
      ·
        refine ⟨13074437825965612502050223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34865167535908300005467261 13074437825965612502050223)
        ·
          refine ⟨19611656738948418753075335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13074437825965612502050223 19611656738948418753075335)
          ·
            refine ⟨29417485108422628129613003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611656738948418753075335 29417485108422628129613003)
            ·
              refine ⟨44126227662633942194419505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29417485108422628129613003 44126227662633942194419505)
              ·
                refine ⟨33094670746975456645814629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44126227662633942194419505 33094670746975456645814629)
                ·
                  refine ⟨6205250765057898121090243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33094670746975456645814629 6205250765057898121090243)
                  ·
                    refine ⟨9307876147586847181635365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6205250765057898121090243 9307876147586847181635365)
                    ·
                      refine ⟨1745226777672533846556631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9307876147586847181635365 1745226777672533846556631)
                      ·
                        rfl

theorem cell23_3398817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3398817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398817 prefixEnd_3398817 := by exact prefixLift 3398817
  have htrace : WordTrace (prefixWord ++ tailWord_3398817) baseStart_3398817 baseEnd_3398817 := by
    simpa [prefixWord, tailWord_3398817, baseEnd_3398817] using wordTrace_append hprefix tailTrace_3398817
  have hstable : (prefixWord ++ tailWord_3398817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398817).length < 2 ^ (prefixWord ++ tailWord_3398817).sum := by decide
  have hdescent : baseEnd_3398817 < baseStart_3398817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398834 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_3398834 : Nat := 118140960795 + 3398834 * 2 ^ 59
def prefixEnd_3398834 : Nat := 4983230072969 + 3 ^ 40 * 3398834 * 2
def baseEnd_3398834 : Nat := 1745235506843660280044053

theorem tailTrace_3398834 : CollatzResearch.WordTrace tailWord_3398834 prefixEnd_3398834 1745235506843660280044053 := by
  unfold tailWord_3398834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991415042153091869590889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82643773445741578318909037 30991415042153091869590889)
  ·
    refine ⟨23243561281614818902193167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30991415042153091869590889 23243561281614818902193167)
    ·
      refine ⟨34865341922422228353289751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23243561281614818902193167 34865341922422228353289751)
      ·
        refine ⟨52298012883633342529934627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34865341922422228353289751 52298012883633342529934627)
        ·
          refine ⟨78447019325450013794901941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52298012883633342529934627 78447019325450013794901941)
          ·
            refine ⟨7354408061760938793272057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78447019325450013794901941 7354408061760938793272057)
            ·
              refine ⟨5515806046320704094954043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354408061760938793272057 5515806046320704094954043)
              ·
                refine ⟨8273709069481056142431065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515806046320704094954043 8273709069481056142431065)
                ·
                  refine ⟨6205281802110792106823299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273709069481056142431065 6205281802110792106823299)
                  ·
                    refine ⟨9307922703166188160234949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6205281802110792106823299 9307922703166188160234949)
                    ·
                      refine ⟨1745235506843660280044053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9307922703166188160234949 1745235506843660280044053)
                      ·
                        rfl

theorem cell23_3398834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_3398834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398834 prefixEnd_3398834 := by exact prefixLift 3398834
  have htrace : WordTrace (prefixWord ++ tailWord_3398834) baseStart_3398834 baseEnd_3398834 := by
    simpa [prefixWord, tailWord_3398834, baseEnd_3398834] using wordTrace_append hprefix tailTrace_3398834
  have hstable : (prefixWord ++ tailWord_3398834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398834).length < 2 ^ (prefixWord ++ tailWord_3398834).sum := by decide
  have hdescent : baseEnd_3398834 < baseStart_3398834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398840 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 8]
def baseStart_3398840 : Nat := 118140960795 + 3398840 * 2 ^ 59
def prefixEnd_3398840 : Nat := 4983230072969 + 3 ^ 40 * 3398840 * 2
def baseEnd_3398840 : Nat := 193915398636398584063225

theorem tailTrace_3398840 : CollatzResearch.WordTrace tailWord_3398840 prefixEnd_3398840 193915398636398584063225 := by
  unfold tailWord_3398840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61982939503295315251540987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82643919337727087002054649 61982939503295315251540987)
  ·
    refine ⟨92974409254942972877311481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61982939503295315251540987 92974409254942972877311481)
    ·
      refine ⟨69730806941207229657983611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92974409254942972877311481 69730806941207229657983611)
      ·
        refine ⟨104596210411810844486975417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69730806941207229657983611 104596210411810844486975417)
        ·
          refine ⟨78447157808858133365231563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104596210411810844486975417 78447157808858133365231563)
          ·
            refine ⟨117670736713287200047847345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78447157808858133365231563 117670736713287200047847345)
            ·
              refine ⟨88253052534965400035885509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117670736713287200047847345 88253052534965400035885509)
              ·
                refine ⟨16547447350306012506728533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88253052534965400035885509 16547447350306012506728533)
                ·
                  refine ⟨193915398636398584063225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16547447350306012506728533 193915398636398584063225)
                  ·
                    rfl

theorem cell23_3398840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_3398840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398840 prefixEnd_3398840 := by exact prefixLift 3398840
  have htrace : WordTrace (prefixWord ++ tailWord_3398840) baseStart_3398840 baseEnd_3398840 := by
    simpa [prefixWord, tailWord_3398840, baseEnd_3398840] using wordTrace_append hprefix tailTrace_3398840
  have hstable : (prefixWord ++ tailWord_3398840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398840).length < 2 ^ (prefixWord ++ tailWord_3398840).sum := by decide
  have hdescent : baseEnd_3398840 < baseStart_3398840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398868 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3398868 : Nat := 118140960795 + 3398868 * 2 ^ 59
def prefixEnd_3398868 : Nat := 4983230072969 + 3 ^ 40 * 3398868 * 2
def baseEnd_3398868 : Nat := 1745252965185913147018897

theorem tailTrace_3398868 : CollatzResearch.WordTrace tailWord_3398868 prefixEnd_3398868 1745252965185913147018897 := by
  unfold tailWord_3398868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61983450125244595642550629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82644600166992794190067505 61983450125244595642550629)
  ·
    refine ⟨11621896898483361682978243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61983450125244595642550629 11621896898483361682978243)
    ·
      refine ⟨17432845347725042524467365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11621896898483361682978243 17432845347725042524467365)
      ·
        refine ⟨3268658502698445473337631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17432845347725042524467365 3268658502698445473337631)
        ·
          refine ⟨4902987754047668210006447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268658502698445473337631 4902987754047668210006447)
          ·
            refine ⟨7354481631071502315009671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902987754047668210006447 7354481631071502315009671)
            ·
              refine ⟨11031722446607253472514507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354481631071502315009671 11031722446607253472514507)
              ·
                refine ⟨16547583669910880208771761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031722446607253472514507 16547583669910880208771761)
                ·
                  refine ⟨12410687752433160156578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16547583669910880208771761 12410687752433160156578821)
                  ·
                    refine ⟨2327003953581217529358529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12410687752433160156578821 2327003953581217529358529)
                    ·
                      refine ⟨1745252965185913147018897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327003953581217529358529 1745252965185913147018897)
                      ·
                        rfl

theorem cell23_3398868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3398868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398868 prefixEnd_3398868 := by exact prefixLift 3398868
  have htrace : WordTrace (prefixWord ++ tailWord_3398868) baseStart_3398868 baseEnd_3398868 := by
    simpa [prefixWord, tailWord_3398868, baseEnd_3398868] using wordTrace_append hprefix tailTrace_3398868
  have hstable : (prefixWord ++ tailWord_3398868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398868).length < 2 ^ (prefixWord ++ tailWord_3398868).sum := by decide
  have hdescent : baseEnd_3398868 < baseStart_3398868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398884 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_3398884 : Nat := 118140960795 + 3398884 * 2 ^ 59
def prefixEnd_3398884 : Nat := 4983230072969 + 3 ^ 40 * 3398884 * 2
def baseEnd_3398884 : Nat := 1745261180876385084418823

theorem tailTrace_3398884 : CollatzResearch.WordTrace tailWord_3398884 prefixEnd_3398884 1745261180876385084418823 := by
  unfold tailWord_3398884
  simp only [CollatzResearch.WordTrace]
  refine ⟨61983741909215613008841853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82644989212287484011789137 61983741909215613008841853)
  ·
    refine ⟨23243903215955854878315695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61983741909215613008841853 23243903215955854878315695)
    ·
      refine ⟨34865854823933782317473543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23243903215955854878315695 34865854823933782317473543)
      ·
        refine ⟨52298782235900673476210315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34865854823933782317473543 52298782235900673476210315)
        ·
          refine ⟨78448173353851010214315473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52298782235900673476210315 78448173353851010214315473)
          ·
            refine ⟨58836130015388257660736605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78448173353851010214315473 58836130015388257660736605)
            ·
              refine ⟨22063548755770596622776227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58836130015388257660736605 22063548755770596622776227)
              ·
                refine ⟨33095323133655894934164341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22063548755770596622776227 33095323133655894934164341)
                ·
                  refine ⟨3102686543780240150077907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33095323133655894934164341 3102686543780240150077907)
                  ·
                    refine ⟨4654029815670360225116861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3102686543780240150077907 4654029815670360225116861)
                    ·
                      refine ⟨1745261180876385084418823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4654029815670360225116861 1745261180876385084418823)
                      ·
                        rfl

theorem cell23_3398884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_3398884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398884 prefixEnd_3398884 := by exact prefixLift 3398884
  have htrace : WordTrace (prefixWord ++ tailWord_3398884) baseStart_3398884 baseEnd_3398884 := by
    simpa [prefixWord, tailWord_3398884, baseEnd_3398884] using wordTrace_append hprefix tailTrace_3398884
  have hstable : (prefixWord ++ tailWord_3398884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398884).length < 2 ^ (prefixWord ++ tailWord_3398884).sum := by decide
  have hdescent : baseEnd_3398884 < baseStart_3398884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398941 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3398941 : Nat := 118140960795 + 3398941 * 2 ^ 59
def prefixEnd_3398941 : Nat := 4983230072969 + 3 ^ 40 * 3398941 * 2
def baseEnd_3398941 : Nat := 1745290449273691361406061

theorem tailTrace_3398941 : CollatzResearch.WordTrace tailWord_3398941 prefixEnd_3398941 1745290449273691361406061 := by
  unfold tailWord_3398941
  simp only [CollatzResearch.WordTrace]
  refine ⟨123969562779224724752508677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82646375186149816501672451 123969562779224724752508677)
  ·
    refine ⟨23244293021104635891095377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123969562779224724752508677 23244293021104635891095377)
    ·
      refine ⟨17433219765828476918321533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23244293021104635891095377 17433219765828476918321533)
      ·
        refine ⟨6537457412185678844370575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17433219765828476918321533 6537457412185678844370575)
        ·
          refine ⟨9806186118278518266555863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537457412185678844370575 9806186118278518266555863)
          ·
            refine ⟨14709279177417777399833795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806186118278518266555863 14709279177417777399833795)
            ·
              refine ⟨22063918766126666099750693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709279177417777399833795 22063918766126666099750693)
              ·
                refine ⟨4136984768648749893703255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22063918766126666099750693 4136984768648749893703255)
                ·
                  refine ⟨6205477152973124840554883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136984768648749893703255 6205477152973124840554883)
                  ·
                    refine ⟨9308215729459687260832325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6205477152973124840554883 9308215729459687260832325)
                    ·
                      refine ⟨1745290449273691361406061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9308215729459687260832325 1745290449273691361406061)
                      ·
                        rfl

theorem cell23_3398941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3398941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398941 prefixEnd_3398941 := by exact prefixLift 3398941
  have htrace : WordTrace (prefixWord ++ tailWord_3398941) baseStart_3398941 baseEnd_3398941 := by
    simpa [prefixWord, tailWord_3398941, baseEnd_3398941] using wordTrace_append hprefix tailTrace_3398941
  have hstable : (prefixWord ++ tailWord_3398941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398941).length < 2 ^ (prefixWord ++ tailWord_3398941).sum := by decide
  have hdescent : baseEnd_3398941 < baseStart_3398941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398947 : List Nat := [1, 1, 1, 4, 2, 4, 1, 9]
def baseStart_3398947 : Nat := 118140960795 + 3398947 * 2 ^ 59
def prefixEnd_3398947 : Nat := 4983230072969 + 3 ^ 40 * 3398947 * 2
def baseEnd_3398947 : Nat := 64640501116948827330779

theorem tailTrace_3398947 : CollatzResearch.WordTrace tailWord_3398947 prefixEnd_3398947 64640501116948827330779 := by
  unfold tailWord_3398947
  simp only [CollatzResearch.WordTrace]
  refine ⟨123969781617202987777227095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82646521078135325184818063 123969781617202987777227095)
  ·
    refine ⟨185954672425804481665840643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123969781617202987777227095 185954672425804481665840643)
    ·
      refine ⟨278932008638706722498760965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185954672425804481665840643 278932008638706722498760965)
      ·
        refine ⟨52299751619757510468517681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278932008638706722498760965 52299751619757510468517681)
        ·
          refine ⟨39224813714818132851388261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52299751619757510468517681 39224813714818132851388261)
          ·
            refine ⟨7354652571528399909635299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39224813714818132851388261 7354652571528399909635299)
            ·
              refine ⟨11031978857292599864452949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354652571528399909635299 11031978857292599864452949)
              ·
                refine ⟨64640501116948827330779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11031978857292599864452949 64640501116948827330779)
                ·
                  rfl

theorem cell23_3398947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 9].length) (baseStart_3398947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398947 prefixEnd_3398947 := by exact prefixLift 3398947
  have htrace : WordTrace (prefixWord ++ tailWord_3398947) baseStart_3398947 baseEnd_3398947 := by
    simpa [prefixWord, tailWord_3398947, baseEnd_3398947] using wordTrace_append hprefix tailTrace_3398947
  have hstable : (prefixWord ++ tailWord_3398947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398947).length < 2 ^ (prefixWord ++ tailWord_3398947).sum := by decide
  have hdescent : baseEnd_3398947 < baseStart_3398947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398961 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3398961 : Nat := 118140960795 + 3398961 * 2 ^ 59
def prefixEnd_3398961 : Nat := 4983230072969 + 3 ^ 40 * 3398961 * 2
def baseEnd_3398961 : Nat := 1745300718886781283155969

theorem tailTrace_3398961 : CollatzResearch.WordTrace tailWord_3398961 prefixEnd_3398961 1745300718886781283155969 := by
  unfold tailWord_3398961
  simp only [CollatzResearch.WordTrace]
  refine ⟨123970292239152268168236737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82646861492768178778824491 123970292239152268168236737)
  ·
    refine ⟨92977719179364201126177553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123970292239152268168236737 92977719179364201126177553)
    ·
      refine ⟨69733289384523150844633165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92977719179364201126177553 69733289384523150844633165)
      ·
        refine ⟨26149983519196181566737437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69733289384523150844633165 26149983519196181566737437)
        ·
          refine ⟨9806243819698568087526539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26149983519196181566737437 9806243819698568087526539)
          ·
            refine ⟨14709365729547852131289809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806243819698568087526539 14709365729547852131289809)
            ·
              refine ⟨11032024297160889098467357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14709365729547852131289809 11032024297160889098467357)
              ·
                refine ⟨4137009111435333411925259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11032024297160889098467357 4137009111435333411925259)
                ·
                  refine ⟨6205513667153000117887889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137009111435333411925259 6205513667153000117887889)
                  ·
                    refine ⟨4654135250364750088415917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6205513667153000117887889 4654135250364750088415917)
                    ·
                      refine ⟨1745300718886781283155969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4654135250364750088415917 1745300718886781283155969)
                      ·
                        rfl

theorem cell23_3398961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3398961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398961 prefixEnd_3398961 := by exact prefixLift 3398961
  have htrace : WordTrace (prefixWord ++ tailWord_3398961) baseStart_3398961 baseEnd_3398961 := by
    simpa [prefixWord, tailWord_3398961, baseEnd_3398961] using wordTrace_append hprefix tailTrace_3398961
  have hstable : (prefixWord ++ tailWord_3398961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398961).length < 2 ^ (prefixWord ++ tailWord_3398961).sum := by decide
  have hdescent : baseEnd_3398961 < baseStart_3398961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3398984 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_3398984 : Nat := 118140960795 + 3398984 * 2 ^ 59
def prefixEnd_3398984 : Nat := 4983230072969 + 3 ^ 40 * 3398984 * 2
def baseEnd_3398984 : Nat := 1745312528941834693168363

theorem tailTrace_3398984 : CollatzResearch.WordTrace tailWord_3398984 prefixEnd_3398984 1745312528941834693168363 := by
  unfold tailWord_3398984
  simp only [CollatzResearch.WordTrace]
  refine ⟨61985565559034471548162003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82647420745379295397549337 61985565559034471548162003)
  ·
    refine ⟨92978348338551707322243005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61985565559034471548162003 92978348338551707322243005)
    ·
      refine ⟨34866880626956890245841127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92978348338551707322243005 34866880626956890245841127)
      ·
        refine ⟨52300320940435335368761691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34866880626956890245841127 52300320940435335368761691)
        ·
          refine ⟨78450481410653003053142537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52300320940435335368761691 78450481410653003053142537)
          ·
            refine ⟨58837861057989752289856903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78450481410653003053142537 58837861057989752289856903)
            ·
              refine ⟨88256791586984628434785355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58837861057989752289856903 88256791586984628434785355)
              ·
                refine ⟨132385187380476942652178033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88256791586984628434785355 132385187380476942652178033)
                ·
                  refine ⟨99288890535357706989133525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132385187380476942652178033 99288890535357706989133525)
                  ·
                    refine ⟨2327083371922446257557817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 99288890535357706989133525 2327083371922446257557817)
                    ·
                      refine ⟨1745312528941834693168363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327083371922446257557817 1745312528941834693168363)
                      ·
                        rfl

theorem cell23_3398984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_3398984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3398984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3398984 prefixEnd_3398984 := by exact prefixLift 3398984
  have htrace : WordTrace (prefixWord ++ tailWord_3398984) baseStart_3398984 baseEnd_3398984 := by
    simpa [prefixWord, tailWord_3398984, baseEnd_3398984] using wordTrace_append hprefix tailTrace_3398984
  have hstable : (prefixWord ++ tailWord_3398984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3398984).length < 2 ^ (prefixWord ++ tailWord_3398984).sum := by decide
  have hdescent : baseEnd_3398984 < baseStart_3398984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3398984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399005 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3399005 : Nat := 118140960795 + 3399005 * 2 ^ 59
def prefixEnd_3399005 : Nat := 4983230072969 + 3 ^ 40 * 3399005 * 2
def baseEnd_3399005 : Nat := 1745323312035579111005767

theorem tailTrace_3399005 : CollatzResearch.WordTrace tailWord_3399005 prefixEnd_3399005 1745323312035579111005767 := by
  unfold tailWord_3399005
  simp only [CollatzResearch.WordTrace]
  refine ⟨123971897050992863682838469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82647931367328575788558979 123971897050992863682838469)
  ·
    refine ⟨23244730697061161940532213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123971897050992863682838469 23244730697061161940532213)
    ·
      refine ⟨2179193502849483931924895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23244730697061161940532213 2179193502849483931924895)
      ·
        refine ⟨3268790254274225897887343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179193502849483931924895 3268790254274225897887343)
        ·
          refine ⟨4903185381411338846831015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268790254274225897887343 4903185381411338846831015)
          ·
            refine ⟨7354778072117008270246523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903185381411338846831015 7354778072117008270246523)
            ·
              refine ⟨11032167108175512405369785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354778072117008270246523 11032167108175512405369785)
              ·
                refine ⟨8274125331131634304027339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11032167108175512405369785 8274125331131634304027339)
                ·
                  refine ⟨12411187996697451456041009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274125331131634304027339 12411187996697451456041009)
                  ·
                    refine ⟨9308390997523088592030757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12411187996697451456041009 9308390997523088592030757)
                    ·
                      refine ⟨1745323312035579111005767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9308390997523088592030757 1745323312035579111005767)
                      ·
                        rfl

theorem cell23_3399005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3399005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399005 prefixEnd_3399005 := by exact prefixLift 3399005
  have htrace : WordTrace (prefixWord ++ tailWord_3399005) baseStart_3399005 baseEnd_3399005 := by
    simpa [prefixWord, tailWord_3399005, baseEnd_3399005] using wordTrace_append hprefix tailTrace_3399005
  have hstable : (prefixWord ++ tailWord_3399005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399005).length < 2 ^ (prefixWord ++ tailWord_3399005).sum := by decide
  have hdescent : baseEnd_3399005 < baseStart_3399005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399007 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 4, 6]
def baseStart_3399007 : Nat := 118140960795 + 3399007 * 2 ^ 59
def prefixEnd_3399007 : Nat := 4983230072969 + 3 ^ 40 * 3399007 * 2
def baseEnd_3399007 : Nat := 581774779665629367726919

theorem tailTrace_3399007 : CollatzResearch.WordTrace tailWord_3399007 prefixEnd_3399007 581774779665629367726919 := by
  unfold tailWord_3399007
  simp only [CollatzResearch.WordTrace]
  refine ⟨123971969996985618024411275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82647979997990412016274183 123971969996985618024411275)
  ·
    refine ⟨185957954995478427036616913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123971969996985618024411275 185957954995478427036616913)
    ·
      refine ⟨139468466246608820277462685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185957954995478427036616913 139468466246608820277462685)
      ·
        refine ⟨52300674842478307604048507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139468466246608820277462685 52300674842478307604048507)
        ·
          refine ⟨78451012263717461406072761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52300674842478307604048507 78451012263717461406072761)
          ·
            refine ⟨58838259197788096054554571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78451012263717461406072761 58838259197788096054554571)
            ·
              refine ⟨88257388796682144081831857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58838259197788096054554571 88257388796682144081831857)
              ·
                refine ⟨66193041597511608061373893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88257388796682144081831857 66193041597511608061373893)
                ·
                  refine ⟨12411195299533426511507605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66193041597511608061373893 12411195299533426511507605)
                  ·
                    refine ⟨581774779665629367726919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12411195299533426511507605 581774779665629367726919)
                    ·
                      rfl

theorem cell23_3399007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_3399007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399007 prefixEnd_3399007 := by exact prefixLift 3399007
  have htrace : WordTrace (prefixWord ++ tailWord_3399007) baseStart_3399007 baseEnd_3399007 := by
    simpa [prefixWord, tailWord_3399007, baseEnd_3399007] using wordTrace_append hprefix tailTrace_3399007
  have hstable : (prefixWord ++ tailWord_3399007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399007).length < 2 ^ (prefixWord ++ tailWord_3399007).sum := by decide
  have hdescent : baseEnd_3399007 < baseStart_3399007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399017 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_3399017 : Nat := 118140960795 + 3399017 * 2 ^ 59
def prefixEnd_3399017 : Nat := 4983230072969 + 3 ^ 40 * 3399017 * 2
def baseEnd_3399017 : Nat := 1745329473803433064055711

theorem tailTrace_3399017 : CollatzResearch.WordTrace tailWord_3399017 prefixEnd_3399017 1745329473803433064055711 := by
  unfold tailWord_3399017
  simp only [CollatzResearch.WordTrace]
  refine ⟨123972334726949389732275305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82648223151299593154850203 123972334726949389732275305)
  ·
    refine ⟨92979251045212042299206479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123972334726949389732275305 92979251045212042299206479)
    ·
      refine ⟨139468876567818063448809719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92979251045212042299206479 139468876567818063448809719)
      ·
        refine ⟨209203314851727095173214579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139468876567818063448809719 209203314851727095173214579)
        ·
          refine ⟨313804972277590642759821869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209203314851727095173214579 313804972277590642759821869)
          ·
            refine ⟨117676864604096491034933201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313804972277590642759821869 117676864604096491034933201)
            ·
              refine ⟨88257648453072368276199901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117676864604096491034933201 88257648453072368276199901)
              ·
                refine ⟨33096618169902138103574963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88257648453072368276199901 33096618169902138103574963)
                ·
                  refine ⟨49644927254853207155362445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33096618169902138103574963 49644927254853207155362445)
                  ·
                    refine ⟨18616847720569952683260917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49644927254853207155362445 18616847720569952683260917)
                    ·
                      refine ⟨1745329473803433064055711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18616847720569952683260917 1745329473803433064055711)
                      ·
                        rfl

theorem cell23_3399017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_3399017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399017 prefixEnd_3399017 := by exact prefixLift 3399017
  have htrace : WordTrace (prefixWord ++ tailWord_3399017) baseStart_3399017 baseEnd_3399017 := by
    simpa [prefixWord, tailWord_3399017, baseEnd_3399017] using wordTrace_append hprefix tailTrace_3399017
  have hstable : (prefixWord ++ tailWord_3399017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399017).length < 2 ^ (prefixWord ++ tailWord_3399017).sum := by decide
  have hdescent : baseEnd_3399017 < baseStart_3399017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399041 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3399041 : Nat := 118140960795 + 3399041 * 2 ^ 59
def prefixEnd_3399041 : Nat := 4983230072969 + 3 ^ 40 * 3399041 * 2
def baseEnd_3399041 : Nat := 581780599113046990051867

theorem tailTrace_3399041 : CollatzResearch.WordTrace tailWord_3399041 prefixEnd_3399041 581780599113046990051867 := by
  unfold tailWord_3399041
  simp only [CollatzResearch.WordTrace]
  refine ⟨123973210078862441831148977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82648806719241627887432651 123973210078862441831148977)
  ·
    refine ⟨92979907559146831373361733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123973210078862441831148977 92979907559146831373361733)
    ·
      refine ⟨17433732667340030882505325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92979907559146831373361733 17433732667340030882505325)
      ·
        refine ⟨6537649750252511580939497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17433732667340030882505325 6537649750252511580939497)
        ·
          refine ⟨4903237312689383685704623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6537649750252511580939497 4903237312689383685704623)
          ·
            refine ⟨7354855969034075528556935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903237312689383685704623 7354855969034075528556935)
            ·
              refine ⟨11032283953551113292835403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354855969034075528556935 11032283953551113292835403)
              ·
                refine ⟨16548425930326669939253105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11032283953551113292835403 16548425930326669939253105)
                ·
                  refine ⟨12411319447745002454439829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16548425930326669939253105 12411319447745002454439829)
                  ·
                    refine ⟨581780599113046990051867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12411319447745002454439829 581780599113046990051867)
                    ·
                      rfl

theorem cell23_3399041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3399041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399041 prefixEnd_3399041 := by exact prefixLift 3399041
  have htrace : WordTrace (prefixWord ++ tailWord_3399041) baseStart_3399041 baseEnd_3399041 := by
    simpa [prefixWord, tailWord_3399041, baseEnd_3399041] using wordTrace_append hprefix tailTrace_3399041
  have hstable : (prefixWord ++ tailWord_3399041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399041).length < 2 ^ (prefixWord ++ tailWord_3399041).sum := by decide
  have hdescent : baseEnd_3399041 < baseStart_3399041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399044 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3399044 : Nat := 118140960795 + 3399044 * 2 ^ 59
def prefixEnd_3399044 : Nat := 4983230072969 + 3 ^ 40 * 3399044 * 2
def baseEnd_3399044 : Nat := 1745343337781104458418087

theorem tailTrace_3399044 : CollatzResearch.WordTrace tailWord_3399044 prefixEnd_3399044 1745343337781104458418087 := by
  unfold tailWord_3399044
  simp only [CollatzResearch.WordTrace]
  refine ⟨61986659748925786671754093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82648879665234382229005457 61986659748925786671754093)
  ·
    refine ⟨23244997405847170001907785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61986659748925786671754093 23244997405847170001907785)
    ·
      refine ⟨17433748054385377501430839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23244997405847170001907785 17433748054385377501430839)
      ·
        refine ⟨26150622081578066252146259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433748054385377501430839 26150622081578066252146259)
        ·
          refine ⟨39225933122367099378219389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26150622081578066252146259 39225933122367099378219389)
          ·
            refine ⟨14709724920887662266832271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39225933122367099378219389 14709724920887662266832271)
            ·
              refine ⟨22064587381331493400248407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709724920887662266832271 22064587381331493400248407)
              ·
                refine ⟨33096881071997240100372611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22064587381331493400248407 33096881071997240100372611)
                ·
                  refine ⟨49645321607995860150558917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33096881071997240100372611 49645321607995860150558917)
                  ·
                    refine ⟨9308497801499223778229797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49645321607995860150558917 9308497801499223778229797)
                    ·
                      refine ⟨1745343337781104458418087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9308497801499223778229797 1745343337781104458418087)
                      ·
                        rfl

theorem cell23_3399044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3399044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399044 prefixEnd_3399044 := by exact prefixLift 3399044
  have htrace : WordTrace (prefixWord ++ tailWord_3399044) baseStart_3399044 baseEnd_3399044 := by
    simpa [prefixWord, tailWord_3399044, baseEnd_3399044] using wordTrace_append hprefix tailTrace_3399044
  have hstable : (prefixWord ++ tailWord_3399044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399044).length < 2 ^ (prefixWord ++ tailWord_3399044).sum := by decide
  have hdescent : baseEnd_3399044 < baseStart_3399044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399048 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_3399048 : Nat := 118140960795 + 3399048 * 2 ^ 59
def prefixEnd_3399048 : Nat := 4983230072969 + 3 ^ 40 * 3399048 * 2
def baseEnd_3399048 : Nat := 1745345391703722442768069

theorem tailTrace_3399048 : CollatzResearch.WordTrace tailWord_3399048 prefixEnd_3399048 1745345391703722442768069 := by
  unfold tailWord_3399048
  simp only [CollatzResearch.WordTrace]
  refine ⟨61986732694918541013326899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82648976926558054684435865 61986732694918541013326899)
  ·
    refine ⟨92980099042377811519990349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61986732694918541013326899 92980099042377811519990349)
    ·
      refine ⟨34867537140891679319996381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92980099042377811519990349 34867537140891679319996381)
      ·
        refine ⟨13075326427834379744998643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34867537140891679319996381 13075326427834379744998643)
        ·
          refine ⟨19612989641751569617497965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075326427834379744998643 19612989641751569617497965)
          ·
            refine ⟨7354871115656838606561737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19612989641751569617497965 7354871115656838606561737)
            ·
              refine ⟨5516153336742628954921303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354871115656838606561737 5516153336742628954921303)
              ·
                refine ⟨8274230005113943432381955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516153336742628954921303 8274230005113943432381955)
                ·
                  refine ⟨12411345007670915148572933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274230005113943432381955 12411345007670915148572933)
                  ·
                    refine ⟨2327127188938296590357425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12411345007670915148572933 2327127188938296590357425)
                    ·
                      refine ⟨1745345391703722442768069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327127188938296590357425 1745345391703722442768069)
                      ·
                        rfl

theorem cell23_3399048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_3399048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399048 prefixEnd_3399048 := by exact prefixLift 3399048
  have htrace : WordTrace (prefixWord ++ tailWord_3399048) baseStart_3399048 baseEnd_3399048 := by
    simpa [prefixWord, tailWord_3399048, baseEnd_3399048] using wordTrace_append hprefix tailTrace_3399048
  have hstable : (prefixWord ++ tailWord_3399048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399048).length < 2 ^ (prefixWord ++ tailWord_3399048).sum := by decide
  have hdescent : baseEnd_3399048 < baseStart_3399048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399057 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3399057 : Nat := 118140960795 + 3399057 * 2 ^ 59
def prefixEnd_3399057 : Nat := 4983230072969 + 3 ^ 40 * 3399057 * 2
def baseEnd_3399057 : Nat := 1745350013029612907555527

theorem tailTrace_3399057 : CollatzResearch.WordTrace tailWord_3399057 prefixEnd_3399057 1745350013029612907555527 := by
  unfold tailWord_3399057
  simp only [CollatzResearch.WordTrace]
  refine ⟨123973793646804476563731425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82649195764536317709154283 123973793646804476563731425)
  ·
    refine ⟨92980345235103357422798569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123973793646804476563731425 92980345235103357422798569)
    ·
      refine ⟨69735258926327518067098927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92980345235103357422798569 69735258926327518067098927)
      ·
        refine ⟨104602888389491277100648391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69735258926327518067098927 104602888389491277100648391)
        ·
          refine ⟨156904332584236915650972587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104602888389491277100648391 156904332584236915650972587)
          ·
            refine ⟨235356498876355373476458881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156904332584236915650972587 235356498876355373476458881)
            ·
              refine ⟨176517374157266530107344161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235356498876355373476458881 176517374157266530107344161)
              ·
                refine ⟨132388030617949897580508121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176517374157266530107344161 132388030617949897580508121)
                ·
                  refine ⟨99291022963462423185381091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132388030617949897580508121 99291022963462423185381091)
                  ·
                    refine ⟨148936534445193634778071637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99291022963462423185381091 148936534445193634778071637)
                    ·
                      refine ⟨1745350013029612907555527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148936534445193634778071637 1745350013029612907555527)
                      ·
                        rfl

theorem cell23_3399057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3399057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399057 prefixEnd_3399057 := by exact prefixLift 3399057
  have htrace : WordTrace (prefixWord ++ tailWord_3399057) baseStart_3399057 baseEnd_3399057 := by
    simpa [prefixWord, tailWord_3399057, baseEnd_3399057] using wordTrace_append hprefix tailTrace_3399057
  have hstable : (prefixWord ++ tailWord_3399057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399057).length < 2 ^ (prefixWord ++ tailWord_3399057).sum := by decide
  have hdescent : baseEnd_3399057 < baseStart_3399057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399067 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 7]
def baseStart_3399067 : Nat := 118140960795 + 3399067 * 2 ^ 59
def prefixEnd_3399067 : Nat := 4983230072969 + 3 ^ 40 * 3399067 * 2
def baseEnd_3399067 : Nat := 581785049278719289476827

theorem tailTrace_3399067 : CollatzResearch.WordTrace tailWord_3399067 prefixEnd_3399067 581785049278719289476827 := by
  unfold tailWord_3399067
  simp only [CollatzResearch.WordTrace]
  refine ⟨123974158376768248271595455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82649438917845498847730303 123974158376768248271595455)
  ·
    refine ⟨185961237565152372407393183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123974158376768248271595455 185961237565152372407393183)
    ·
      refine ⟨278941856347728558611089775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185961237565152372407393183 278941856347728558611089775)
      ·
        refine ⟨418412784521592837916634663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278941856347728558611089775 418412784521592837916634663)
        ·
          refine ⟨627619176782389256874951995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418412784521592837916634663 627619176782389256874951995)
          ·
            refine ⟨941428765173583885312427993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627619176782389256874951995 941428765173583885312427993)
            ·
              refine ⟨706071573880187913984320995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941428765173583885312427993 706071573880187913984320995)
              ·
                refine ⟨1059107360820281870976481493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706071573880187913984320995 1059107360820281870976481493)
                ·
                  refine ⟨24822828769225356351011285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1059107360820281870976481493 24822828769225356351011285)
                  ·
                    refine ⟨581785049278719289476827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24822828769225356351011285 581785049278719289476827)
                    ·
                      rfl

theorem cell23_3399067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_3399067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399067 prefixEnd_3399067 := by exact prefixLift 3399067
  have htrace : WordTrace (prefixWord ++ tailWord_3399067) baseStart_3399067 baseEnd_3399067 := by
    simpa [prefixWord, tailWord_3399067, baseEnd_3399067] using wordTrace_append hprefix tailTrace_3399067
  have hstable : (prefixWord ++ tailWord_3399067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399067).length < 2 ^ (prefixWord ++ tailWord_3399067).sum := by decide
  have hdescent : baseEnd_3399067 < baseStart_3399067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399071 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 5]
def baseStart_3399071 : Nat := 118140960795 + 3399071 * 2 ^ 59
def prefixEnd_3399071 : Nat := 4983230072969 + 3 ^ 40 * 3399071 * 2
def baseEnd_3399071 : Nat := 193928577973197316975607

theorem tailTrace_3399071 : CollatzResearch.WordTrace tailWord_3399071 prefixEnd_3399071 193928577973197316975607 := by
  unfold tailWord_3399071
  simp only [CollatzResearch.WordTrace]
  refine ⟨123974304268753756954741067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82649536179169171303160711 123974304268753756954741067)
  ·
    refine ⟨185961456403130635432111601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123974304268753756954741067 185961456403130635432111601)
    ·
      refine ⟨139471092302347976574083701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185961456403130635432111601 139471092302347976574083701)
      ·
        refine ⟨13075414903345122803820347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139471092302347976574083701 13075414903345122803820347)
        ·
          refine ⟨19613122355017684205730521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075414903345122803820347 19613122355017684205730521)
          ·
            refine ⟨14709841766263263154297891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19613122355017684205730521 14709841766263263154297891)
            ·
              refine ⟨22064762649394894731446837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709841766263263154297891 22064762649394894731446837)
              ·
                refine ⟨2068571498380771381073141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22064762649394894731446837 2068571498380771381073141)
                ·
                  refine ⟨193928577973197316975607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068571498380771381073141 193928577973197316975607)
                  ·
                    rfl

theorem cell23_3399071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 5].length) (baseStart_3399071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399071 prefixEnd_3399071 := by exact prefixLift 3399071
  have htrace : WordTrace (prefixWord ++ tailWord_3399071) baseStart_3399071 baseEnd_3399071 := by
    simpa [prefixWord, tailWord_3399071, baseEnd_3399071] using wordTrace_append hprefix tailTrace_3399071
  have hstable : (prefixWord ++ tailWord_3399071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399071).length < 2 ^ (prefixWord ++ tailWord_3399071).sum := by decide
  have hdescent : baseEnd_3399071 < baseStart_3399071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399084 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_3399084 : Nat := 118140960795 + 3399084 * 2 ^ 59
def prefixEnd_3399084 : Nat := 4983230072969 + 3 ^ 40 * 3399084 * 2
def baseEnd_3399084 : Nat := 581787959002428100639301

theorem tailTrace_3399084 : CollatzResearch.WordTrace tailWord_3399084 prefixEnd_3399084 581787959002428100639301 := by
  unfold tailWord_3399084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61987389208853330087482153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82649852278471106783309537 61987389208853330087482153)
  ·
    refine ⟨46490541906639997565611615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61987389208853330087482153 46490541906639997565611615)
    ·
      refine ⟨69735812859959996348417423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46490541906639997565611615 69735812859959996348417423)
      ·
        refine ⟨104603719289939994522626135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69735812859959996348417423 104603719289939994522626135)
        ·
          refine ⟨156905578934909991783939203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104603719289939994522626135 156905578934909991783939203)
          ·
            refine ⟨235358368402364987675908805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156905578934909991783939203 235358368402364987675908805)
            ·
              refine ⟨44129694075443435189232901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235358368402364987675908805 44129694075443435189232901)
              ·
                refine ⟨8274317639145644097981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44129694075443435189232901 8274317639145644097981169)
                ·
                  refine ⟨6205738229359233073485877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8274317639145644097981169 6205738229359233073485877)
                  ·
                    refine ⟨581787959002428100639301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6205738229359233073485877 581787959002428100639301)
                    ·
                      rfl

theorem cell23_3399084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_3399084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399084 prefixEnd_3399084 := by exact prefixLift 3399084
  have htrace : WordTrace (prefixWord ++ tailWord_3399084) baseStart_3399084 baseEnd_3399084 := by
    simpa [prefixWord, tailWord_3399084, baseEnd_3399084] using wordTrace_append hprefix tailTrace_3399084
  have hstable : (prefixWord ++ tailWord_3399084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399084).length < 2 ^ (prefixWord ++ tailWord_3399084).sum := by decide
  have hdescent : baseEnd_3399084 < baseStart_3399084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399104 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_3399104 : Nat := 118140960795 + 3399104 * 2 ^ 59
def prefixEnd_3399104 : Nat := 4983230072969 + 3 ^ 40 * 3399104 * 2
def baseEnd_3399104 : Nat := 1745374146620374223667811

theorem tailTrace_3399104 : CollatzResearch.WordTrace tailWord_3399104 prefixEnd_3399104 1745374146620374223667811 := by
  unfold tailWord_3399104
  simp only [CollatzResearch.WordTrace]
  refine ⟨61987753938817101795346183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82650338585089469060461577 61987753938817101795346183)
  ·
    refine ⟨92981630908225652693019275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61987753938817101795346183 92981630908225652693019275)
    ·
      refine ⟨139472446362338479039528913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92981630908225652693019275 139472446362338479039528913)
      ·
        refine ⟨104604334771753859279646685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139472446362338479039528913 104604334771753859279646685)
        ·
          refine ⟨39226625539407697229867507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104604334771753859279646685 39226625539407697229867507)
          ·
            refine ⟨58839938309111545844801261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39226625539407697229867507 58839938309111545844801261)
            ·
              refine ⟨22064976865916829691800473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58839938309111545844801261 22064976865916829691800473)
              ·
                refine ⟨16548732649437622268850355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22064976865916829691800473 16548732649437622268850355)
                ·
                  refine ⟨24823098974156433403275533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16548732649437622268850355 24823098974156433403275533)
                  ·
                    refine ⟨9308662115308662526228325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24823098974156433403275533 9308662115308662526228325)
                    ·
                      refine ⟨1745374146620374223667811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9308662115308662526228325 1745374146620374223667811)
                      ·
                        rfl

theorem cell23_3399104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_3399104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399104 prefixEnd_3399104 := by exact prefixLift 3399104
  have htrace : WordTrace (prefixWord ++ tailWord_3399104) baseStart_3399104 baseEnd_3399104 := by
    simpa [prefixWord, tailWord_3399104, baseEnd_3399104] using wordTrace_append hprefix tailTrace_3399104
  have hstable : (prefixWord ++ tailWord_3399104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399104).length < 2 ^ (prefixWord ++ tailWord_3399104).sum := by decide
  have hdescent : baseEnd_3399104 < baseStart_3399104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399144 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 8]
def baseStart_3399144 : Nat := 118140960795 + 3399144 * 2 ^ 59
def prefixEnd_3399144 : Nat := 4983230072969 + 3 ^ 40 * 3399144 * 2
def baseEnd_3399144 : Nat := 193932742871839340796403

theorem tailTrace_3399144 : CollatzResearch.WordTrace tailWord_3399144 prefixEnd_3399144 193932742871839340796403 := by
  unfold tailWord_3399144
  simp only [CollatzResearch.WordTrace]
  refine ⟨61988483398744645211074243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82651311198326193614765657 61988483398744645211074243)
  ·
    refine ⟨92982725098116967816611365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61988483398744645211074243 92982725098116967816611365)
    ·
      refine ⟨17434260955896931465614631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92982725098116967816611365 17434260955896931465614631)
      ·
        refine ⟨26151391433845397198421947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17434260955896931465614631 26151391433845397198421947)
        ·
          refine ⟨39227087150768095797632921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26151391433845397198421947 39227087150768095797632921)
          ·
            refine ⟨29420315363076071848224691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39227087150768095797632921 29420315363076071848224691)
            ·
              refine ⟨44130473044614107772337037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29420315363076071848224691 44130473044614107772337037)
              ·
                refine ⟨16548927391730290414626389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44130473044614107772337037 16548927391730290414626389)
                ·
                  refine ⟨193932742871839340796403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16548927391730290414626389 193932742871839340796403)
                  ·
                    rfl

theorem cell23_3399144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_3399144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399144 prefixEnd_3399144 := by exact prefixLift 3399144
  have htrace : WordTrace (prefixWord ++ tailWord_3399144) baseStart_3399144 baseEnd_3399144 := by
    simpa [prefixWord, tailWord_3399144, baseEnd_3399144] using wordTrace_append hprefix tailTrace_3399144
  have hstable : (prefixWord ++ tailWord_3399144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399144).length < 2 ^ (prefixWord ++ tailWord_3399144).sum := by decide
  have hdescent : baseEnd_3399144 < baseStart_3399144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399164 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3399164 : Nat := 118140960795 + 3399164 * 2 ^ 59
def prefixEnd_3399164 : Nat := 4983230072969 + 3 ^ 40 * 3399164 * 2
def baseEnd_3399164 : Nat := 1745404955459643988917535

theorem tailTrace_3399164 : CollatzResearch.WordTrace tailWord_3399164 prefixEnd_3399164 1745404955459643988917535 := by
  unfold tailWord_3399164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61988848128708416918938273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82651797504944555891917697 61988848128708416918938273)
  ·
    refine ⟨46491636096531312689203705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61988848128708416918938273 46491636096531312689203705)
    ·
      refine ⟨34868727072398484516902779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46491636096531312689203705 34868727072398484516902779)
      ·
        refine ⟨52303090608597726775354169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34868727072398484516902779 52303090608597726775354169)
        ·
          refine ⟨39227317956448295081515627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52303090608597726775354169 39227317956448295081515627)
          ·
            refine ⟨58840976934672442622273441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39227317956448295081515627 58840976934672442622273441)
            ·
              refine ⟨44130732701004331966705081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58840976934672442622273441 44130732701004331966705081)
              ·
                refine ⟨33098049525753248975028811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44130732701004331966705081 33098049525753248975028811)
                ·
                  refine ⟨49647074288629873462543217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33098049525753248975028811 49647074288629873462543217)
                  ·
                    refine ⟨37235305716472405096907413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49647074288629873462543217 37235305716472405096907413)
                    ·
                      refine ⟨1745404955459643988917535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37235305716472405096907413 1745404955459643988917535)
                      ·
                        rfl

theorem cell23_3399164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3399164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399164 prefixEnd_3399164 := by exact prefixLift 3399164
  have htrace : WordTrace (prefixWord ++ tailWord_3399164) baseStart_3399164 baseEnd_3399164 := by
    simpa [prefixWord, tailWord_3399164, baseEnd_3399164] using wordTrace_append hprefix tailTrace_3399164
  have hstable : (prefixWord ++ tailWord_3399164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399164).length < 2 ^ (prefixWord ++ tailWord_3399164).sum := by decide
  have hdescent : baseEnd_3399164 < baseStart_3399164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399211 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 6, 2]
def baseStart_3399211 : Nat := 118140960795 + 3399211 * 2 ^ 59
def prefixEnd_3399211 : Nat := 4983230072969 + 3 ^ 40 * 3399211 * 2
def baseEnd_3399211 : Nat := 1745429089050405305029819

theorem tailTrace_3399211 : CollatzResearch.WordTrace tailWord_3399211 prefixEnd_3399211 1745429089050405305029819 := by
  unfold tailWord_3399211
  simp only [CollatzResearch.WordTrace]
  refine ⟨123979410488246560864837487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82652940325497707243224991 123979410488246560864837487)
  ·
    refine ⟨185969115732369841297256231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123979410488246560864837487 185969115732369841297256231)
    ·
      refine ⟨278953673598554761945884347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185969115732369841297256231 278953673598554761945884347)
      ·
        refine ⟨418430510397832142918826521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278953673598554761945884347 418430510397832142918826521)
        ·
          refine ⟨313822882798374107189119891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418430510397832142918826521 313822882798374107189119891)
          ·
            refine ⟨470734324197561160783679837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313822882798374107189119891 470734324197561160783679837)
            ·
              refine ⟨176525371574085435293879939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470734324197561160783679837 176525371574085435293879939)
              ·
                refine ⟨264788057361128152940819909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176525371574085435293879939 264788057361128152940819909)
                ·
                  refine ⟨49647760755211528676403733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264788057361128152940819909 49647760755211528676403733)
                  ·
                    refine ⟨2327238785400540406706425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49647760755211528676403733 2327238785400540406706425)
                    ·
                      refine ⟨1745429089050405305029819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327238785400540406706425 1745429089050405305029819)
                      ·
                        rfl

theorem cell23_3399211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6, 2].length) (baseStart_3399211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399211 prefixEnd_3399211 := by exact prefixLift 3399211
  have htrace : WordTrace (prefixWord ++ tailWord_3399211) baseStart_3399211 baseEnd_3399211 := by
    simpa [prefixWord, tailWord_3399211, baseEnd_3399211] using wordTrace_append hprefix tailTrace_3399211
  have hstable : (prefixWord ++ tailWord_3399211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399211).length < 2 ^ (prefixWord ++ tailWord_3399211).sum := by decide
  have hdescent : baseEnd_3399211 < baseStart_3399211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399221 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3399221 : Nat := 118140960795 + 3399221 * 2 ^ 59
def prefixEnd_3399221 : Nat := 4983230072969 + 3 ^ 40 * 3399221 * 2
def baseEnd_3399221 : Nat := 581811407952316755301591

theorem tailTrace_3399221 : CollatzResearch.WordTrace tailWord_3399221 prefixEnd_3399221 581811407952316755301591 := by
  unfold tailWord_3399221
  simp only [CollatzResearch.WordTrace]
  refine ⟨123979775218210332572701517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82653183478806888381801011 123979775218210332572701517)
  ·
    refine ⟨46492415706828874714763069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123979775218210332572701517 46492415706828874714763069)
    ·
      refine ⟨17434655890060828018036151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46492415706828874714763069 17434655890060828018036151)
      ·
        refine ⟨26151983835091242027054227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17434655890060828018036151 26151983835091242027054227)
        ·
          refine ⟨39227975752636863040581341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26151983835091242027054227 39227975752636863040581341)
          ·
            refine ⟨14710490907238823640218003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39227975752636863040581341 14710490907238823640218003)
            ·
              refine ⟨22065736360858235460327005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14710490907238823640218003 22065736360858235460327005)
              ·
                refine ⟨8274651135321838297622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22065736360858235460327005 8274651135321838297622627)
                ·
                  refine ⟨12411976702982757446433941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274651135321838297622627 12411976702982757446433941)
                  ·
                    refine ⟨581811407952316755301591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12411976702982757446433941 581811407952316755301591)
                    ·
                      rfl

theorem cell23_3399221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3399221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399221 prefixEnd_3399221 := by exact prefixLift 3399221
  have htrace : WordTrace (prefixWord ++ tailWord_3399221) baseStart_3399221 baseEnd_3399221 := by
    simpa [prefixWord, tailWord_3399221, baseEnd_3399221] using wordTrace_append hprefix tailTrace_3399221
  have hstable : (prefixWord ++ tailWord_3399221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399221).length < 2 ^ (prefixWord ++ tailWord_3399221).sum := by decide
  have hdescent : baseEnd_3399221 < baseStart_3399221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399222 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3399222 : Nat := 118140960795 + 3399222 * 2 ^ 59
def prefixEnd_3399222 : Nat := 4983230072969 + 3 ^ 40 * 3399222 * 2
def baseEnd_3399222 : Nat := 1745434737337604761992269

theorem tailTrace_3399222 : CollatzResearch.WordTrace tailWord_3399222 prefixEnd_3399222 1745434737337604761992269 := by
  unfold tailWord_3399222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748738230700419358967995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82653207794137806495658613 7748738230700419358967995)
  ·
    refine ⟨11623107346050629038451993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748738230700419358967995 11623107346050629038451993)
    ·
      refine ⟨8717330509537971778838995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11623107346050629038451993 8717330509537971778838995)
      ·
        refine ⟨13075995764306957668258493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717330509537971778838995 13075995764306957668258493)
        ·
          refine ⟨4903498411615109125596935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13075995764306957668258493 4903498411615109125596935)
          ·
            refine ⟨7355247617422663688395403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903498411615109125596935 7355247617422663688395403)
            ·
              refine ⟨11032871426133995532593105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355247617422663688395403 11032871426133995532593105)
              ·
                refine ⟨8274653569600496649444829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11032871426133995532593105 8274653569600496649444829)
                ·
                  refine ⟨3102995088600186243541811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8274653569600496649444829 3102995088600186243541811)
                  ·
                    refine ⟨4654492632900279365312717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3102995088600186243541811 4654492632900279365312717)
                    ·
                      refine ⟨1745434737337604761992269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4654492632900279365312717 1745434737337604761992269)
                      ·
                        rfl

theorem cell23_3399222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3399222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399222 prefixEnd_3399222 := by exact prefixLift 3399222
  have htrace : WordTrace (prefixWord ++ tailWord_3399222) baseStart_3399222 baseEnd_3399222 := by
    simpa [prefixWord, tailWord_3399222, baseEnd_3399222] using wordTrace_append hprefix tailTrace_3399222
  have hstable : (prefixWord ++ tailWord_3399222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399222).length < 2 ^ (prefixWord ++ tailWord_3399222).sum := by decide
  have hdescent : baseEnd_3399222 < baseStart_3399222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399248 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_3399248 : Nat := 118140960795 + 3399248 * 2 ^ 59
def prefixEnd_3399248 : Nat := 4983230072969 + 3 ^ 40 * 3399248 * 2
def baseEnd_3399248 : Nat := 1745448087834621660267149

theorem tailTrace_3399248 : CollatzResearch.WordTrace tailWord_3399248 prefixEnd_3399248 1745448087834621660267149 := by
  unfold tailWord_3399248
  simp only [CollatzResearch.WordTrace]
  refine ⟨61990379994556258091967199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82653839992741677455956265 61990379994556258091967199)
  ·
    refine ⟨92985569991834387137950799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61990379994556258091967199 92985569991834387137950799)
    ·
      refine ⟨139478354987751580706926199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92985569991834387137950799 139478354987751580706926199)
      ·
        refine ⟨209217532481627371060389299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139478354987751580706926199 209217532481627371060389299)
        ·
          refine ⟨313826298722441056590583949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209217532481627371060389299 313826298722441056590583949)
          ·
            refine ⟨117684862020915396221468981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313826298722441056590583949 117684862020915396221468981)
            ·
              refine ⟨11032955814460818395762717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117684862020915396221468981 11032955814460818395762717)
              ·
                refine ⟨4137358430422806898411019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11032955814460818395762717 4137358430422806898411019)
                ·
                  refine ⟨6206037645634210347616529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137358430422806898411019 6206037645634210347616529)
                  ·
                    refine ⟨4654528234225657760712397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6206037645634210347616529 4654528234225657760712397)
                    ·
                      refine ⟨1745448087834621660267149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4654528234225657760712397 1745448087834621660267149)
                      ·
                        rfl

theorem cell23_3399248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_3399248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399248 prefixEnd_3399248 := by exact prefixLift 3399248
  have htrace : WordTrace (prefixWord ++ tailWord_3399248) baseStart_3399248 baseEnd_3399248 := by
    simpa [prefixWord, tailWord_3399248, baseEnd_3399248] using wordTrace_append hprefix tailTrace_3399248
  have hstable : (prefixWord ++ tailWord_3399248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399248).length < 2 ^ (prefixWord ++ tailWord_3399248).sum := by decide
  have hdescent : baseEnd_3399248 < baseStart_3399248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399255 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 2, 4]
def baseStart_3399255 : Nat := 118140960795 + 3399255 * 2 ^ 59
def prefixEnd_3399255 : Nat := 4983230072969 + 3 ^ 40 * 3399255 * 2
def baseEnd_3399255 : Nat := 581817227399734377626539

theorem tailTrace_3399255 : CollatzResearch.WordTrace tailWord_3399255 prefixEnd_3399255 581817227399734377626539 := by
  unfold tailWord_3399255
  simp only [CollatzResearch.WordTrace]
  refine ⟨123981015300087156379439219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82654010200058104252959479 123981015300087156379439219)
  ·
    refine ⟨185971522950130734569158829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123981015300087156379439219 185971522950130734569158829)
    ·
      refine ⟨69739321106299025463434561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185971522950130734569158829 69739321106299025463434561)
      ·
        refine ⟨52304490829724269097575921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69739321106299025463434561 52304490829724269097575921)
        ·
          refine ⟨39228368122293201823181941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52304490829724269097575921 39228368122293201823181941)
          ·
            refine ⟨3677659511464987670923307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39228368122293201823181941 3677659511464987670923307)
            ·
              refine ⟨5516489267197481506384961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677659511464987670923307 5516489267197481506384961)
              ·
                refine ⟨4137366950398111129788721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516489267197481506384961 4137366950398111129788721)
                ·
                  refine ⟨3103025212798583347341541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137366950398111129788721 3103025212798583347341541)
                  ·
                    refine ⟨581817227399734377626539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103025212798583347341541 581817227399734377626539)
                    ·
                      rfl

theorem cell23_3399255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_3399255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399255 prefixEnd_3399255 := by exact prefixLift 3399255
  have htrace : WordTrace (prefixWord ++ tailWord_3399255) baseStart_3399255 baseEnd_3399255 := by
    simpa [prefixWord, tailWord_3399255, baseEnd_3399255] using wordTrace_append hprefix tailTrace_3399255
  have hstable : (prefixWord ++ tailWord_3399255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399255).length < 2 ^ (prefixWord ++ tailWord_3399255).sum := by decide
  have hdescent : baseEnd_3399255 < baseStart_3399255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399272 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 2, 4]
def baseStart_3399272 : Nat := 118140960795 + 3399272 * 2 ^ 59
def prefixEnd_3399272 : Nat := 4983230072969 + 3 ^ 40 * 3399272 * 2
def baseEnd_3399272 : Nat := 581820137123443188789013

theorem tailTrace_3399272 : CollatzResearch.WordTrace tailWord_3399272 prefixEnd_3399272 581820137123443188789013 := by
  unfold tailWord_3399272
  simp only [CollatzResearch.WordTrace]
  refine ⟨61990817670512784141404035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82654423560683712188538713 61990817670512784141404035)
  ·
    refine ⟨92986226505769176212106053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61990817670512784141404035 92986226505769176212106053)
    ·
      refine ⟨17434917469831720539769885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92986226505769176212106053 17434917469831720539769885)
      ·
        refine ⟨6538094051186895202413707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17434917469831720539769885 6538094051186895202413707)
        ·
          refine ⟨9807141076780342803620561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538094051186895202413707 9807141076780342803620561)
          ·
            refine ⟨7355355807585257102715421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9807141076780342803620561 7355355807585257102715421)
            ·
              refine ⟨2758258427844471413518283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7355355807585257102715421 2758258427844471413518283)
              ·
                refine ⟨4137387641766707120277425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758258427844471413518283 4137387641766707120277425)
                ·
                  refine ⟨3103040731325030340208069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137387641766707120277425 3103040731325030340208069)
                  ·
                    refine ⟨581820137123443188789013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103040731325030340208069 581820137123443188789013)
                    ·
                      rfl

theorem cell23_3399272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_3399272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399272 prefixEnd_3399272 := by exact prefixLift 3399272
  have htrace : WordTrace (prefixWord ++ tailWord_3399272) baseStart_3399272 baseEnd_3399272 := by
    simpa [prefixWord, tailWord_3399272, baseEnd_3399272] using wordTrace_append hprefix tailTrace_3399272
  have hstable : (prefixWord ++ tailWord_3399272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399272).length < 2 ^ (prefixWord ++ tailWord_3399272).sum := by decide
  have hdescent : baseEnd_3399272 < baseStart_3399272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399285 : List Nat := [1, 3, 4, 2, 1, 3, 2, 7]
def baseStart_3399285 : Nat := 118140960795 + 3399285 * 2 ^ 59
def prefixEnd_3399285 : Nat := 4983230072969 + 3 ^ 40 * 3399285 * 2
def baseEnd_3399285 : Nat := 64646929134031037611277

theorem tailTrace_3399285 : CollatzResearch.WordTrace tailWord_3399285 prefixEnd_3399285 64646929134031037611277 := by
  unfold tailWord_3399285
  simp only [CollatzResearch.WordTrace]
  refine ⟨123982109489978471503031309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82654739659985647668687539 123982109489978471503031309)
  ·
    refine ⟨46493291058741926813636741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123982109489978471503031309 46493291058741926813636741)
    ·
      refine ⟨8717492073514111277556889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46493291058741926813636741 8717492073514111277556889)
      ·
        refine ⟨6538119055135583458167667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8717492073514111277556889 6538119055135583458167667)
        ·
          refine ⟨9807178582703375187251501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538119055135583458167667 9807178582703375187251501)
          ·
            refine ⟨3677691968513765695219313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9807178582703375187251501 3677691968513765695219313)
            ·
              refine ⟨2758268976385324271414485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677691968513765695219313 2758268976385324271414485)
              ·
                refine ⟨64646929134031037611277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2758268976385324271414485 64646929134031037611277)
                ·
                  rfl

theorem cell23_3399285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 7].length) (baseStart_3399285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399285 prefixEnd_3399285 := by exact prefixLift 3399285
  have htrace : WordTrace (prefixWord ++ tailWord_3399285) baseStart_3399285 baseEnd_3399285 := by
    simpa [prefixWord, tailWord_3399285, baseEnd_3399285] using wordTrace_append hprefix tailTrace_3399285
  have hstable : (prefixWord ++ tailWord_3399285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399285).length < 2 ^ (prefixWord ++ tailWord_3399285).sum := by decide
  have hdescent : baseEnd_3399285 < baseStart_3399285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399305 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 1, 3, 2]
def baseStart_3399305 : Nat := 118140960795 + 3399305 * 2 ^ 59
def prefixEnd_3399305 : Nat := 4983230072969 + 3 ^ 40 * 3399305 * 2
def baseEnd_3399305 : Nat := 1745477356231927937254387

theorem tailTrace_3399305 : CollatzResearch.WordTrace tailWord_3399305 prefixEnd_3399305 1745477356231927937254387 := by
  unfold tailWord_3399305
  simp only [CollatzResearch.WordTrace]
  refine ⟨123982838949906014918759369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82655225966604009945839579 123982838949906014918759369)
  ·
    refine ⟨92987129212429511189069527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123982838949906014918759369 92987129212429511189069527)
    ·
      refine ⟨139480693818644266783604291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92987129212429511189069527 139480693818644266783604291)
      ·
        refine ⟨209221040727966400175406437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139480693818644266783604291 209221040727966400175406437)
        ·
          refine ⟨39228945136493700032888707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209221040727966400175406437 39228945136493700032888707)
          ·
            refine ⟨58843417704740550049333061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39228945136493700032888707 58843417704740550049333061)
            ·
              refine ⟨11033140819638853134249949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58843417704740550049333061 11033140819638853134249949)
              ·
                refine ⟨4137427807364569925343731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11033140819638853134249949 4137427807364569925343731)
                ·
                  refine ⟨6206141711046854888015597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137427807364569925343731 6206141711046854888015597)
                  ·
                    refine ⟨2327303141642570583005849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6206141711046854888015597 2327303141642570583005849)
                    ·
                      refine ⟨1745477356231927937254387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327303141642570583005849 1745477356231927937254387)
                      ·
                        rfl

theorem cell23_3399305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3, 2].length) (baseStart_3399305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399305 prefixEnd_3399305 := by exact prefixLift 3399305
  have htrace : WordTrace (prefixWord ++ tailWord_3399305) baseStart_3399305 baseEnd_3399305 := by
    simpa [prefixWord, tailWord_3399305, baseEnd_3399305] using wordTrace_append hprefix tailTrace_3399305
  have hstable : (prefixWord ++ tailWord_3399305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399305).length < 2 ^ (prefixWord ++ tailWord_3399305).sum := by decide
  have hdescent : baseEnd_3399305 < baseStart_3399305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399329 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3399329 : Nat := 118140960795 + 3399329 * 2 ^ 59
def prefixEnd_3399329 : Nat := 4983230072969 + 3 ^ 40 * 3399329 * 2
def baseEnd_3399329 : Nat := 1745489679767635843354277

theorem tailTrace_3399329 : CollatzResearch.WordTrace tailWord_3399329 prefixEnd_3399329 1745489679767635843354277 := by
  unfold tailWord_3399329
  simp only [CollatzResearch.WordTrace]
  refine ⟨123983714301819067017633041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82655809534546044678422027 123983714301819067017633041)
  ·
    refine ⟨92987785726364300263224781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123983714301819067017633041 92987785726364300263224781)
    ·
      refine ⟨34870419647386612598709293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92987785726364300263224781 34870419647386612598709293)
      ·
        refine ⟨13076407367769979724515985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34870419647386612598709293 13076407367769979724515985)
        ·
          refine ⟨9807305525827484793386989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13076407367769979724515985 9807305525827484793386989)
          ·
            refine ⟨3677739572185306797520121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9807305525827484793386989 3677739572185306797520121)
            ·
              refine ⟨2758304679138980098140091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677739572185306797520121 2758304679138980098140091)
              ·
                refine ⟨4137457018708470147210137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758304679138980098140091 4137457018708470147210137)
                ·
                  refine ⟨3103092764031352610407603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137457018708470147210137 3103092764031352610407603)
                  ·
                    refine ⟨4654639146047028915611405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103092764031352610407603 4654639146047028915611405)
                    ·
                      refine ⟨1745489679767635843354277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4654639146047028915611405 1745489679767635843354277)
                      ·
                        rfl

theorem cell23_3399329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3399329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399329 prefixEnd_3399329 := by exact prefixLift 3399329
  have htrace : WordTrace (prefixWord ++ tailWord_3399329) baseStart_3399329 baseEnd_3399329 := by
    simpa [prefixWord, tailWord_3399329, baseEnd_3399329] using wordTrace_append hprefix tailTrace_3399329
  have hstable : (prefixWord ++ tailWord_3399329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399329).length < 2 ^ (prefixWord ++ tailWord_3399329).sum := by decide
  have hdescent : baseEnd_3399329 < baseStart_3399329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399331 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3399331 : Nat := 118140960795 + 3399331 * 2 ^ 59
def prefixEnd_3399331 : Nat := 4983230072969 + 3 ^ 40 * 3399331 * 2
def baseEnd_3399331 : Nat := 1745490706728944835529267

theorem tailTrace_3399331 : CollatzResearch.WordTrace tailWord_3399331 prefixEnd_3399331 1745490706728944835529267 := by
  unfold tailWord_3399331
  simp only [CollatzResearch.WordTrace]
  refine ⟨123983787247811821359205847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82655858165207880906137231 123983787247811821359205847)
  ·
    refine ⟨185975680871717732038808771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123983787247811821359205847 185975680871717732038808771)
    ·
      refine ⟨278963521307576598058213157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185975680871717732038808771 278963521307576598058213157)
      ·
        refine ⟨52305660245170612135914967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278963521307576598058213157 52305660245170612135914967)
        ·
          refine ⟨78458490367755918203872451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52305660245170612135914967 78458490367755918203872451)
          ·
            refine ⟨117687735551633877305808677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78458490367755918203872451 117687735551633877305808677)
            ·
              refine ⟨22066450415931351994839127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117687735551633877305808677 22066450415931351994839127)
              ·
                refine ⟨33099675623897027992258691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22066450415931351994839127 33099675623897027992258691)
                ·
                  refine ⟨49649513435845541988388037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33099675623897027992258691 49649513435845541988388037)
                  ·
                    refine ⟨9309283769221039122822757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49649513435845541988388037 9309283769221039122822757)
                    ·
                      refine ⟨1745490706728944835529267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9309283769221039122822757 1745490706728944835529267)
                      ·
                        rfl

theorem cell23_3399331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3399331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399331 prefixEnd_3399331 := by exact prefixLift 3399331
  have htrace : WordTrace (prefixWord ++ tailWord_3399331) baseStart_3399331 baseEnd_3399331 := by
    simpa [prefixWord, tailWord_3399331, baseEnd_3399331] using wordTrace_append hprefix tailTrace_3399331
  have hstable : (prefixWord ++ tailWord_3399331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399331).length < 2 ^ (prefixWord ++ tailWord_3399331).sum := by decide
  have hdescent : baseEnd_3399331 < baseStart_3399331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399368 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_3399368 : Nat := 118140960795 + 3399368 * 2 ^ 59
def prefixEnd_3399368 : Nat := 4983230072969 + 3 ^ 40 * 3399368 * 2
def baseEnd_3399368 : Nat := 1745509705513161190766597

theorem tailTrace_3399368 : CollatzResearch.WordTrace tailWord_3399368 prefixEnd_3399368 1745509705513161190766597 := by
  unfold tailWord_3399368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61992568374338888339151379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82656757832451851118868505 61992568374338888339151379)
  ·
    refine ⟨92988852561508332508727069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61992568374338888339151379 92988852561508332508727069)
    ·
      refine ⟨34870819710565624690772651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92988852561508332508727069 34870819710565624690772651)
      ·
        refine ⟨52306229565848437036158977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34870819710565624690772651 52306229565848437036158977)
        ·
          refine ⟨39229672174386327777119233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52306229565848437036158977 39229672174386327777119233)
          ·
            refine ⟨29422254130789745832839425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39229672174386327777119233 29422254130789745832839425)
            ·
              refine ⟨22066690598092309374629569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29422254130789745832839425 22066690598092309374629569)
              ·
                refine ⟨16550017948569232030972177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22066690598092309374629569 16550017948569232030972177)
                ·
                  refine ⟨12412513461426924023229133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16550017948569232030972177 12412513461426924023229133)
                  ·
                    refine ⟨4654692548035096508710925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12412513461426924023229133 4654692548035096508710925)
                    ·
                      refine ⟨1745509705513161190766597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4654692548035096508710925 1745509705513161190766597)
                      ·
                        rfl

theorem cell23_3399368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_3399368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399368 prefixEnd_3399368 := by exact prefixLift 3399368
  have htrace : WordTrace (prefixWord ++ tailWord_3399368) baseStart_3399368 baseEnd_3399368 := by
    simpa [prefixWord, tailWord_3399368, baseEnd_3399368] using wordTrace_append hprefix tailTrace_3399368
  have hstable : (prefixWord ++ tailWord_3399368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399368).length < 2 ^ (prefixWord ++ tailWord_3399368).sum := by decide
  have hdescent : baseEnd_3399368 < baseStart_3399368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399405 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3399405 : Nat := 118140960795 + 3399405 * 2 ^ 59
def prefixEnd_3399405 : Nat := 4983230072969 + 3 ^ 40 * 3399405 * 2
def baseEnd_3399405 : Nat := 581842901432459182001309

theorem tailTrace_3399405 : CollatzResearch.WordTrace tailWord_3399405 prefixEnd_3399405 581842901432459182001309 := by
  unfold tailWord_3399405
  simp only [CollatzResearch.WordTrace]
  refine ⟨123986486249543731997399669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82657657499695821331599779 123986486249543731997399669)
  ·
    refine ⟨11623733085894724874756219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123986486249543731997399669 11623733085894724874756219)
    ·
      refine ⟨17435599628842087312134329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11623733085894724874756219 17435599628842087312134329)
      ·
        refine ⟨13076699721631565484100747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17435599628842087312134329 13076699721631565484100747)
        ·
          refine ⟨19615049582447348226151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13076699721631565484100747 19615049582447348226151121)
          ·
            refine ⟨14711287186835511169613341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19615049582447348226151121 14711287186835511169613341)
            ·
              refine ⟨5516732695063316688605003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14711287186835511169613341 5516732695063316688605003)
              ·
                refine ⟨8275099042594975032907505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516732695063316688605003 8275099042594975032907505)
                ·
                  refine ⟨6206324281946231274680629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275099042594975032907505 6206324281946231274680629)
                  ·
                    refine ⟨581842901432459182001309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6206324281946231274680629 581842901432459182001309)
                    ·
                      rfl

theorem cell23_3399405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3399405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399405 prefixEnd_3399405 := by exact prefixLift 3399405
  have htrace : WordTrace (prefixWord ++ tailWord_3399405) baseStart_3399405 baseEnd_3399405 := by
    simpa [prefixWord, tailWord_3399405, baseEnd_3399405] using wordTrace_append hprefix tailTrace_3399405
  have hstable : (prefixWord ++ tailWord_3399405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399405).length < 2 ^ (prefixWord ++ tailWord_3399405).sum := by decide
  have hdescent : baseEnd_3399405 < baseStart_3399405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399408 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_3399408 : Nat := 118140960795 + 3399408 * 2 ^ 59
def prefixEnd_3399408 : Nat := 4983230072969 + 3 ^ 40 * 3399408 * 2
def baseEnd_3399408 : Nat := 1745530244739341034266413

theorem tailTrace_3399408 : CollatzResearch.WordTrace tailWord_3399408 prefixEnd_3399408 1745530244739341034266413 := by
  unfold tailWord_3399408
  simp only [CollatzResearch.WordTrace]
  refine ⟨61993297834266431754879439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82657730445688575673172585 61993297834266431754879439)
  ·
    refine ⟨92989946751399647632319159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61993297834266431754879439 92989946751399647632319159)
    ·
      refine ⟨139484920127099471448478739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92989946751399647632319159 139484920127099471448478739)
      ·
        refine ⟨209227380190649207172718109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139484920127099471448478739 209227380190649207172718109)
        ·
          refine ⟨78460267571493452689769291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209227380190649207172718109 78460267571493452689769291)
          ·
            refine ⟨117690401357240179034653937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78460267571493452689769291 117690401357240179034653937)
            ·
              refine ⟨88267801017930134275990453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117690401357240179034653937 88267801017930134275990453)
              ·
                refine ⟨8275106345430950088374105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88267801017930134275990453 8275106345430950088374105)
                ·
                  refine ⟨6206329759073212566280579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275106345430950088374105 6206329759073212566280579)
                  ·
                    refine ⟨9309494638609818849420869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6206329759073212566280579 9309494638609818849420869)
                    ·
                      refine ⟨1745530244739341034266413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9309494638609818849420869 1745530244739341034266413)
                      ·
                        rfl

theorem cell23_3399408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_3399408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399408 prefixEnd_3399408 := by exact prefixLift 3399408
  have htrace : WordTrace (prefixWord ++ tailWord_3399408) baseStart_3399408 baseEnd_3399408 := by
    simpa [prefixWord, tailWord_3399408, baseEnd_3399408] using wordTrace_append hprefix tailTrace_3399408
  have hstable : (prefixWord ++ tailWord_3399408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399408).length < 2 ^ (prefixWord ++ tailWord_3399408).sum := by decide
  have hdescent : baseEnd_3399408 < baseStart_3399408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399418 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_3399418 : Nat := 118140960795 + 3399418 * 2 ^ 59
def prefixEnd_3399418 : Nat := 4983230072969 + 3 ^ 40 * 3399418 * 2
def baseEnd_3399418 : Nat := 581845126515295331713789

theorem tailTrace_3399418 : CollatzResearch.WordTrace tailWord_3399418 prefixEnd_3399418 581845126515295331713789 := by
  unfold tailWord_3399418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996740099624158804405727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82657973598997756811748605 30996740099624158804405727)
  ·
    refine ⟨46495110149436238206608591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30996740099624158804405727 46495110149436238206608591)
    ·
      refine ⟨69742665224154357309912887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46495110149436238206608591 69742665224154357309912887)
      ·
        refine ⟨104613997836231535964869331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69742665224154357309912887 104613997836231535964869331)
        ·
          refine ⟨156920996754347303947303997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104613997836231535964869331 156920996754347303947303997)
          ·
            refine ⟨58845373782880238980238999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156920996754347303947303997 58845373782880238980238999)
            ·
              refine ⟨88268060674320358470358499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58845373782880238980238999 88268060674320358470358499)
              ·
                refine ⟨132402091011480537705537749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88268060674320358470358499 132402091011480537705537749)
                ·
                  refine ⟨3103174008081575102473541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 132402091011480537705537749 3103174008081575102473541)
                  ·
                    refine ⟨581845126515295331713789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103174008081575102473541 581845126515295331713789)
                    ·
                      rfl

theorem cell23_3399418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_3399418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399418 prefixEnd_3399418 := by exact prefixLift 3399418
  have htrace : WordTrace (prefixWord ++ tailWord_3399418) baseStart_3399418 baseEnd_3399418 := by
    simpa [prefixWord, tailWord_3399418, baseEnd_3399418] using wordTrace_append hprefix tailTrace_3399418
  have hstable : (prefixWord ++ tailWord_3399418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399418).length < 2 ^ (prefixWord ++ tailWord_3399418).sum := by decide
  have hdescent : baseEnd_3399418 < baseStart_3399418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399425 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_3399425 : Nat := 118140960795 + 3399425 * 2 ^ 59
def prefixEnd_3399425 : Nat := 4983230072969 + 3 ^ 40 * 3399425 * 2
def baseEnd_3399425 : Nat := 1745538973910467467753835

theorem tailTrace_3399425 : CollatzResearch.WordTrace tailWord_3399425 prefixEnd_3399425 1745538973910467467753835 := by
  unfold tailWord_3399425
  simp only [CollatzResearch.WordTrace]
  refine ⟨123987215709471275413127729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82658143806314183608751819 123987215709471275413127729)
  ·
    refine ⟨92990411782103456559845797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123987215709471275413127729 92990411782103456559845797)
    ·
      refine ⟨17435702209144398104971087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92990411782103456559845797 17435702209144398104971087)
      ·
        refine ⟨26153553313716597157456631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17435702209144398104971087 26153553313716597157456631)
        ·
          refine ⟨39230329970574895736184947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26153553313716597157456631 39230329970574895736184947)
          ·
            refine ⟨58845494955862343604277421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39230329970574895736184947 58845494955862343604277421)
            ·
              refine ⟨22067060608448378851604033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58845494955862343604277421 22067060608448378851604033)
              ·
                refine ⟨16550295456336284138703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22067060608448378851604033 16550295456336284138703025)
                ·
                  refine ⟨12412721592252213104027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16550295456336284138703025 12412721592252213104027269)
                  ·
                    refine ⟨2327385298547289957005113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12412721592252213104027269 2327385298547289957005113)
                    ·
                      refine ⟨1745538973910467467753835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327385298547289957005113 1745538973910467467753835)
                      ·
                        rfl

theorem cell23_3399425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_3399425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399425 prefixEnd_3399425 := by exact prefixLift 3399425
  have htrace : WordTrace (prefixWord ++ tailWord_3399425) baseStart_3399425 baseEnd_3399425 := by
    simpa [prefixWord, tailWord_3399425, baseEnd_3399425] using wordTrace_append hprefix tailTrace_3399425
  have hstable : (prefixWord ++ tailWord_3399425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399425).length < 2 ^ (prefixWord ++ tailWord_3399425).sum := by decide
  have hdescent : baseEnd_3399425 < baseStart_3399425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399437 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3399437 : Nat := 118140960795 + 3399437 * 2 ^ 59
def prefixEnd_3399437 : Nat := 4983230072969 + 3 ^ 40 * 3399437 * 2
def baseEnd_3399437 : Nat := 1745545135678321420803781

theorem tailTrace_3399437 : CollatzResearch.WordTrace tailWord_3399437 prefixEnd_3399437 1745545135678321420803781 := by
  unfold tailWord_3399437
  simp only [CollatzResearch.WordTrace]
  refine ⟨123987653385427801462564565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82658435590285200975043043 123987653385427801462564565)
  ·
    refine ⟨2905960626220964096778857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 123987653385427801462564565 2905960626220964096778857)
    ·
      refine ⟨2179470469665723072584143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2905960626220964096778857 2179470469665723072584143)
      ·
        refine ⟨3269205704498584608876215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179470469665723072584143 3269205704498584608876215)
        ·
          refine ⟨4903808556747876913314323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269205704498584608876215 4903808556747876913314323)
          ·
            refine ⟨7355712835121815369971485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903808556747876913314323 7355712835121815369971485)
            ·
              refine ⟨2758392313170680763739307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7355712835121815369971485 2758392313170680763739307)
              ·
                refine ⟨4137588469756021145608961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758392313170680763739307 4137588469756021145608961)
                ·
                  refine ⟨3103191352317015859206721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137588469756021145608961 3103191352317015859206721)
                  ·
                    refine ⟨2327393514237761894405041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103191352317015859206721 2327393514237761894405041)
                    ·
                      refine ⟨1745545135678321420803781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327393514237761894405041 1745545135678321420803781)
                      ·
                        rfl

theorem cell23_3399437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3399437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399437 prefixEnd_3399437 := by exact prefixLift 3399437
  have htrace : WordTrace (prefixWord ++ tailWord_3399437) baseStart_3399437 baseEnd_3399437 := by
    simpa [prefixWord, tailWord_3399437, baseEnd_3399437] using wordTrace_append hprefix tailTrace_3399437
  have hstable : (prefixWord ++ tailWord_3399437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399437).length < 2 ^ (prefixWord ++ tailWord_3399437).sum := by decide
  have hdescent : baseEnd_3399437 < baseStart_3399437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399448 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 6]
def baseStart_3399448 : Nat := 118140960795 + 3399448 * 2 ^ 59
def prefixEnd_3399448 : Nat := 4983230072969 + 3 ^ 40 * 3399448 * 2
def baseEnd_3399448 : Nat := 193950087107280097529581

theorem tailTrace_3399448 : CollatzResearch.WordTrace tailWord_3399448 prefixEnd_3399448 193950087107280097529581 := by
  unfold tailWord_3399448
  simp only [CollatzResearch.WordTrace]
  refine ⟨61994027294193975170607499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82658703058925300227476665 61994027294193975170607499)
  ·
    refine ⟨92991040941290962755911249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61994027294193975170607499 92991040941290962755911249)
    ·
      refine ⟨69743280705968222066933437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92991040941290962755911249 69743280705968222066933437)
      ·
        refine ⟨26153730264738083275100039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69743280705968222066933437 26153730264738083275100039)
        ·
          refine ⟨39230595397107124912650059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26153730264738083275100039 39230595397107124912650059)
          ·
            refine ⟨58845893095660687368975089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39230595397107124912650059 58845893095660687368975089)
            ·
              refine ⟨44134419821745515526731317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58845893095660687368975089 44134419821745515526731317)
              ·
                refine ⟨4137601858288642080631061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44134419821745515526731317 4137601858288642080631061)
                ·
                  refine ⟨193950087107280097529581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4137601858288642080631061 193950087107280097529581)
                  ·
                    rfl

theorem cell23_3399448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_3399448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399448 prefixEnd_3399448 := by exact prefixLift 3399448
  have htrace : WordTrace (prefixWord ++ tailWord_3399448) baseStart_3399448 baseEnd_3399448 := by
    simpa [prefixWord, tailWord_3399448, baseEnd_3399448] using wordTrace_append hprefix tailTrace_3399448
  have hstable : (prefixWord ++ tailWord_3399448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399448).length < 2 ^ (prefixWord ++ tailWord_3399448).sum := by decide
  have hdescent : baseEnd_3399448 < baseStart_3399448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399486 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_3399486 : Nat := 118140960795 + 3399486 * 2 ^ 59
def prefixEnd_3399486 : Nat := 4983230072969 + 3 ^ 40 * 3399486 * 2
def baseEnd_3399486 : Nat := 581856765410130576363685

theorem tailTrace_3399486 : CollatzResearch.WordTrace tailWord_3399486 prefixEnd_3399486 581856765410130576363685 := by
  unfold tailWord_3399486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498680070281285353887289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82659627041500188554065541 15498680070281285353887289)
  ·
    refine ⟨11624010052710964015415467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15498680070281285353887289 11624010052710964015415467)
    ·
      refine ⟨17436015079066446023123201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11624010052710964015415467 17436015079066446023123201)
      ·
        refine ⟨13077011309299834517342401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17436015079066446023123201 13077011309299834517342401)
        ·
          refine ⟨9807758481974875888006801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13077011309299834517342401 9807758481974875888006801)
          ·
            refine ⟨7355818861481156916005101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9807758481974875888006801 7355818861481156916005101)
            ·
              refine ⟨2758432073055433843501913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7355818861481156916005101 2758432073055433843501913)
              ·
                refine ⟨2068824054791575382626435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758432073055433843501913 2068824054791575382626435)
                ·
                  refine ⟨3103236082187363073939653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068824054791575382626435 3103236082187363073939653)
                  ·
                    refine ⟨581856765410130576363685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103236082187363073939653 581856765410130576363685)
                    ·
                      rfl

theorem cell23_3399486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_3399486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399486 prefixEnd_3399486 := by exact prefixLift 3399486
  have htrace : WordTrace (prefixWord ++ tailWord_3399486) baseStart_3399486 baseEnd_3399486 := by
    simpa [prefixWord, tailWord_3399486, baseEnd_3399486] using wordTrace_append hprefix tailTrace_3399486
  have hstable : (prefixWord ++ tailWord_3399486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399486).length < 2 ^ (prefixWord ++ tailWord_3399486).sum := by decide
  have hdescent : baseEnd_3399486 < baseStart_3399486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399555 : List Nat := [1, 1, 1, 3, 4, 4, 1, 8]
def baseStart_3399555 : Nat := 118140960795 + 3399555 * 2 ^ 59
def prefixEnd_3399555 : Nat := 4983230072969 + 3 ^ 40 * 3399555 * 2
def baseEnd_3399555 : Nat := 64652063940575998486231

theorem tailTrace_3399555 : CollatzResearch.WordTrace tailWord_3399555 prefixEnd_3399555 64652063940575998486231 := by
  unfold tailWord_3399555
  simp only [CollatzResearch.WordTrace]
  refine ⟨123991957199000307615360119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82661304799333538410240079 123991957199000307615360119)
  ·
    refine ⟨185987935798500461423040179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123991957199000307615360119 185987935798500461423040179)
    ·
      refine ⟨278981903697750692134560269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185987935798500461423040179 278981903697750692134560269)
      ·
        refine ⟨104618213886656509550460101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278981903697750692134560269 104618213886656509550460101)
        ·
          refine ⟨19615915103748095540711269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104618213886656509550460101 19615915103748095540711269)
          ·
            refine ⟨3677984081952767913883363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19615915103748095540711269 3677984081952767913883363)
            ·
              refine ⟨5516976122929151870825045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677984081952767913883363 5516976122929151870825045)
              ·
                refine ⟨64652063940575998486231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5516976122929151870825045 64652063940575998486231)
                ·
                  rfl

theorem cell23_3399555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 8].length) (baseStart_3399555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399555 prefixEnd_3399555 := by exact prefixLift 3399555
  have htrace : WordTrace (prefixWord ++ tailWord_3399555) baseStart_3399555 baseEnd_3399555 := by
    simpa [prefixWord, tailWord_3399555, baseEnd_3399555] using wordTrace_append hprefix tailTrace_3399555
  have hstable : (prefixWord ++ tailWord_3399555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399555).length < 2 ^ (prefixWord ++ tailWord_3399555).sum := by decide
  have hdescent : baseEnd_3399555 < baseStart_3399555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399572 : List Nat := [2, 4, 2, 1, 1, 3, 3, 7]
def baseStart_3399572 : Nat := 118140960795 + 3399572 * 2 ^ 59
def prefixEnd_3399572 : Nat := 4983230072969 + 3 ^ 40 * 3399572 * 2
def baseEnd_3399572 : Nat := 64652387243210310837617

theorem tailTrace_3399572 : CollatzResearch.WordTrace tailWord_3399572 prefixEnd_3399572 64652387243210310837617 := by
  unfold tailWord_3399572
  simp only [CollatzResearch.WordTrace]
  refine ⟨61996288619969359759364485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82661718159959146345819313 61996288619969359759364485)
  ·
    refine ⟨11624304116244254954880841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61996288619969359759364485 11624304116244254954880841)
    ·
      refine ⟨8718228087183191216160631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624304116244254954880841 8718228087183191216160631)
      ·
        refine ⟨13077342130774786824240947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718228087183191216160631 13077342130774786824240947)
        ·
          refine ⟨19616013196162180236361421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13077342130774786824240947 19616013196162180236361421)
          ·
            refine ⟨7356004948560817588635533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19616013196162180236361421 7356004948560817588635533)
            ·
              refine ⟨2758501855710306595738325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7356004948560817588635533 2758501855710306595738325)
              ·
                refine ⟨64652387243210310837617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2758501855710306595738325 64652387243210310837617)
                ·
                  rfl

theorem cell23_3399572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 7].length) (baseStart_3399572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399572 prefixEnd_3399572 := by exact prefixLift 3399572
  have htrace : WordTrace (prefixWord ++ tailWord_3399572) baseStart_3399572 baseEnd_3399572 := by
    simpa [prefixWord, tailWord_3399572, baseEnd_3399572] using wordTrace_append hprefix tailTrace_3399572
  have hstable : (prefixWord ++ tailWord_3399572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399572).length < 2 ^ (prefixWord ++ tailWord_3399572).sum := by decide
  have hdescent : baseEnd_3399572 < baseStart_3399572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399583 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3399583 : Nat := 118140960795 + 3399583 * 2 ^ 59
def prefixEnd_3399583 : Nat := 4983230072969 + 3 ^ 40 * 3399583 * 2
def baseEnd_3399583 : Nat := 1745620103853877849578109

theorem tailTrace_3399583 : CollatzResearch.WordTrace tailWord_3399583 prefixEnd_3399583 1745620103853877849578109 := by
  unfold tailWord_3399583
  simp only [CollatzResearch.WordTrace]
  refine ⟨123992978442898868397379403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82661985628599245598252935 123992978442898868397379403)
  ·
    refine ⟨185989467664348302596069105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123992978442898868397379403 185989467664348302596069105)
    ·
      refine ⟨139492100748261226947051829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185989467664348302596069105 139492100748261226947051829)
      ·
        refine ⟨13077384445149490026286109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139492100748261226947051829 13077384445149490026286109)
        ·
          refine ⟨4904019166931058759857291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13077384445149490026286109 4904019166931058759857291)
          ·
            refine ⟨7356028750396588139785937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904019166931058759857291 7356028750396588139785937)
            ·
              refine ⟨5517021562797441104839453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7356028750396588139785937 5517021562797441104839453)
              ·
                refine ⟨2068883086049040414314795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5517021562797441104839453 2068883086049040414314795)
                ·
                  refine ⟨3103324629073560621472193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068883086049040414314795 3103324629073560621472193)
                  ·
                    refine ⟨2327493471805170466104145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103324629073560621472193 2327493471805170466104145)
                    ·
                      refine ⟨1745620103853877849578109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327493471805170466104145 1745620103853877849578109)
                      ·
                        rfl

theorem cell23_3399583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3399583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399583 prefixEnd_3399583 := by exact prefixLift 3399583
  have htrace : WordTrace (prefixWord ++ tailWord_3399583) baseStart_3399583 baseEnd_3399583 := by
    simpa [prefixWord, tailWord_3399583, baseEnd_3399583] using wordTrace_append hprefix tailTrace_3399583
  have hstable : (prefixWord ++ tailWord_3399583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399583).length < 2 ^ (prefixWord ++ tailWord_3399583).sum := by decide
  have hdescent : baseEnd_3399583 < baseStart_3399583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399642 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_3399642 : Nat := 118140960795 + 3399642 * 2 ^ 59
def prefixEnd_3399642 : Nat := 4983230072969 + 3 ^ 40 * 3399642 * 2
def baseEnd_3399642 : Nat := 1745650399212493118740337

theorem tailTrace_3399642 : CollatzResearch.WordTrace tailWord_3399642 prefixEnd_3399642 1745650399212493118740337 := by
  unfold tailWord_3399642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30998782587421280368444295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82663420233123414315851453 30998782587421280368444295)
  ·
    refine ⟨46498173881131920552666443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30998782587421280368444295 46498173881131920552666443)
    ·
      refine ⟨69747260821697880828999665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46498173881131920552666443 69747260821697880828999665)
      ·
        refine ⟨52310445616273410621749749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69747260821697880828999665 52310445616273410621749749)
        ·
          refine ⟨4904104276525632245789039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52310445616273410621749749 4904104276525632245789039)
          ·
            refine ⟨7356156414788448368683559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904104276525632245789039 7356156414788448368683559)
            ·
              refine ⟨11034234622182672553025339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356156414788448368683559 11034234622182672553025339)
              ·
                refine ⟨16551351933274008829538009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034234622182672553025339 16551351933274008829538009)
                ·
                  refine ⟨12413513949955506622153507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16551351933274008829538009 12413513949955506622153507)
                  ·
                    refine ⟨18620270924933259933230261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12413513949955506622153507 18620270924933259933230261)
                    ·
                      refine ⟨1745650399212493118740337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18620270924933259933230261 1745650399212493118740337)
                      ·
                        rfl

theorem cell23_3399642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_3399642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399642 prefixEnd_3399642 := by exact prefixLift 3399642
  have htrace : WordTrace (prefixWord ++ tailWord_3399642) baseStart_3399642 baseEnd_3399642 := by
    simpa [prefixWord, tailWord_3399642, baseEnd_3399642] using wordTrace_append hprefix tailTrace_3399642
  have hstable : (prefixWord ++ tailWord_3399642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399642).length < 2 ^ (prefixWord ++ tailWord_3399642).sum := by decide
  have hdescent : baseEnd_3399642 < baseStart_3399642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399662 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_3399662 : Nat := 118140960795 + 3399662 * 2 ^ 59
def prefixEnd_3399662 : Nat := 4983230072969 + 3 ^ 40 * 3399662 * 2
def baseEnd_3399662 : Nat := 193962296536175893387805

theorem tailTrace_3399662 : CollatzResearch.WordTrace tailWord_3399662 prefixEnd_3399662 193962296536175893387805 := by
  unfold tailWord_3399662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15499482476201583111188155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82663906539741776593003493 15499482476201583111188155)
  ·
    refine ⟨23249223714302374666782233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15499482476201583111188155 23249223714302374666782233)
    ·
      refine ⟨17436917785726781000086675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23249223714302374666782233 17436917785726781000086675)
      ·
        refine ⟨26155376678590171500130013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17436917785726781000086675 26155376678590171500130013)
        ·
          refine ⟨9808266254471314312548755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26155376678590171500130013 9808266254471314312548755)
          ·
            refine ⟨14712399381706971468823133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808266254471314312548755 14712399381706971468823133)
            ·
              refine ⟨5517149768140114300808675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14712399381706971468823133 5517149768140114300808675)
              ·
                refine ⟨8275724652210171451213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517149768140114300808675 8275724652210171451213013)
                ·
                  refine ⟨193962296536175893387805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8275724652210171451213013 193962296536175893387805)
                  ·
                    rfl

theorem cell23_3399662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_3399662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399662 prefixEnd_3399662 := by exact prefixLift 3399662
  have htrace : WordTrace (prefixWord ++ tailWord_3399662) baseStart_3399662 baseEnd_3399662 := by
    simpa [prefixWord, tailWord_3399662, baseEnd_3399662] using wordTrace_append hprefix tailTrace_3399662
  have hstable : (prefixWord ++ tailWord_3399662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399662).length < 2 ^ (prefixWord ++ tailWord_3399662).sum := by decide
  have hdescent : baseEnd_3399662 < baseStart_3399662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399673 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 2, 2, 2]
def baseStart_3399673 : Nat := 118140960795 + 3399673 * 2 ^ 59
def prefixEnd_3399673 : Nat := 4983230072969 + 3 ^ 40 * 3399673 * 2
def baseEnd_3399673 : Nat := 1745666317112782497452695

theorem tailTrace_3399673 : CollatzResearch.WordTrace tailWord_3399673 prefixEnd_3399673 1745666317112782497452695 := by
  unfold tailWord_3399673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123996261012572813768155673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82664174008381875845437115 123996261012572813768155673)
  ·
    refine ⟨92997195759429610326116755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123996261012572813768155673 92997195759429610326116755)
    ·
      refine ⟨139495793639144415489175133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92997195759429610326116755 139495793639144415489175133)
      ·
        refine ⟨52310922614679155808440675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139495793639144415489175133 52310922614679155808440675)
        ·
          refine ⟨78466383922018733712661013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52310922614679155808440675 78466383922018733712661013)
          ·
            refine ⟨3678111746344628142780985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78466383922018733712661013 3678111746344628142780985)
            ·
              refine ⟨2758583809758471107085739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678111746344628142780985 2758583809758471107085739)
              ·
                refine ⟨4137875714637706660628609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758583809758471107085739 4137875714637706660628609)
                ·
                  refine ⟨3103406785978279995471457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137875714637706660628609 3103406785978279995471457)
                  ·
                    refine ⟨2327555089483709996603593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103406785978279995471457 2327555089483709996603593)
                    ·
                      refine ⟨1745666317112782497452695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327555089483709996603593 1745666317112782497452695)
                      ·
                        rfl

theorem cell23_3399673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_3399673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399673 prefixEnd_3399673 := by exact prefixLift 3399673
  have htrace : WordTrace (prefixWord ++ tailWord_3399673) baseStart_3399673 baseEnd_3399673 := by
    simpa [prefixWord, tailWord_3399673, baseEnd_3399673] using wordTrace_append hprefix tailTrace_3399673
  have hstable : (prefixWord ++ tailWord_3399673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399673).length < 2 ^ (prefixWord ++ tailWord_3399673).sum := by decide
  have hdescent : baseEnd_3399673 < baseStart_3399673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
