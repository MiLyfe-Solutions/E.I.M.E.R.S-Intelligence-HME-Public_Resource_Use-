import V185TrunkScan23Chunk1261

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7475487 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 2, 5]
def baseStart_7475487 : Nat := 118140960795 + 7475487 * 2 ^ 59
def prefixEnd_7475487 : Nat := 4983230072969 + 3 ^ 40 * 7475487 * 2
def baseEnd_7475487 : Nat := 1279505985812366285477789

theorem tailTrace_7475487 : CollatzResearch.WordTrace tailWord_7475487 prefixEnd_7475487 1279505985812366285477789 := by
  unfold tailWord_7475487
  simp only [CollatzResearch.WordTrace]
  refine ⟨272653410268594785380512715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181768940179063190253675143 272653410268594785380512715)
  ·
    refine ⟨408980115402892178070769073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272653410268594785380512715 408980115402892178070769073)
    ·
      refine ⟨306735086552169133553076805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408980115402892178070769073 306735086552169133553076805)
      ·
        refine ⟨57512828728531712541201901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306735086552169133553076805 57512828728531712541201901)
        ·
          refine ⟨21567310773199392202950713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57512828728531712541201901 21567310773199392202950713)
          ·
            refine ⟨16175483079899544152213035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21567310773199392202950713 16175483079899544152213035)
            ·
              refine ⟨24263224619849316228319553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16175483079899544152213035 24263224619849316228319553)
              ·
                refine ⟨18197418464886987171239665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24263224619849316228319553 18197418464886987171239665)
                ·
                  refine ⟨13648063848665240378429749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18197418464886987171239665 13648063848665240378429749)
                  ·
                    refine ⟨1279505985812366285477789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13648063848665240378429749 1279505985812366285477789)
                    ·
                      rfl

theorem cell23_7475487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_7475487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475487 prefixEnd_7475487 := by exact prefixLift 7475487
  have htrace : WordTrace (prefixWord ++ tailWord_7475487) baseStart_7475487 baseEnd_7475487 := by
    simpa [prefixWord, tailWord_7475487, baseEnd_7475487] using wordTrace_append hprefix tailTrace_7475487
  have hstable : (prefixWord ++ tailWord_7475487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475487).length < 2 ^ (prefixWord ++ tailWord_7475487).sum := by decide
  have hdescent : baseEnd_7475487 < baseStart_7475487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475502 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7475502 : Nat := 118140960795 + 7475502 * 2 ^ 59
def prefixEnd_7475502 : Nat := 4983230072969 + 3 ^ 40 * 7475502 * 2
def baseEnd_7475502 : Nat := 3838525659646916297745799

theorem tailTrace_7475502 : CollatzResearch.WordTrace tailWord_7475502 prefixEnd_7475502 3838525659646916297745799 := by
  unfold tailWord_7475502
  simp only [CollatzResearch.WordTrace]
  refine ⟨34081744670442555367788595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181769304909026961961539173 34081744670442555367788595)
  ·
    refine ⟨51122617005663833051682893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34081744670442555367788595 51122617005663833051682893)
    ·
      refine ⟨19170981377123937394381085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51122617005663833051682893 19170981377123937394381085)
      ·
        refine ⟨7189118016421476522892907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19170981377123937394381085 7189118016421476522892907)
        ·
          refine ⟨10783677024632214784339361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189118016421476522892907 10783677024632214784339361)
          ·
            refine ⟨8087757768474161088254521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10783677024632214784339361 8087757768474161088254521)
            ·
              refine ⟨6065818326355620816190891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8087757768474161088254521 6065818326355620816190891)
              ·
                refine ⟨9098727489533431224286337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065818326355620816190891 9098727489533431224286337)
                ·
                  refine ⟨6824045617150073418214753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098727489533431224286337 6824045617150073418214753)
                  ·
                    refine ⟨5118034212862555063661065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6824045617150073418214753 5118034212862555063661065)
                    ·
                      refine ⟨3838525659646916297745799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118034212862555063661065 3838525659646916297745799)
                      ·
                        rfl

theorem cell23_7475502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7475502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475502 prefixEnd_7475502 := by exact prefixLift 7475502
  have htrace : WordTrace (prefixWord ++ tailWord_7475502) baseStart_7475502 baseEnd_7475502 := by
    simpa [prefixWord, tailWord_7475502, baseEnd_7475502] using wordTrace_append hprefix tailTrace_7475502
  have hstable : (prefixWord ++ tailWord_7475502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475502).length < 2 ^ (prefixWord ++ tailWord_7475502).sum := by decide
  have hdescent : baseEnd_7475502 < baseStart_7475502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475507 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 6, 2]
def baseStart_7475507 : Nat := 118140960795 + 7475507 * 2 ^ 59
def prefixEnd_7475507 : Nat := 4983230072969 + 3 ^ 40 * 7475507 * 2
def baseEnd_7475507 : Nat := 3838528227050188778183275

theorem tailTrace_7475507 : CollatzResearch.WordTrace tailWord_7475507 prefixEnd_7475507 3838528227050188778183275 := by
  unfold tailWord_7475507
  simp only [CollatzResearch.WordTrace]
  refine ⟨272654139728522328796240775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181769426485681552530827183 272654139728522328796240775)
  ·
    refine ⟨408981209592783493194361163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272654139728522328796240775 408981209592783493194361163)
    ·
      refine ⟨613471814389175239791541745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408981209592783493194361163 613471814389175239791541745)
      ·
        refine ⟨460103860791881429843656309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613471814389175239791541745 460103860791881429843656309)
        ·
          refine ⟨43134736949238884047842779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460103860791881429843656309 43134736949238884047842779)
          ·
            refine ⟨64702105423858326071764169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43134736949238884047842779 64702105423858326071764169)
            ·
              refine ⟨48526579067893744553823127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64702105423858326071764169 48526579067893744553823127)
              ·
                refine ⟨72789868601840616830734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48526579067893744553823127 72789868601840616830734691)
                ·
                  refine ⟨109184802902760925246102037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72789868601840616830734691 109184802902760925246102037)
                  ·
                    refine ⟨5118037636066918370911033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109184802902760925246102037 5118037636066918370911033)
                    ·
                      refine ⟨3838528227050188778183275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118037636066918370911033 3838528227050188778183275)
                      ·
                        rfl

theorem cell23_7475507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6, 2].length) (baseStart_7475507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475507 prefixEnd_7475507 := by exact prefixLift 7475507
  have htrace : WordTrace (prefixWord ++ tailWord_7475507) baseStart_7475507 baseEnd_7475507 := by
    simpa [prefixWord, tailWord_7475507, baseEnd_7475507] using wordTrace_append hprefix tailTrace_7475507
  have hstable : (prefixWord ++ tailWord_7475507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475507).length < 2 ^ (prefixWord ++ tailWord_7475507).sum := by decide
  have hdescent : baseEnd_7475507 < baseStart_7475507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475551 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 1, 4]
def baseStart_7475551 : Nat := 118140960795 + 7475551 * 2 ^ 59
def prefixEnd_7475551 : Nat := 4983230072969 + 3 ^ 40 * 7475551 * 2
def baseEnd_7475551 : Nat := 1279516940066328868677691

theorem tailTrace_7475551 : CollatzResearch.WordTrace tailWord_7475551 prefixEnd_7475551 1279516940066328868677691 := by
  unfold tailWord_7475551
  simp only [CollatzResearch.WordTrace]
  refine ⟨272655744540362924310842507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181770496360241949540561671 272655744540362924310842507)
  ·
    refine ⟨408983616810544386466263761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272655744540362924310842507 408983616810544386466263761)
    ·
      refine ⟨306737712607908289849697821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408983616810544386466263761 306737712607908289849697821)
      ·
        refine ⟨115026642227965608693636683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306737712607908289849697821 115026642227965608693636683)
        ·
          refine ⟨172539963341948413040455025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115026642227965608693636683 172539963341948413040455025)
          ·
            refine ⟨129404972506461309780341269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172539963341948413040455025 129404972506461309780341269)
            ·
              refine ⟨6065858086240373895953497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129404972506461309780341269 6065858086240373895953497)
              ·
                refine ⟨4549393564680280421965123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065858086240373895953497 4549393564680280421965123)
                ·
                  refine ⟨6824090347020420632947685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549393564680280421965123 6824090347020420632947685)
                  ·
                    refine ⟨1279516940066328868677691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6824090347020420632947685 1279516940066328868677691)
                    ·
                      rfl

theorem cell23_7475551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 1, 4].length) (baseStart_7475551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475551 prefixEnd_7475551 := by exact prefixLift 7475551
  have htrace : WordTrace (prefixWord ++ tailWord_7475551) baseStart_7475551 baseEnd_7475551 := by
    simpa [prefixWord, tailWord_7475551, baseEnd_7475551] using wordTrace_append hprefix tailTrace_7475551
  have hstable : (prefixWord ++ tailWord_7475551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475551).length < 2 ^ (prefixWord ++ tailWord_7475551).sum := by decide
  have hdescent : baseEnd_7475551 < baseStart_7475551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475577 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_7475577 : Nat := 118140960795 + 7475577 * 2 ^ 59
def prefixEnd_7475577 : Nat := 4983230072969 + 3 ^ 40 * 7475577 * 2
def baseEnd_7475577 : Nat := 1279521390232001168102651

theorem tailTrace_7475577 : CollatzResearch.WordTrace tailWord_7475577 prefixEnd_7475577 1279521390232001168102651 := by
  unfold tailWord_7475577
  simp only [CollatzResearch.WordTrace]
  refine ⟨272656692838268730751288985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181771128558845820500859323 272656692838268730751288985)
  ·
    refine ⟨204492519628701548063466739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272656692838268730751288985 204492519628701548063466739)
    ·
      refine ⟨306738779443052322095200109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204492519628701548063466739 306738779443052322095200109)
      ·
        refine ⟨115027042291144620785700041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306738779443052322095200109 115027042291144620785700041)
        ·
          refine ⟨86270281718358465589275031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115027042291144620785700041 86270281718358465589275031)
          ·
            refine ⟨129405422577537698383912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86270281718358465589275031 129405422577537698383912547)
            ·
              refine ⟨194108133866306547575868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129405422577537698383912547 194108133866306547575868821)
              ·
                refine ⟨9098818774983119417618851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194108133866306547575868821 9098818774983119417618851)
                ·
                  refine ⟨13648228162474679126428277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098818774983119417618851 13648228162474679126428277)
                  ·
                    refine ⟨1279521390232001168102651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13648228162474679126428277 1279521390232001168102651)
                    ·
                      rfl

theorem cell23_7475577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_7475577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475577 prefixEnd_7475577 := by exact prefixLift 7475577
  have htrace : WordTrace (prefixWord ++ tailWord_7475577) baseStart_7475577 baseEnd_7475577 := by
    simpa [prefixWord, tailWord_7475577, baseEnd_7475577] using wordTrace_append hprefix tailTrace_7475577
  have hstable : (prefixWord ++ tailWord_7475577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475577).length < 2 ^ (prefixWord ++ tailWord_7475577).sum := by decide
  have hdescent : baseEnd_7475577 < baseStart_7475577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475608 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7475608 : Nat := 118140960795 + 7475608 * 2 ^ 59
def prefixEnd_7475608 : Nat := 4983230072969 + 3 ^ 40 * 7475608 * 2
def baseEnd_7475608 : Nat := 3838580088596292883020311

theorem tailTrace_7475608 : CollatzResearch.WordTrace tailWord_7475608 prefixEnd_7475608 3838580088596292883020311 := by
  unfold tailWord_7475608
  simp only [CollatzResearch.WordTrace]
  refine ⟨136328911750578211522833739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181771882334104282030444985 136328911750578211522833739)
  ·
    refine ⟨204493367625867317284250609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136328911750578211522833739 204493367625867317284250609)
    ·
      refine ⟨153370025719400487963187957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204493367625867317284250609 153370025719400487963187957)
      ·
        refine ⟨14378439911193795746548871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153370025719400487963187957 14378439911193795746548871)
        ·
          refine ⟨21567659866790693619823307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378439911193795746548871 21567659866790693619823307)
          ·
            refine ⟨32351489800186040429734961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567659866790693619823307 32351489800186040429734961)
            ·
              refine ⟨24263617350139530322301221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32351489800186040429734961 24263617350139530322301221)
              ·
                refine ⟨4549428253151161935431479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24263617350139530322301221 4549428253151161935431479)
                ·
                  refine ⟨6824142379726742903147219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549428253151161935431479 6824142379726742903147219)
                  ·
                    refine ⟨10236213569590114354720829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6824142379726742903147219 10236213569590114354720829)
                    ·
                      refine ⟨3838580088596292883020311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10236213569590114354720829 3838580088596292883020311)
                      ·
                        rfl

theorem cell23_7475608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7475608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475608 prefixEnd_7475608 := by exact prefixLift 7475608
  have htrace : WordTrace (prefixWord ++ tailWord_7475608) baseStart_7475608 baseEnd_7475608 := by
    simpa [prefixWord, tailWord_7475608, baseEnd_7475608] using wordTrace_append hprefix tailTrace_7475608
  have hstable : (prefixWord ++ tailWord_7475608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475608).length < 2 ^ (prefixWord ++ tailWord_7475608).sum := by decide
  have hdescent : baseEnd_7475608 < baseStart_7475608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475681 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_7475681 : Nat := 118140960795 + 7475681 * 2 ^ 59
def prefixEnd_7475681 : Nat := 4983230072969 + 3 ^ 40 * 7475681 * 2
def baseEnd_7475681 : Nat := 3838617572684071097407475

theorem tailTrace_7475681 : CollatzResearch.WordTrace tailWord_7475681 prefixEnd_7475681 3838617572684071097407475 := by
  unfold tailWord_7475681
  simp only [CollatzResearch.WordTrace]
  refine ⟨272660486029891956513074897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181773657353261304342049931 272660486029891956513074897)
  ·
    refine ⟨204495364522418967384806173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272660486029891956513074897 204495364522418967384806173)
    ·
      refine ⟨76685761695907112769302315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204495364522418967384806173 76685761695907112769302315)
      ·
        refine ⟨115028642543860669153953473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76685761695907112769302315 115028642543860669153953473)
        ·
          refine ⟨86271481907895501865465105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115028642543860669153953473 86271481907895501865465105)
          ·
            refine ⟨64703611430921626399098829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86271481907895501865465105 64703611430921626399098829)
            ·
              refine ⟨24263854286595609899662061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64703611430921626399098829 24263854286595609899662061)
              ·
                refine ⟨9098945357473353712373273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24263854286595609899662061 9098945357473353712373273)
                ·
                  refine ⟨6824209018105015284279955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098945357473353712373273 6824209018105015284279955)
                  ·
                    refine ⟨10236313527157522926419933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6824209018105015284279955 10236313527157522926419933)
                    ·
                      refine ⟨3838617572684071097407475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10236313527157522926419933 3838617572684071097407475)
                      ·
                        rfl

theorem cell23_7475681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_7475681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475681 prefixEnd_7475681 := by exact prefixLift 7475681
  have htrace : WordTrace (prefixWord ++ tailWord_7475681) baseStart_7475681 baseEnd_7475681 := by
    simpa [prefixWord, tailWord_7475681, baseEnd_7475681] using wordTrace_append hprefix tailTrace_7475681
  have hstable : (prefixWord ++ tailWord_7475681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475681).length < 2 ^ (prefixWord ++ tailWord_7475681).sum := by decide
  have hdescent : baseEnd_7475681 < baseStart_7475681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475682 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7475682 : Nat := 118140960795 + 7475682 * 2 ^ 59
def prefixEnd_7475682 : Nat := 4983230072969 + 3 ^ 40 * 7475682 * 2
def baseEnd_7475682 : Nat := 3838618086164725593494971

theorem tailTrace_7475682 : CollatzResearch.WordTrace tailWord_7475682 prefixEnd_7475682 3838618086164725593494971 := by
  unfold tailWord_7475682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68165130625722083420965325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181773681668592222455907533 68165130625722083420965325)
  ·
    refine ⟨25561923984645781282861997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68165130625722083420965325 25561923984645781282861997)
    ·
      refine ⟨9585721494242167981073249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25561923984645781282861997 9585721494242167981073249)
      ·
        refine ⟨7189291120681625985804937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9585721494242167981073249 7189291120681625985804937)
        ·
          refine ⟨5391968340511219489353703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189291120681625985804937 5391968340511219489353703)
          ·
            refine ⟨8087952510766829234030555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391968340511219489353703 8087952510766829234030555)
            ·
              refine ⟨12131928766150243851045833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087952510766829234030555 12131928766150243851045833)
              ·
                refine ⟨9098946574612682888284375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12131928766150243851045833 9098946574612682888284375)
                ·
                  refine ⟨13648419861919024332426563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098946574612682888284375 13648419861919024332426563)
                  ·
                    refine ⟨20472629792878536498639845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13648419861919024332426563 20472629792878536498639845)
                    ·
                      refine ⟨3838618086164725593494971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20472629792878536498639845 3838618086164725593494971)
                      ·
                        rfl

theorem cell23_7475682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7475682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475682 prefixEnd_7475682 := by exact prefixLift 7475682
  have htrace : WordTrace (prefixWord ++ tailWord_7475682) baseStart_7475682 baseEnd_7475682 := by
    simpa [prefixWord, tailWord_7475682, baseEnd_7475682] using wordTrace_append hprefix tailTrace_7475682
  have hstable : (prefixWord ++ tailWord_7475682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475682).length < 2 ^ (prefixWord ++ tailWord_7475682).sum := by decide
  have hdescent : baseEnd_7475682 < baseStart_7475682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475685 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7475685 : Nat := 118140960795 + 7475685 * 2 ^ 59
def prefixEnd_7475685 : Nat := 4983230072969 + 3 ^ 40 * 7475685 * 2
def baseEnd_7475685 : Nat := 3838619626606689081757457

theorem tailTrace_7475685 : CollatzResearch.WordTrace tailWord_7475685 prefixEnd_7475685 3838619626606689081757457 := by
  unfold tailWord_7475685
  simp only [CollatzResearch.WordTrace]
  refine ⟨272660631921877465196220509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181773754614584976797480339 272660631921877465196220509)
  ·
    refine ⟨102247736970704049448582691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272660631921877465196220509 102247736970704049448582691)
    ·
      refine ⟨153371605456056074172874037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102247736970704049448582691 153371605456056074172874037)
      ·
        refine ⟨14378588011505256953706941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153371605456056074172874037 14378588011505256953706941)
        ·
          refine ⟨5391970504314471357640103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14378588011505256953706941 5391970504314471357640103)
          ·
            refine ⟨8087955756471707036460155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391970504314471357640103 8087955756471707036460155)
            ·
              refine ⟨12131933634707560554690233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087955756471707036460155 12131933634707560554690233)
              ·
                refine ⟨9098950226030670416017675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12131933634707560554690233 9098950226030670416017675)
                ·
                  refine ⟨13648425339046005624026513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098950226030670416017675 13648425339046005624026513)
                  ·
                    refine ⟨10236319004284504218019885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13648425339046005624026513 10236319004284504218019885)
                    ·
                      refine ⟨3838619626606689081757457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10236319004284504218019885 3838619626606689081757457)
                      ·
                        rfl

theorem cell23_7475685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7475685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475685 prefixEnd_7475685 := by exact prefixLift 7475685
  have htrace : WordTrace (prefixWord ++ tailWord_7475685) baseStart_7475685 baseEnd_7475685 := by
    simpa [prefixWord, tailWord_7475685, baseEnd_7475685] using wordTrace_append hprefix tailTrace_7475685
  have hstable : (prefixWord ++ tailWord_7475685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475685).length < 2 ^ (prefixWord ++ tailWord_7475685).sum := by decide
  have hdescent : baseEnd_7475685 < baseStart_7475685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475707 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3]
def baseStart_7475707 : Nat := 118140960795 + 7475707 * 2 ^ 59
def prefixEnd_7475707 : Nat := 4983230072969 + 3 ^ 40 * 7475707 * 2
def baseEnd_7475707 : Nat := 3838630923181087995682355

theorem tailTrace_7475707 : CollatzResearch.WordTrace tailWord_7475707 prefixEnd_7475707 3838630923181087995682355 := by
  unfold tailWord_7475707
  simp only [CollatzResearch.WordTrace]
  refine ⟨272661434327797762953521375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181774289551865175302347583 272661434327797762953521375)
  ·
    refine ⟨408992151491696644430282063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272661434327797762953521375 408992151491696644430282063)
    ·
      refine ⟨613488227237544966645423095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408992151491696644430282063 613488227237544966645423095)
      ·
        refine ⟨920232340856317449968134643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613488227237544966645423095 920232340856317449968134643)
        ·
          refine ⟨1380348511284476174952201965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920232340856317449968134643 1380348511284476174952201965)
          ·
            refine ⟨517630691731678565607075737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1380348511284476174952201965 517630691731678565607075737)
            ·
              refine ⟨388223018798758924205306803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517630691731678565607075737 388223018798758924205306803)
              ·
                refine ⟨582334528198138386307960205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388223018798758924205306803 582334528198138386307960205)
                ·
                  refine ⟨218375448074301894865485077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582334528198138386307960205 218375448074301894865485077)
                  ·
                    refine ⟨10236349128482901321819613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218375448074301894865485077 10236349128482901321819613)
                    ·
                      refine ⟨3838630923181087995682355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10236349128482901321819613 3838630923181087995682355)
                      ·
                        rfl

theorem cell23_7475707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3].length) (baseStart_7475707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475707 prefixEnd_7475707 := by exact prefixLift 7475707
  have htrace : WordTrace (prefixWord ++ tailWord_7475707) baseStart_7475707 baseEnd_7475707 := by
    simpa [prefixWord, tailWord_7475707, baseEnd_7475707] using wordTrace_append hprefix tailTrace_7475707
  have hstable : (prefixWord ++ tailWord_7475707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475707).length < 2 ^ (prefixWord ++ tailWord_7475707).sum := by decide
  have hdescent : baseEnd_7475707 < baseStart_7475707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475718 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7475718 : Nat := 118140960795 + 7475718 * 2 ^ 59
def prefixEnd_7475718 : Nat := 4983230072969 + 3 ^ 40 * 7475718 * 2
def baseEnd_7475718 : Nat := 1279545523822762484214935

theorem tailTrace_7475718 : CollatzResearch.WordTrace tailWord_7475718 prefixEnd_7475718 1279545523822762484214935 := by
  unfold tailWord_7475718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520682360336184744755369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181774557020505274554781205 8520682360336184744755369)
  ·
    refine ⟨6390511770252138558566527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8520682360336184744755369 6390511770252138558566527)
    ·
      refine ⟨9585767655378207837849791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390511770252138558566527 9585767655378207837849791)
      ·
        refine ⟨14378651483067311756774687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9585767655378207837849791 14378651483067311756774687)
        ·
          refine ⟨21567977224600967635162031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378651483067311756774687 21567977224600967635162031)
          ·
            refine ⟨32351965836901451452743047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567977224600967635162031 32351965836901451452743047)
            ·
              refine ⟨48527948755352177179114571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32351965836901451452743047 48527948755352177179114571)
              ·
                refine ⟨72791923133028265768671857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48527948755352177179114571 72791923133028265768671857)
                ·
                  refine ⟨54593942349771199326503893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72791923133028265768671857 54593942349771199326503893)
                  ·
                    refine ⟨1279545523822762484214935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54593942349771199326503893 1279545523822762484214935)
                    ·
                      rfl

theorem cell23_7475718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7475718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475718 prefixEnd_7475718 := by exact prefixLift 7475718
  have htrace : WordTrace (prefixWord ++ tailWord_7475718) baseStart_7475718 baseEnd_7475718 := by
    simpa [prefixWord, tailWord_7475718, baseEnd_7475718] using wordTrace_append hprefix tailTrace_7475718
  have hstable : (prefixWord ++ tailWord_7475718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475718).length < 2 ^ (prefixWord ++ tailWord_7475718).sum := by decide
  have hdescent : baseEnd_7475718 < baseStart_7475718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475724 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_7475724 : Nat := 118140960795 + 7475724 * 2 ^ 59
def prefixEnd_7475724 : Nat := 4983230072969 + 3 ^ 40 * 7475724 * 2
def baseEnd_7475724 : Nat := 3838639652352214429169777

theorem tailTrace_7475724 : CollatzResearch.WordTrace tailWord_7475724 prefixEnd_7475724 3838639652352214429169777 := by
  unfold tailWord_7475724
  simp only [CollatzResearch.WordTrace]
  refine ⟨136331027184368087428445113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181774702912490783237926817 136331027184368087428445113)
  ·
    refine ⟨102248270388276065571333835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136331027184368087428445113 102248270388276065571333835)
    ·
      refine ⟨153372405582414098357000753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102248270388276065571333835 153372405582414098357000753)
      ·
        refine ⟨115029304186810573767750565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153372405582414098357000753 115029304186810573767750565)
        ·
          refine ⟨21567994535026982581453231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115029304186810573767750565 21567994535026982581453231)
          ·
            refine ⟨32351991802540473872179847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567994535026982581453231 32351991802540473872179847)
            ·
              refine ⟨48527987703810710808269771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32351991802540473872179847 48527987703810710808269771)
              ·
                refine ⟨72791981555716066212404657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48527987703810710808269771 72791981555716066212404657)
                ·
                  refine ⟨54593986166787049659303493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72791981555716066212404657 54593986166787049659303493)
                  ·
                    refine ⟨10236372406272571811119405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54593986166787049659303493 10236372406272571811119405)
                    ·
                      refine ⟨3838639652352214429169777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10236372406272571811119405 3838639652352214429169777)
                      ·
                        rfl

theorem cell23_7475724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_7475724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475724 prefixEnd_7475724 := by exact prefixLift 7475724
  have htrace : WordTrace (prefixWord ++ tailWord_7475724) baseStart_7475724 baseEnd_7475724 := by
    simpa [prefixWord, tailWord_7475724, baseEnd_7475724] using wordTrace_append hprefix tailTrace_7475724
  have hstable : (prefixWord ++ tailWord_7475724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475724).length < 2 ^ (prefixWord ++ tailWord_7475724).sum := by decide
  have hdescent : baseEnd_7475724 < baseStart_7475724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475725 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7475725 : Nat := 118140960795 + 7475725 * 2 ^ 59
def prefixEnd_7475725 : Nat := 4983230072969 + 3 ^ 40 * 7475725 * 2
def baseEnd_7475725 : Nat := 3838640165832868925257273

theorem tailTrace_7475725 : CollatzResearch.WordTrace tailWord_7475725 prefixEnd_7475725 3838640165832868925257273 := by
  unfold tailWord_7475725
  simp only [CollatzResearch.WordTrace]
  refine ⟨272662090841732552027676629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181774727227821701351784419 272662090841732552027676629)
  ·
    refine ⟨6390517754103106688148671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 272662090841732552027676629 6390517754103106688148671)
    ·
      refine ⟨9585776631154660032223007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390517754103106688148671 9585776631154660032223007)
      ·
        refine ⟨14378664946731990048334511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9585776631154660032223007 14378664946731990048334511)
        ·
          refine ⟨21567997420097985072501767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378664946731990048334511 21567997420097985072501767)
          ·
            refine ⟨32351996130146977608752651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567997420097985072501767 32351996130146977608752651)
            ·
              refine ⟨48527994195220466413128977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32351996130146977608752651 48527994195220466413128977)
              ·
                refine ⟨36395995646415349809846733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48527994195220466413128977 36395995646415349809846733)
                ·
                  refine ⟨13648498367405756178692525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36395995646415349809846733 13648498367405756178692525)
                  ·
                    refine ⟨5118186887777158567009697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13648498367405756178692525 5118186887777158567009697)
                    ·
                      refine ⟨3838640165832868925257273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118186887777158567009697 3838640165832868925257273)
                      ·
                        rfl

theorem cell23_7475725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7475725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475725 prefixEnd_7475725 := by exact prefixLift 7475725
  have htrace : WordTrace (prefixWord ++ tailWord_7475725) baseStart_7475725 baseEnd_7475725 := by
    simpa [prefixWord, tailWord_7475725, baseEnd_7475725] using wordTrace_append hprefix tailTrace_7475725
  have hstable : (prefixWord ++ tailWord_7475725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475725).length < 2 ^ (prefixWord ++ tailWord_7475725).sum := by decide
  have hdescent : baseEnd_7475725 < baseStart_7475725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475738 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_7475738 : Nat := 118140960795 + 7475738 * 2 ^ 59
def prefixEnd_7475738 : Nat := 4983230072969 + 3 ^ 40 * 7475738 * 2
def baseEnd_7475738 : Nat := 3838646841081377374394713

theorem tailTrace_7475738 : CollatzResearch.WordTrace tailWord_7475738 prefixEnd_7475738 3838646841081377374394713 := by
  unfold tailWord_7475738
  simp only [CollatzResearch.WordTrace]
  refine ⟨68165641247671363811974967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181775043327123636831933245 68165641247671363811974967)
  ·
    refine ⟨102248461871507045717962451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68165641247671363811974967 102248461871507045717962451)
    ·
      refine ⟨153372692807260568576943677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102248461871507045717962451 153372692807260568576943677)
      ·
        refine ⟨57514759802722713216353879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153372692807260568576943677 57514759802722713216353879)
        ·
          refine ⟨86272139704084069824530819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57514759802722713216353879 86272139704084069824530819)
          ·
            refine ⟨129408209556126104736796229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86272139704084069824530819 129408209556126104736796229)
            ·
              refine ⟨24264039291773644638149293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129408209556126104736796229 24264039291773644638149293)
              ·
                refine ⟨9099014734415116739305985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24264039291773644638149293 9099014734415116739305985)
                ·
                  refine ⟨6824261050811337554479489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9099014734415116739305985 6824261050811337554479489)
                  ·
                    refine ⟨5118195788108503165859617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6824261050811337554479489 5118195788108503165859617)
                    ·
                      refine ⟨3838646841081377374394713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118195788108503165859617 3838646841081377374394713)
                      ·
                        rfl

theorem cell23_7475738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_7475738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475738 prefixEnd_7475738 := by exact prefixLift 7475738
  have htrace : WordTrace (prefixWord ++ tailWord_7475738) baseStart_7475738 baseEnd_7475738 := by
    simpa [prefixWord, tailWord_7475738, baseEnd_7475738] using wordTrace_append hprefix tailTrace_7475738
  have hstable : (prefixWord ++ tailWord_7475738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475738).length < 2 ^ (prefixWord ++ tailWord_7475738).sum := by decide
  have hdescent : baseEnd_7475738 < baseStart_7475738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475794 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7475794 : Nat := 118140960795 + 7475794 * 2 ^ 59
def prefixEnd_7475794 : Nat := 4983230072969 + 3 ^ 40 * 7475794 * 2
def baseEnd_7475794 : Nat := 3838675595998029155294455

theorem tailTrace_7475794 : CollatzResearch.WordTrace tailWord_7475794 prefixEnd_7475794 3838675595998029155294455 := by
  unfold tailWord_7475794
  simp only [CollatzResearch.WordTrace]
  refine ⟨68166151869620644202984609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181776404985655051207958957 68166151869620644202984609)
  ·
    refine ⟨51124613902215483152238457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68166151869620644202984609 51124613902215483152238457)
    ·
      refine ⟨38343460426661612364178843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51124613902215483152238457 38343460426661612364178843)
      ·
        refine ⟨57515190639992418546268265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38343460426661612364178843 57515190639992418546268265)
        ·
          refine ⟨43136392979994313909701199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57515190639992418546268265 43136392979994313909701199)
          ·
            refine ⟨64704589469991470864551799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43136392979994313909701199 64704589469991470864551799)
            ·
              refine ⟨97056884204987206296827699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64704589469991470864551799 97056884204987206296827699)
              ·
                refine ⟨145585326307480809445241549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97056884204987206296827699 145585326307480809445241549)
                ·
                  refine ⟨54594497365305303541965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145585326307480809445241549 54594497365305303541965581)
                  ·
                    refine ⟨20472936511989488828237093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54594497365305303541965581 20472936511989488828237093)
                    ·
                      refine ⟨3838675595998029155294455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20472936511989488828237093 3838675595998029155294455)
                      ·
                        rfl

theorem cell23_7475794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7475794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475794 prefixEnd_7475794 := by exact prefixLift 7475794
  have htrace : WordTrace (prefixWord ++ tailWord_7475794) baseStart_7475794 baseEnd_7475794 := by
    simpa [prefixWord, tailWord_7475794, baseEnd_7475794] using wordTrace_append hprefix tailTrace_7475794
  have hstable : (prefixWord ++ tailWord_7475794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475794).length < 2 ^ (prefixWord ++ tailWord_7475794).sum := by decide
  have hdescent : baseEnd_7475794 < baseStart_7475794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475889 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 1, 4]
def baseStart_7475889 : Nat := 118140960795 + 7475889 * 2 ^ 59
def prefixEnd_7475889 : Nat := 4983230072969 + 3 ^ 40 * 7475889 * 2
def baseEnd_7475889 : Nat := 1279574792220068761202173

theorem tailTrace_7475889 : CollatzResearch.WordTrace tailWord_7475889 prefixEnd_7475889 1279574792220068761202173 := by
  unfold tailWord_7475889
  simp only [CollatzResearch.WordTrace]
  refine ⟨272668072413138408036646721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181778714942092272024431147 272668072413138408036646721)
  ·
    refine ⟨204501054309853806027485041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272668072413138408036646721 204501054309853806027485041)
    ·
      refine ⟨153375790732390354520613781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204501054309853806027485041 153375790732390354520613781)
      ·
        refine ⟨7189490190580797868153771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153375790732390354520613781 7189490190580797868153771)
        ·
          refine ⟨10784235285871196802230657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189490190580797868153771 10784235285871196802230657)
          ·
            refine ⟨8088176464403397601672993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10784235285871196802230657 8088176464403397601672993)
            ·
              refine ⟨6066132348302548201254745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088176464403397601672993 6066132348302548201254745)
              ·
                refine ⟨4549599261226911150941059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066132348302548201254745 4549599261226911150941059)
                ·
                  refine ⟨6824398891840366726411589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549599261226911150941059 6824398891840366726411589)
                  ·
                    refine ⟨1279574792220068761202173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6824398891840366726411589 1279574792220068761202173)
                    ·
                      rfl

theorem cell23_7475889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_7475889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475889 prefixEnd_7475889 := by exact prefixLift 7475889
  have htrace : WordTrace (prefixWord ++ tailWord_7475889) baseStart_7475889 baseEnd_7475889 := by
    simpa [prefixWord, tailWord_7475889, baseEnd_7475889] using wordTrace_append hprefix tailTrace_7475889
  have hstable : (prefixWord ++ tailWord_7475889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475889).length < 2 ^ (prefixWord ++ tailWord_7475889).sum := by decide
  have hdescent : baseEnd_7475889 < baseStart_7475889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475901 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7475901 : Nat := 118140960795 + 7475901 * 2 ^ 59
def prefixEnd_7475901 : Nat := 4983230072969 + 3 ^ 40 * 7475901 * 2
def baseEnd_7475901 : Nat := 3838730538428060236656463

theorem tailTrace_7475901 : CollatzResearch.WordTrace tailWord_7475901 prefixEnd_7475901 3838730538428060236656463 := by
  unfold tailWord_7475901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272668510089094934086083557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181779006726063289390722371 272668510089094934086083557)
  ·
    refine ⟨51125345641705300141140667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272668510089094934086083557 51125345641705300141140667)
    ·
      refine ⟨76688018462557950211711001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51125345641705300141140667 76688018462557950211711001)
      ·
        refine ⟨57516013846918462658783251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76688018462557950211711001 57516013846918462658783251)
        ·
          refine ⟨86274020770377693988174877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57516013846918462658783251 86274020770377693988174877)
          ·
            refine ⟨32352757788891635245565579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86274020770377693988174877 32352757788891635245565579)
            ·
              refine ⟨48529136683337452868348369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32352757788891635245565579 48529136683337452868348369)
              ·
                refine ⟨36396852512503089651261277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48529136683337452868348369 36396852512503089651261277)
                ·
                  refine ⟨13648819692188658619222979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36396852512503089651261277 13648819692188658619222979)
                  ·
                    refine ⟨20473229538282987928834469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13648819692188658619222979 20473229538282987928834469)
                    ·
                      refine ⟨3838730538428060236656463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20473229538282987928834469 3838730538428060236656463)
                      ·
                        rfl

theorem cell23_7475901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7475901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475901 prefixEnd_7475901 := by exact prefixLift 7475901
  have htrace : WordTrace (prefixWord ++ tailWord_7475901) baseStart_7475901 baseEnd_7475901 := by
    simpa [prefixWord, tailWord_7475901, baseEnd_7475901] using wordTrace_append hprefix tailTrace_7475901
  have hstable : (prefixWord ++ tailWord_7475901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475901).length < 2 ^ (prefixWord ++ tailWord_7475901).sum := by decide
  have hdescent : baseEnd_7475901 < baseStart_7475901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475921 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_7475921 : Nat := 118140960795 + 7475921 * 2 ^ 59
def prefixEnd_7475921 : Nat := 4983230072969 + 3 ^ 40 * 7475921 * 2
def baseEnd_7475921 : Nat := 3838740808041150158406371

theorem tailTrace_7475921 : CollatzResearch.WordTrace tailWord_7475921 prefixEnd_7475921 3838740808041150158406371 := by
  unfold tailWord_7475921
  simp only [CollatzResearch.WordTrace]
  refine ⟨272669239549022477501811617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181779493032681651667874411 272669239549022477501811617)
  ·
    refine ⟨204501929661766858126358713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272669239549022477501811617 204501929661766858126358713)
    ·
      refine ⟨153376447246325143594769035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204501929661766858126358713 153376447246325143594769035)
      ·
        refine ⟨230064670869487715392153553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153376447246325143594769035 230064670869487715392153553)
        ·
          refine ⟨172548503152115786544115165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230064670869487715392153553 172548503152115786544115165)
          ·
            refine ⟨64705688682043419954043187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172548503152115786544115165 64705688682043419954043187)
            ·
              refine ⟨97058533023065129931064781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64705688682043419954043187 97058533023065129931064781)
              ·
                refine ⟨36396949883649423724149293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97058533023065129931064781 36396949883649423724149293)
                ·
                  refine ⟨13648856206368533896555985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36396949883649423724149293 13648856206368533896555985)
                  ·
                    refine ⟨10236642154776400422416989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13648856206368533896555985 10236642154776400422416989)
                    ·
                      refine ⟨3838740808041150158406371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10236642154776400422416989 3838740808041150158406371)
                      ·
                        rfl

theorem cell23_7475921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_7475921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475921 prefixEnd_7475921 := by exact prefixLift 7475921
  have htrace : WordTrace (prefixWord ++ tailWord_7475921) baseStart_7475921 baseEnd_7475921 := by
    simpa [prefixWord, tailWord_7475921, baseEnd_7475921] using wordTrace_append hprefix tailTrace_7475921
  have hstable : (prefixWord ++ tailWord_7475921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475921).length < 2 ^ (prefixWord ++ tailWord_7475921).sum := by decide
  have hdescent : baseEnd_7475921 < baseStart_7475921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475922 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7475922 : Nat := 118140960795 + 7475922 * 2 ^ 59
def prefixEnd_7475922 : Nat := 4983230072969 + 3 ^ 40 * 7475922 * 2
def baseEnd_7475922 : Nat := 3838741321521804654493867

theorem tailTrace_7475922 : CollatzResearch.WordTrace tailWord_7475922 prefixEnd_7475922 3838741321521804654493867 := by
  unfold tailWord_7475922
  simp only [CollatzResearch.WordTrace]
  refine ⟨68167319005504713668149505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181779517348012569781732013 68167319005504713668149505)
  ·
    refine ⟨51125489254128535251112129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68167319005504713668149505 51125489254128535251112129)
    ·
      refine ⟨38344116940596401438334097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51125489254128535251112129 38344116940596401438334097)
      ·
        refine ⟨28758087705447301078750573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38344116940596401438334097 28758087705447301078750573)
        ·
          refine ⟨10784282889542737904531465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28758087705447301078750573 10784282889542737904531465)
          ·
            refine ⟨8088212167157053428398599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10784282889542737904531465 8088212167157053428398599)
            ·
              refine ⟨12132318250735580142597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088212167157053428398599 12132318250735580142597899)
              ·
                refine ⟨18198477376103370213896849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12132318250735580142597899 18198477376103370213896849)
                ·
                  refine ⟨13648858032077527660422637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18198477376103370213896849 13648858032077527660422637)
                  ·
                    refine ⟨5118321762029072872658489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13648858032077527660422637 5118321762029072872658489)
                    ·
                      refine ⟨3838741321521804654493867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118321762029072872658489 3838741321521804654493867)
                      ·
                        rfl

theorem cell23_7475922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7475922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475922 prefixEnd_7475922 := by exact prefixLift 7475922
  have htrace : WordTrace (prefixWord ++ tailWord_7475922) baseStart_7475922 baseEnd_7475922 := by
    simpa [prefixWord, tailWord_7475922, baseEnd_7475922] using wordTrace_append hprefix tailTrace_7475922
  have hstable : (prefixWord ++ tailWord_7475922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475922).length < 2 ^ (prefixWord ++ tailWord_7475922).sum := by decide
  have hdescent : baseEnd_7475922 < baseStart_7475922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475932 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7475932 : Nat := 118140960795 + 7475932 * 2 ^ 59
def prefixEnd_7475932 : Nat := 4983230072969 + 3 ^ 40 * 7475932 * 2
def baseEnd_7475932 : Nat := 1279582152109449871789607

theorem tailTrace_7475932 : CollatzResearch.WordTrace tailWord_7475932 prefixEnd_7475932 1279582152109449871789607 := by
  unfold tailWord_7475932
  simp only [CollatzResearch.WordTrace]
  refine ⟨136334820375991313190231025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181779760501321750920308033 136334820375991313190231025)
  ·
    refine ⟨102251115281993484892673269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136334820375991313190231025 102251115281993484892673269)
    ·
      refine ⟨9586042057686889208688119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102251115281993484892673269 9586042057686889208688119)
      ·
        refine ⟨14379063086530333813032179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586042057686889208688119 14379063086530333813032179)
        ·
          refine ⟨21568594629795500719548269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379063086530333813032179 21568594629795500719548269)
          ·
            refine ⟨8088222986173312769830601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21568594629795500719548269 8088222986173312769830601)
            ·
              refine ⟨6066167239629984577372951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088222986173312769830601 6066167239629984577372951)
              ·
                refine ⟨9099250859444976866059427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066167239629984577372951 9099250859444976866059427)
                ·
                  refine ⟨13648876289167465299089141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099250859444976866059427 13648876289167465299089141)
                  ·
                    refine ⟨1279582152109449871789607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13648876289167465299089141 1279582152109449871789607)
                    ·
                      rfl

theorem cell23_7475932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7475932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475932 prefixEnd_7475932 := by exact prefixLift 7475932
  have htrace : WordTrace (prefixWord ++ tailWord_7475932) baseStart_7475932 baseEnd_7475932 := by
    simpa [prefixWord, tailWord_7475932, baseEnd_7475932] using wordTrace_append hprefix tailTrace_7475932
  have hstable : (prefixWord ++ tailWord_7475932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475932).length < 2 ^ (prefixWord ++ tailWord_7475932).sum := by decide
  have hdescent : baseEnd_7475932 < baseStart_7475932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475935 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 1, 1, 4]
def baseStart_7475935 : Nat := 118140960795 + 7475935 * 2 ^ 59
def prefixEnd_7475935 : Nat := 4983230072969 + 3 ^ 40 * 7475935 * 2
def baseEnd_7475935 : Nat := 3838747996770313103631307

theorem tailTrace_7475935 : CollatzResearch.WordTrace tailWord_7475935 prefixEnd_7475935 3838747996770313103631307 := by
  unfold tailWord_7475935
  simp only [CollatzResearch.WordTrace]
  refine ⟨272669750170971757892821259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181779833447314505261880839 272669750170971757892821259)
  ·
    refine ⟨409004625256457636839231889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272669750170971757892821259 409004625256457636839231889)
    ·
      refine ⟨306753468942343227629423917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409004625256457636839231889 306753468942343227629423917)
      ·
        refine ⟨115032550853378710361033969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306753468942343227629423917 115032550853378710361033969)
        ·
          refine ⟨86274413140034032770775477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115032550853378710361033969 86274413140034032770775477)
          ·
            refine ⟨8088226231878190572260201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86274413140034032770775477 8088226231878190572260201)
            ·
              refine ⟨6066169673908642929195151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088226231878190572260201 6066169673908642929195151)
              ·
                refine ⟨9099254510862964393792727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066169673908642929195151 9099254510862964393792727)
                ·
                  refine ⟨13648881766294446590689091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099254510862964393792727 13648881766294446590689091)
                  ·
                    refine ⟨20473322649441669886033637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13648881766294446590689091 20473322649441669886033637)
                    ·
                      refine ⟨3838747996770313103631307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20473322649441669886033637 3838747996770313103631307)
                      ·
                        rfl

theorem cell23_7475935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_7475935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475935 prefixEnd_7475935 := by exact prefixLift 7475935
  have htrace : WordTrace (prefixWord ++ tailWord_7475935) baseStart_7475935 baseEnd_7475935 := by
    simpa [prefixWord, tailWord_7475935, baseEnd_7475935] using wordTrace_append hprefix tailTrace_7475935
  have hstable : (prefixWord ++ tailWord_7475935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475935).length < 2 ^ (prefixWord ++ tailWord_7475935).sum := by decide
  have hdescent : baseEnd_7475935 < baseStart_7475935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476029 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7476029 : Nat := 118140960795 + 7476029 * 2 ^ 59
def prefixEnd_7476029 : Nat := 4983230072969 + 3 ^ 40 * 7476029 * 2
def baseEnd_7476029 : Nat := 3838796263951835735855875

theorem tailTrace_7476029 : CollatzResearch.WordTrace tailWord_7476029 prefixEnd_7476029 3838796263951835735855875 := by
  unfold tailWord_7476029
  simp only [CollatzResearch.WordTrace]
  refine ⟨272673178632631211946743141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181782119088420807964495427 272673178632631211946743141)
  ·
    refine ⟨51126220993618352240014339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272673178632631211946743141 51126220993618352240014339)
    ·
      refine ⟨76689331490427528360021509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51126220993618352240014339 76689331490427528360021509)
      ·
        refine ⟨14379249654455161567504033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76689331490427528360021509 14379249654455161567504033)
        ·
          refine ⟨10784437240841371175628025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14379249654455161567504033 10784437240841371175628025)
          ·
            refine ⟨8088327930631028381721019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10784437240841371175628025 8088327930631028381721019)
            ·
              refine ⟨12132491895946542572581529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088327930631028381721019 12132491895946542572581529)
              ·
                refine ⟨9099368921959906929436147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12132491895946542572581529 9099368921959906929436147)
                ·
                  refine ⟨13649053382939860394154221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099368921959906929436147 13649053382939860394154221)
                  ·
                    refine ⟨5118395018602447647807833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13649053382939860394154221 5118395018602447647807833)
                    ·
                      refine ⟨3838796263951835735855875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118395018602447647807833 3838796263951835735855875)
                      ·
                        rfl

theorem cell23_7476029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7476029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476029 prefixEnd_7476029 := by exact prefixLift 7476029
  have htrace : WordTrace (prefixWord ++ tailWord_7476029) baseStart_7476029 baseEnd_7476029 := by
    simpa [prefixWord, tailWord_7476029, baseEnd_7476029] using wordTrace_append hprefix tailTrace_7476029
  have hstable : (prefixWord ++ tailWord_7476029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476029).length < 2 ^ (prefixWord ++ tailWord_7476029).sum := by decide
  have hdescent : baseEnd_7476029 < baseStart_7476029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476125 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_7476125 : Nat := 118140960795 + 7476125 * 2 ^ 59
def prefixEnd_7476125 : Nat := 4983230072969 + 3 ^ 40 * 7476125 * 2
def baseEnd_7476125 : Nat := 1279615186031555786751811

theorem tailTrace_7476125 : CollatzResearch.WordTrace tailWord_7476125 prefixEnd_7476125 1279615186031555786751811 := by
  unfold tailWord_7476125
  simp only [CollatzResearch.WordTrace]
  refine ⟨272676680040283420342237829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181784453360188946894825219 272676680040283420342237829)
  ·
    refine ⟨51126877507553141314169593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272676680040283420342237829 51126877507553141314169593)
    ·
      refine ⟨38345158130664855985627195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51126877507553141314169593 38345158130664855985627195)
      ·
        refine ⟨57517737195997283978440793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38345158130664855985627195 57517737195997283978440793)
        ·
          refine ⟨43138302896997962983830595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57517737195997283978440793 43138302896997962983830595)
          ·
            refine ⟨64707454345496944475745893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43138302896997962983830595 64707454345496944475745893)
            ·
              refine ⟨12132647689780677089202355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64707454345496944475745893 12132647689780677089202355)
              ·
                refine ⟨18198971534671015633803533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12132647689780677089202355 18198971534671015633803533)
                ·
                  refine ⟨6824614325501630862676325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18198971534671015633803533 6824614325501630862676325)
                  ·
                    refine ⟨1279615186031555786751811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6824614325501630862676325 1279615186031555786751811)
                    ·
                      rfl

theorem cell23_7476125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_7476125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476125 prefixEnd_7476125 := by exact prefixLift 7476125
  have htrace : WordTrace (prefixWord ++ tailWord_7476125) baseStart_7476125 baseEnd_7476125 := by
    simpa [prefixWord, tailWord_7476125, baseEnd_7476125] using wordTrace_append hprefix tailTrace_7476125
  have hstable : (prefixWord ++ tailWord_7476125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476125).length < 2 ^ (prefixWord ++ tailWord_7476125).sum := by decide
  have hdescent : baseEnd_7476125 < baseStart_7476125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476175 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 4, 3, 2]
def baseStart_7476175 : Nat := 118140960795 + 7476175 * 2 ^ 59
def prefixEnd_7476175 : Nat := 4983230072969 + 3 ^ 40 * 7476175 * 2
def baseEnd_7476175 : Nat := 3838871232127392164630203

theorem tailTrace_7476175 : CollatzResearch.WordTrace tailWord_7476175 prefixEnd_7476175 3838871232127392164630203 := by
  unfold tailWord_7476175
  simp only [CollatzResearch.WordTrace]
  refine ⟨272678503690102278881557979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181785669126734852587705319 272678503690102278881557979)
  ·
    refine ⟨409017755535153418322336969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272678503690102278881557979 409017755535153418322336969)
    ·
      refine ⟨306763316651365063741752727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409017755535153418322336969 306763316651365063741752727)
      ·
        refine ⟨460144974977047595612629091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306763316651365063741752727 460144974977047595612629091)
        ·
          refine ⟨690217462465571393418943637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460144974977047595612629091 690217462465571393418943637)
          ·
            refine ⟨32353943553073659066512983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 690217462465571393418943637 32353943553073659066512983)
            ·
              refine ⟨48530915329610488599769475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32353943553073659066512983 48530915329610488599769475)
              ·
                refine ⟨72796372994415732899654213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48530915329610488599769475 72796372994415732899654213)
                ·
                  refine ⟨13649319936452949918685165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72796372994415732899654213 13649319936452949918685165)
                  ·
                    refine ⟨5118494976169856219506937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13649319936452949918685165 5118494976169856219506937)
                    ·
                      refine ⟨3838871232127392164630203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118494976169856219506937 3838871232127392164630203)
                      ·
                        rfl

theorem cell23_7476175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3, 2].length) (baseStart_7476175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476175 prefixEnd_7476175 := by exact prefixLift 7476175
  have htrace : WordTrace (prefixWord ++ tailWord_7476175) baseStart_7476175 baseEnd_7476175 := by
    simpa [prefixWord, tailWord_7476175, baseEnd_7476175] using wordTrace_append hprefix tailTrace_7476175
  have hstable : (prefixWord ++ tailWord_7476175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476175).length < 2 ^ (prefixWord ++ tailWord_7476175).sum := by decide
  have hdescent : baseEnd_7476175 < baseStart_7476175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476202 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_7476202 : Nat := 118140960795 + 7476202 * 2 ^ 59
def prefixEnd_7476202 : Nat := 4983230072969 + 3 ^ 40 * 7476202 * 2
def baseEnd_7476202 : Nat := 1279628365368354519664193

theorem tailTrace_7476202 : CollatzResearch.WordTrace tailWord_7476202 prefixEnd_7476202 1279628365368354519664193 := by
  unfold tailWord_7476202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68169872115251115623197715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181786325640669641661860573 68169872115251115623197715)
  ·
    refine ⟨102254808172876673434796573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68169872115251115623197715 102254808172876673434796573)
    ·
      refine ⟨38345553064828752538048715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102254808172876673434796573 38345553064828752538048715)
      ·
        refine ⟨57518329597243128807073073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38345553064828752538048715 57518329597243128807073073)
        ·
          refine ⟨43138747197932346605304805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57518329597243128807073073 43138747197932346605304805)
          ·
            refine ⟨8088515099612314988494651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43138747197932346605304805 8088515099612314988494651)
            ·
              refine ⟨12132772649418472482741977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088515099612314988494651 12132772649418472482741977)
              ·
                refine ⟨9099579487063854362056483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12132772649418472482741977 9099579487063854362056483)
                ·
                  refine ⟨13649369230595781543084725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099579487063854362056483 13649369230595781543084725)
                  ·
                    refine ⟨1279628365368354519664193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13649369230595781543084725 1279628365368354519664193)
                    ·
                      rfl

theorem cell23_7476202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_7476202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476202 prefixEnd_7476202 := by exact prefixLift 7476202
  have htrace : WordTrace (prefixWord ++ tailWord_7476202) baseStart_7476202 baseEnd_7476202 := by
    simpa [prefixWord, tailWord_7476202, baseEnd_7476202] using wordTrace_append hprefix tailTrace_7476202
  have hstable : (prefixWord ++ tailWord_7476202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476202).length < 2 ^ (prefixWord ++ tailWord_7476202).sum := by decide
  have hdescent : baseEnd_7476202 < baseStart_7476202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476225 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_7476225 : Nat := 118140960795 + 7476225 * 2 ^ 59
def prefixEnd_7476225 : Nat := 4983230072969 + 3 ^ 40 * 7476225 * 2
def baseEnd_7476225 : Nat := 3838896906160116969004973

theorem tailTrace_7476225 : CollatzResearch.WordTrace tailWord_7476225 prefixEnd_7476225 3838896906160116969004973 := by
  unfold tailWord_7476225
  simp only [CollatzResearch.WordTrace]
  refine ⟨272680327339921137420878129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181786884893280758280585419 272680327339921137420878129)
  ·
    refine ⟨204510245504940853065658597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272680327339921137420878129 204510245504940853065658597)
    ·
      refine ⟨38345671032176409949810987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204510245504940853065658597 38345671032176409949810987)
      ·
        refine ⟨57518506548264614924716481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38345671032176409949810987 57518506548264614924716481)
        ·
          refine ⟨43138879911198461193537361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57518506548264614924716481 43138879911198461193537361)
          ·
            refine ⟨32354159933398845895153021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43138879911198461193537361 32354159933398845895153021)
            ·
              refine ⟨12132809975024567210682383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32354159933398845895153021 12132809975024567210682383)
              ·
                refine ⟨18199214962536850816023575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12132809975024567210682383 18199214962536850816023575)
                ·
                  refine ⟨27298822443805276224035363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18199214962536850816023575 27298822443805276224035363)
                  ·
                    refine ⟨40948233665707914336053045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27298822443805276224035363 40948233665707914336053045)
                    ·
                      refine ⟨3838896906160116969004973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40948233665707914336053045 3838896906160116969004973)
                      ·
                        rfl

theorem cell23_7476225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_7476225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476225 prefixEnd_7476225 := by exact prefixLift 7476225
  have htrace : WordTrace (prefixWord ++ tailWord_7476225) baseStart_7476225 baseEnd_7476225 := by
    simpa [prefixWord, tailWord_7476225, baseEnd_7476225] using wordTrace_append hprefix tailTrace_7476225
  have hstable : (prefixWord ++ tailWord_7476225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476225).length < 2 ^ (prefixWord ++ tailWord_7476225).sum := by decide
  have hdescent : baseEnd_7476225 < baseStart_7476225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476232 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_7476232 : Nat := 118140960795 + 7476232 * 2 ^ 59
def prefixEnd_7476232 : Nat := 4983230072969 + 3 ^ 40 * 7476232 * 2
def baseEnd_7476232 : Nat := 1279633500174899480539147

theorem tailTrace_7476232 : CollatzResearch.WordTrace tailWord_7476232 prefixEnd_7476232 1279633500174899480539147 := by
  unfold tailWord_7476232
  simp only [CollatzResearch.WordTrace]
  refine ⟨136340291325447888808191475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181787055100597185077588633 136340291325447888808191475)
  ·
    refine ⟨204510436988171833212287213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136340291325447888808191475 204510436988171833212287213)
    ·
      refine ⟨76691413870564437454607705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204510436988171833212287213 76691413870564437454607705)
      ·
        refine ⟨57518560402923328090955779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76691413870564437454607705 57518560402923328090955779)
        ·
          refine ⟨86277840604384992136433669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57518560402923328090955779 86277840604384992136433669)
          ·
            refine ⟨16177095113322186025581313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86277840604384992136433669 16177095113322186025581313)
            ·
              refine ⟨12132821334991639519185985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16177095113322186025581313 12132821334991639519185985)
              ·
                refine ⟨9099616001243729639389489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12132821334991639519185985 9099616001243729639389489)
                ·
                  refine ⟨6824712000932797229542117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9099616001243729639389489 6824712000932797229542117)
                  ·
                    refine ⟨1279633500174899480539147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6824712000932797229542117 1279633500174899480539147)
                    ·
                      rfl

theorem cell23_7476232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_7476232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476232 prefixEnd_7476232 := by exact prefixLift 7476232
  have htrace : WordTrace (prefixWord ++ tailWord_7476232) baseStart_7476232 baseEnd_7476232 := by
    simpa [prefixWord, tailWord_7476232, baseEnd_7476232] using wordTrace_append hprefix tailTrace_7476232
  have hstable : (prefixWord ++ tailWord_7476232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476232).length < 2 ^ (prefixWord ++ tailWord_7476232).sum := by decide
  have hdescent : baseEnd_7476232 < baseStart_7476232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476245 : List Nat := [1, 3, 2, 1, 4, 3, 1, 8]
def baseStart_7476245 : Nat := 118140960795 + 7476245 * 2 ^ 59
def prefixEnd_7476245 : Nat := 4983230072969 + 3 ^ 40 * 7476245 * 2
def baseEnd_7476245 : Nat := 142181747250859514472403

theorem tailTrace_7476245 : CollatzResearch.WordTrace tailWord_7476245 prefixEnd_7476245 142181747250859514472403 := by
  unfold tailWord_7476245
  simp only [CollatzResearch.WordTrace]
  refine ⟨272681056799848680836606189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181787371199899120557737459 272681056799848680836606189)
  ·
    refine ⟨102255396299943255313727321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272681056799848680836606189 102255396299943255313727321)
    ·
      refine ⟨76691547224957441485295491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102255396299943255313727321 76691547224957441485295491)
      ·
        refine ⟨115037320837436162227943237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76691547224957441485295491 115037320837436162227943237)
        ·
          refine ⟨21569497657019280417739357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115037320837436162227943237 21569497657019280417739357)
          ·
            refine ⟨8088561621382230156652259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21569497657019280417739357 8088561621382230156652259)
            ·
              refine ⟨12132842432073345234978389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088561621382230156652259 12132842432073345234978389)
              ·
                refine ⟨142181747250859514472403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12132842432073345234978389 142181747250859514472403)
                ·
                  rfl

theorem cell23_7476245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 8].length) (baseStart_7476245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476245 prefixEnd_7476245 := by exact prefixLift 7476245
  have htrace : WordTrace (prefixWord ++ tailWord_7476245) baseStart_7476245 baseEnd_7476245 := by
    simpa [prefixWord, tailWord_7476245, baseEnd_7476245] using wordTrace_append hprefix tailTrace_7476245
  have hstable : (prefixWord ++ tailWord_7476245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476245).length < 2 ^ (prefixWord ++ tailWord_7476245).sum := by decide
  have hdescent : baseEnd_7476245 < baseStart_7476245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476252 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7476252 : Nat := 118140960795 + 7476252 * 2 ^ 59
def prefixEnd_7476252 : Nat := 4983230072969 + 3 ^ 40 * 7476252 * 2
def baseEnd_7476252 : Nat := 3838910770137788363367349

theorem tailTrace_7476252 : CollatzResearch.WordTrace tailWord_7476252 prefixEnd_7476252 3838910770137788363367349 := by
  unfold tailWord_7476252
  simp only [CollatzResearch.WordTrace]
  refine ⟨136340656055411660516055505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181787541407215547354740673 136340656055411660516055505)
  ·
    refine ⟨102255492041558745387041629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136340656055411660516055505 102255492041558745387041629)
    ·
      refine ⟨38345809515584529520140611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102255492041558745387041629 38345809515584529520140611)
      ·
        refine ⟨57518714273376794280210917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38345809515584529520140611 57518714273376794280210917)
        ·
          refine ⟨10784758926258148927539547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57518714273376794280210917 10784758926258148927539547)
          ·
            refine ⟨16177138389387223391309321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784758926258148927539547 16177138389387223391309321)
            ·
              refine ⟨12132853792040417543481991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16177138389387223391309321 12132853792040417543481991)
              ·
                refine ⟨18199280688060626315222987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12132853792040417543481991 18199280688060626315222987)
                ·
                  refine ⟨27298921032090939472834481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18199280688060626315222987 27298921032090939472834481)
                  ·
                    refine ⟨20474190774068204604625861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27298921032090939472834481 20474190774068204604625861)
                    ·
                      refine ⟨3838910770137788363367349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20474190774068204604625861 3838910770137788363367349)
                      ·
                        rfl

theorem cell23_7476252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7476252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476252 prefixEnd_7476252 := by exact prefixLift 7476252
  have htrace : WordTrace (prefixWord ++ tailWord_7476252) baseStart_7476252 baseEnd_7476252 := by
    simpa [prefixWord, tailWord_7476252, baseEnd_7476252] using wordTrace_append hprefix tailTrace_7476252
  have hstable : (prefixWord ++ tailWord_7476252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476252).length < 2 ^ (prefixWord ++ tailWord_7476252).sum := by decide
  have hdescent : baseEnd_7476252 < baseStart_7476252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476255 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_7476255 : Nat := 118140960795 + 7476255 * 2 ^ 59
def prefixEnd_7476255 : Nat := 4983230072969 + 3 ^ 40 * 7476255 * 2
def baseEnd_7476255 : Nat := 3838912310579751851629835

theorem tailTrace_7476255 : CollatzResearch.WordTrace tailWord_7476255 prefixEnd_7476255 3838912310579751851629835 := by
  unfold tailWord_7476255
  simp only [CollatzResearch.WordTrace]
  refine ⟨272681421529812452544470219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181787614353208301696313479 272681421529812452544470219)
  ·
    refine ⟨409022132294718678816705329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272681421529812452544470219 409022132294718678816705329)
    ·
      refine ⟨306766599221039009112528997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409022132294718678816705329 306766599221039009112528997)
      ·
        refine ⟨57518737353944814208599187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306766599221039009112528997 57518737353944814208599187)
        ·
          refine ⟨86278106030917221312898781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57518737353944814208599187 86278106030917221312898781)
          ·
            refine ⟨32354289761593957992337043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86278106030917221312898781 32354289761593957992337043)
            ·
              refine ⟨48531434642390936988505565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32354289761593957992337043 48531434642390936988505565)
              ·
                refine ⟨18199287990896601370689587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48531434642390936988505565 18199287990896601370689587)
                ·
                  refine ⟨27298931986344902056034381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18199287990896601370689587 27298931986344902056034381)
                  ·
                    refine ⟨10237099494879338271012893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27298931986344902056034381 10237099494879338271012893)
                    ·
                      refine ⟨3838912310579751851629835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237099494879338271012893 3838912310579751851629835)
                      ·
                        rfl

theorem cell23_7476255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_7476255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476255 prefixEnd_7476255 := by exact prefixLift 7476255
  have htrace : WordTrace (prefixWord ++ tailWord_7476255) baseStart_7476255 baseEnd_7476255 := by
    simpa [prefixWord, tailWord_7476255, baseEnd_7476255] using wordTrace_append hprefix tailTrace_7476255
  have hstable : (prefixWord ++ tailWord_7476255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476255).length < 2 ^ (prefixWord ++ tailWord_7476255).sum := by decide
  have hdescent : baseEnd_7476255 < baseStart_7476255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476256 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7476256 : Nat := 118140960795 + 7476256 * 2 ^ 59
def prefixEnd_7476256 : Nat := 4983230072969 + 3 ^ 40 * 7476256 * 2
def baseEnd_7476256 : Nat := 3838912824060406347717331

theorem tailTrace_7476256 : CollatzResearch.WordTrace tailWord_7476256 prefixEnd_7476256 3838912824060406347717331 := by
  unfold tailWord_7476256
  simp only [CollatzResearch.WordTrace]
  refine ⟨136340729001404414857628311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181787638668539219810171081 136340729001404414857628311)
  ·
    refine ⟨204511093502106622286442467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136340729001404414857628311 204511093502106622286442467)
    ·
      refine ⟨306766640253159933429663701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204511093502106622286442467 306766640253159933429663701)
      ·
        refine ⟨7189843130933435939757743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 306766640253159933429663701 7189843130933435939757743)
        ·
          refine ⟨10784764696400153909636615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189843130933435939757743 10784764696400153909636615)
          ·
            refine ⟨16177147044600230864454923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784764696400153909636615 16177147044600230864454923)
            ·
              refine ⟨24265720566900346296682385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16177147044600230864454923 24265720566900346296682385)
              ·
                refine ⟨18199290425175259722511789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24265720566900346296682385 18199290425175259722511789)
                ·
                  refine ⟨6824733909440722395941921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18199290425175259722511789 6824733909440722395941921)
                  ·
                    refine ⟨5118550432080541796956441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6824733909440722395941921 5118550432080541796956441)
                    ·
                      refine ⟨3838912824060406347717331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118550432080541796956441 3838912824060406347717331)
                      ·
                        rfl

theorem cell23_7476256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7476256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476256 prefixEnd_7476256 := by exact prefixLift 7476256
  have htrace : WordTrace (prefixWord ++ tailWord_7476256) baseStart_7476256 baseEnd_7476256 := by
    simpa [prefixWord, tailWord_7476256, baseEnd_7476256] using wordTrace_append hprefix tailTrace_7476256
  have hstable : (prefixWord ++ tailWord_7476256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476256).length < 2 ^ (prefixWord ++ tailWord_7476256).sum := by decide
  have hdescent : baseEnd_7476256 < baseStart_7476256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476268 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_7476268 : Nat := 118140960795 + 7476268 * 2 ^ 59
def prefixEnd_7476268 : Nat := 4983230072969 + 3 ^ 40 * 7476268 * 2
def baseEnd_7476268 : Nat := 3838918985828260300767275

theorem tailTrace_7476268 : CollatzResearch.WordTrace tailWord_7476268 prefixEnd_7476268 3838918985828260300767275 := by
  unfold tailWord_7476268
  simp only [CollatzResearch.WordTrace]
  refine ⟨136340947839382677882346729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181787930452510237176462305 136340947839382677882346729)
  ·
    refine ⟨102255710879537008411760047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136340947839382677882346729 102255710879537008411760047)
    ·
      refine ⟨153383566319305512617640071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102255710879537008411760047 153383566319305512617640071)
      ·
        refine ⟨230075349478958268926460107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153383566319305512617640071 230075349478958268926460107)
        ·
          refine ⟨345113024218437403389690161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230075349478958268926460107 345113024218437403389690161)
          ·
            refine ⟨258834768163828052542267621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345113024218437403389690161 258834768163828052542267621)
            ·
              refine ⟨48531519030717759851675179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258834768163828052542267621 48531519030717759851675179)
              ·
                refine ⟨72797278546076639777512769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48531519030717759851675179 72797278546076639777512769)
                ·
                  refine ⟨54597958909557479833134577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72797278546076639777512769 54597958909557479833134577)
                  ·
                    refine ⟨40948469182168109874850933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54597958909557479833134577 40948469182168109874850933)
                    ·
                      refine ⟨3838918985828260300767275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40948469182168109874850933 3838918985828260300767275)
                      ·
                        rfl

theorem cell23_7476268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_7476268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476268 prefixEnd_7476268 := by exact prefixLift 7476268
  have htrace : WordTrace (prefixWord ++ tailWord_7476268) baseStart_7476268 baseEnd_7476268 := by
    simpa [prefixWord, tailWord_7476268, baseEnd_7476268] using wordTrace_append hprefix tailTrace_7476268
  have hstable : (prefixWord ++ tailWord_7476268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476268).length < 2 ^ (prefixWord ++ tailWord_7476268).sum := by decide
  have hdescent : baseEnd_7476268 < baseStart_7476268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476276 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7476276 : Nat := 118140960795 + 7476276 * 2 ^ 59
def prefixEnd_7476276 : Nat := 4983230072969 + 3 ^ 40 * 7476276 * 2
def baseEnd_7476276 : Nat := 3838923093673496269467239

theorem tailTrace_7476276 : CollatzResearch.WordTrace tailWord_7476276 prefixEnd_7476276 3838923093673496269467239 := by
  unfold tailWord_7476276
  simp only [CollatzResearch.WordTrace]
  refine ⟨136341093731368186565492341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181788124975157582087323121 136341093731368186565492341)
  ·
    refine ⟨12781977537315767490514907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136341093731368186565492341 12781977537315767490514907)
    ·
      refine ⟨19172966305973651235772361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12781977537315767490514907 19172966305973651235772361)
      ·
        refine ⟨14379724729480238426829271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19172966305973651235772361 14379724729480238426829271)
        ·
          refine ⟨21569587094220357640243907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379724729480238426829271 21569587094220357640243907)
          ·
            refine ⟨32354380641330536460365861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21569587094220357640243907 32354380641330536460365861)
            ·
              refine ⟨6066446370249475586318599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32354380641330536460365861 6066446370249475586318599)
              ·
                refine ⟨9099669555374213379477899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066446370249475586318599 9099669555374213379477899)
                ·
                  refine ⟨13649504333061320069216849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099669555374213379477899 13649504333061320069216849)
                  ·
                    refine ⟨10237128249795990051912637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13649504333061320069216849 10237128249795990051912637)
                    ·
                      refine ⟨3838923093673496269467239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237128249795990051912637 3838923093673496269467239)
                      ·
                        rfl

theorem cell23_7476276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7476276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476276 prefixEnd_7476276 := by exact prefixLift 7476276
  have htrace : WordTrace (prefixWord ++ tailWord_7476276) baseStart_7476276 baseEnd_7476276 := by
    simpa [prefixWord, tailWord_7476276, baseEnd_7476276] using wordTrace_append hprefix tailTrace_7476276
  have hstable : (prefixWord ++ tailWord_7476276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476276).length < 2 ^ (prefixWord ++ tailWord_7476276).sum := by decide
  have hdescent : baseEnd_7476276 < baseStart_7476276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476288 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_7476288 : Nat := 118140960795 + 7476288 * 2 ^ 59
def prefixEnd_7476288 : Nat := 4983230072969 + 3 ^ 40 * 7476288 * 2
def baseEnd_7476288 : Nat := 1279643085147116740839061

theorem tailTrace_7476288 : CollatzResearch.WordTrace tailWord_7476288 prefixEnd_7476288 1279643085147116740839061 := by
  unfold tailWord_7476288
  simp only [CollatzResearch.WordTrace]
  refine ⟨136341312569346449590210759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181788416759128599453614345 136341312569346449590210759)
  ·
    refine ⟨204511968854019674385316139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136341312569346449590210759 204511968854019674385316139)
    ·
      refine ⟨306767953281029511577974209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204511968854019674385316139 306767953281029511577974209)
      ·
        refine ⟨230075964960772133683480657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306767953281029511577974209 230075964960772133683480657)
        ·
          refine ⟨172556973720579100262610493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230075964960772133683480657 172556973720579100262610493)
          ·
            refine ⟨64708865145217162598478935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172556973720579100262610493 64708865145217162598478935)
            ·
              refine ⟨97063297717825743897718403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64708865145217162598478935 97063297717825743897718403)
              ·
                refine ⟨145594946576738615846577605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97063297717825743897718403 145594946576738615846577605)
                ·
                  refine ⟨27299052483138490471233301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145594946576738615846577605 27299052483138490471233301)
                  ·
                    refine ⟨1279643085147116740839061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27299052483138490471233301 1279643085147116740839061)
                    ·
                      rfl

theorem cell23_7476288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_7476288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476288 prefixEnd_7476288 := by exact prefixLift 7476288
  have htrace : WordTrace (prefixWord ++ tailWord_7476288) baseStart_7476288 baseEnd_7476288 := by
    simpa [prefixWord, tailWord_7476288, baseEnd_7476288] using wordTrace_append hprefix tailTrace_7476288
  have hstable : (prefixWord ++ tailWord_7476288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476288).length < 2 ^ (prefixWord ++ tailWord_7476288).sum := by decide
  have hdescent : baseEnd_7476288 < baseStart_7476288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476289 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7476289 : Nat := 118140960795 + 7476289 * 2 ^ 59
def prefixEnd_7476289 : Nat := 4983230072969 + 3 ^ 40 * 7476289 * 2
def baseEnd_7476289 : Nat := 3838929768922004718604679

theorem tailTrace_7476289 : CollatzResearch.WordTrace tailWord_7476289 prefixEnd_7476289 3838929768922004718604679 := by
  unfold tailWord_7476289
  simp only [CollatzResearch.WordTrace]
  refine ⟨272682661611689276351207921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181788441074459517567471947 272682661611689276351207921)
  ·
    refine ⟨204511996208766957263405941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272682661611689276351207921 204511996208766957263405941)
    ·
      refine ⟨19172999644571902243444307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204511996208766957263405941 19172999644571902243444307)
      ·
        refine ⟨28759499466857853365166461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19172999644571902243444307 28759499466857853365166461)
        ·
          refine ⟨10784812300071695011937423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28759499466857853365166461 10784812300071695011937423)
          ·
            refine ⟨16177218450107542517906135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784812300071695011937423 16177218450107542517906135)
            ·
              refine ⟨24265827675161313776859203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16177218450107542517906135 24265827675161313776859203)
              ·
                refine ⟨36398741512741970665288805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24265827675161313776859203 36398741512741970665288805)
                ·
                  refine ⟨6824764033639119499741651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36398741512741970665288805 6824764033639119499741651)
                  ·
                    refine ⟨10237146050458679249612477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6824764033639119499741651 10237146050458679249612477)
                    ·
                      refine ⟨3838929768922004718604679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237146050458679249612477 3838929768922004718604679)
                      ·
                        rfl

theorem cell23_7476289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7476289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476289 prefixEnd_7476289 := by exact prefixLift 7476289
  have htrace : WordTrace (prefixWord ++ tailWord_7476289) baseStart_7476289 baseEnd_7476289 := by
    simpa [prefixWord, tailWord_7476289, baseEnd_7476289] using wordTrace_append hprefix tailTrace_7476289
  have hstable : (prefixWord ++ tailWord_7476289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476289).length < 2 ^ (prefixWord ++ tailWord_7476289).sum := by decide
  have hdescent : baseEnd_7476289 < baseStart_7476289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476306 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 2, 1, 3]
def baseStart_7476306 : Nat := 118140960795 + 7476306 * 2 ^ 59
def prefixEnd_7476306 : Nat := 4983230072969 + 3 ^ 40 * 7476306 * 2
def baseEnd_7476306 : Nat := 3838938498093131152092101

theorem tailTrace_7476306 : CollatzResearch.WordTrace tailWord_7476306 prefixEnd_7476306 3838938498093131152092101 := by
  unfold tailWord_7476306
  simp only [CollatzResearch.WordTrace]
  refine ⟨68170820413156922063644193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181788854435085125503051181 68170820413156922063644193)
  ·
    refine ⟨51128115309867691547733145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68170820413156922063644193 51128115309867691547733145)
    ·
      refine ⟨38346086482400768660799859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51128115309867691547733145 38346086482400768660799859)
      ·
        refine ⟨57519129723601152991199789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38346086482400768660799859 57519129723601152991199789)
        ·
          refine ⟨21569673646350432371699921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57519129723601152991199789 21569673646350432371699921)
          ·
            refine ⟨16177255234762824278774941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21569673646350432371699921 16177255234762824278774941)
            ·
              refine ⟨6066470713036059104540603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16177255234762824278774941 6066470713036059104540603)
              ·
                refine ⟨9099706069554088656810905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066470713036059104540603 9099706069554088656810905)
                ·
                  refine ⟨6824779552165566492608179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9099706069554088656810905 6824779552165566492608179)
                  ·
                    refine ⟨10237169328248349738912269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6824779552165566492608179 10237169328248349738912269)
                    ·
                      refine ⟨3838938498093131152092101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237169328248349738912269 3838938498093131152092101)
                      ·
                        rfl

theorem cell23_7476306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_7476306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476306 prefixEnd_7476306 := by exact prefixLift 7476306
  have htrace : WordTrace (prefixWord ++ tailWord_7476306) baseStart_7476306 baseEnd_7476306 := by
    simpa [prefixWord, tailWord_7476306, baseEnd_7476306] using wordTrace_append hprefix tailTrace_7476306
  have hstable : (prefixWord ++ tailWord_7476306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476306).length < 2 ^ (prefixWord ++ tailWord_7476306).sum := by decide
  have hdescent : baseEnd_7476306 < baseStart_7476306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476402 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_7476402 : Nat := 118140960795 + 7476402 * 2 ^ 59
def prefixEnd_7476402 : Nat := 4983230072969 + 3 ^ 40 * 7476402 * 2
def baseEnd_7476402 : Nat := 3838987792235962776491659

theorem tailTrace_7476402 : CollatzResearch.WordTrace tailWord_7476402 prefixEnd_7476402 3838987792235962776491659 := by
  unfold tailWord_7476402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68171695765069974162517865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181791188706853264433380973 68171695765069974162517865)
  ·
    refine ⟨51128771823802480621888399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68171695765069974162517865 51128771823802480621888399)
    ·
      refine ⟨76693157735703720932832599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51128771823802480621888399 76693157735703720932832599)
      ·
        refine ⟨115039736603555581399248899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76693157735703720932832599 115039736603555581399248899)
        ·
          refine ⟨172559604905333372098873349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115039736603555581399248899 172559604905333372098873349)
          ·
            refine ⟨32354925919750007268538753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172559604905333372098873349 32354925919750007268538753)
            ·
              refine ⟨24266194439812505451404065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32354925919750007268538753 24266194439812505451404065)
              ·
                refine ⟨18199645829859379088553049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24266194439812505451404065 18199645829859379088553049)
                ·
                  refine ⟨13649734372394534316414787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18199645829859379088553049 13649734372394534316414787)
                  ·
                    refine ⟨20474601558591801474622181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13649734372394534316414787 20474601558591801474622181)
                    ·
                      refine ⟨3838987792235962776491659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20474601558591801474622181 3838987792235962776491659)
                      ·
                        rfl

theorem cell23_7476402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_7476402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476402 prefixEnd_7476402 := by exact prefixLift 7476402
  have htrace : WordTrace (prefixWord ++ tailWord_7476402) baseStart_7476402 baseEnd_7476402 := by
    simpa [prefixWord, tailWord_7476402, baseEnd_7476402] using wordTrace_append hprefix tailTrace_7476402
  have hstable : (prefixWord ++ tailWord_7476402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476402).length < 2 ^ (prefixWord ++ tailWord_7476402).sum := by decide
  have hdescent : baseEnd_7476402 < baseStart_7476402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476435 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3]
def baseStart_7476435 : Nat := 118140960795 + 7476435 * 2 ^ 59
def prefixEnd_7476435 : Nat := 4983230072969 + 3 ^ 40 * 7476435 * 2
def baseEnd_7476435 : Nat := 3839004737097561147379007

theorem tailTrace_7476435 : CollatzResearch.WordTrace tailWord_7476435 prefixEnd_7476435 3839004737097561147379007 := by
  unfold tailWord_7476435
  simp only [CollatzResearch.WordTrace]
  refine ⟨272687986669160343286022759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181791991112773562190681839 272687986669160343286022759)
  ·
    refine ⟨409031980003740514929034139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272687986669160343286022759 409031980003740514929034139)
    ·
      refine ⟨613547970005610772393551209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409031980003740514929034139 613547970005610772393551209)
      ·
        refine ⟨460160977504208079295163407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613547970005610772393551209 460160977504208079295163407)
        ·
          refine ⟨690241466256312118942745111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460160977504208079295163407 690241466256312118942745111)
          ·
            refine ⟨1035362199384468178414117667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690241466256312118942745111 1035362199384468178414117667)
            ·
              refine ⟨1553043299076702267621176501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035362199384468178414117667 1553043299076702267621176501)
              ·
                refine ⟨145597809288440837589485297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553043299076702267621176501 145597809288440837589485297)
                ·
                  refine ⟨109198356966330628192113973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145597809288440837589485297 109198356966330628192113973)
                  ·
                    refine ⟨10237345965593496393010685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109198356966330628192113973 10237345965593496393010685)
                    ·
                      refine ⟨3839004737097561147379007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237345965593496393010685 3839004737097561147379007)
                      ·
                        rfl

theorem cell23_7476435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_7476435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476435 prefixEnd_7476435 := by exact prefixLift 7476435
  have htrace : WordTrace (prefixWord ++ tailWord_7476435) baseStart_7476435 baseEnd_7476435 := by
    simpa [prefixWord, tailWord_7476435, baseEnd_7476435] using wordTrace_append hprefix tailTrace_7476435
  have hstable : (prefixWord ++ tailWord_7476435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476435).length < 2 ^ (prefixWord ++ tailWord_7476435).sum := by decide
  have hdescent : baseEnd_7476435 < baseStart_7476435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476515 : List Nat := [1, 1, 1, 4, 2, 3, 11]
def baseStart_7476515 : Nat := 118140960795 + 7476515 * 2 ^ 59
def prefixEnd_7476515 : Nat := 4983230072969 + 3 ^ 40 * 7476515 * 2
def baseEnd_7476515 : Nat := 47395627352468158449119

theorem tailTrace_7476515 : CollatzResearch.WordTrace tailWord_7476515 prefixEnd_7476515 47395627352468158449119 := by
  unfold tailWord_7476515
  simp only [CollatzResearch.WordTrace]
  refine ⟨272690904508870516948934999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181793936339247011299289999 272690904508870516948934999)
  ·
    refine ⟨409036356763305775423402499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272690904508870516948934999 409036356763305775423402499)
    ·
      refine ⟨613554535144958663135103749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409036356763305775423402499 613554535144958663135103749)
      ·
        refine ⟨115041475339679749337831953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 613554535144958663135103749 115041475339679749337831953)
        ·
          refine ⟨86281106504759812003373965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115041475339679749337831953 86281106504759812003373965)
          ·
            refine ⟨32355414939284929501265237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86281106504759812003373965 32355414939284929501265237)
            ·
              refine ⟨47395627352468158449119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32355414939284929501265237 47395627352468158449119)
              ·
                rfl

theorem cell23_7476515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 11].length) (baseStart_7476515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476515 prefixEnd_7476515 := by exact prefixLift 7476515
  have htrace : WordTrace (prefixWord ++ tailWord_7476515) baseStart_7476515 baseEnd_7476515 := by
    simpa [prefixWord, tailWord_7476515, baseEnd_7476515] using wordTrace_append hprefix tailTrace_7476515
  have hstable : (prefixWord ++ tailWord_7476515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476515).length < 2 ^ (prefixWord ++ tailWord_7476515).sum := by decide
  have hdescent : baseEnd_7476515 < baseStart_7476515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476520 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7476520 : Nat := 118140960795 + 7476520 * 2 ^ 59
def prefixEnd_7476520 : Nat := 4983230072969 + 3 ^ 40 * 7476520 * 2
def baseEnd_7476520 : Nat := 3839048382953193314816117

theorem tailTrace_7476520 : CollatzResearch.WordTrace tailWord_7476520 prefixEnd_7476520 3839048382953193314816117 := by
  unfold tailWord_7476520
  simp only [CollatzResearch.WordTrace]
  refine ⟨136345543436926201401433507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181794057915901601868578009 136345543436926201401433507)
  ·
    refine ⟨204518315155389302102150261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136345543436926201401433507 204518315155389302102150261)
    ·
      refine ⟨19173592045817747072076587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204518315155389302102150261 19173592045817747072076587)
      ·
        refine ⟨28760388068726620608114881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19173592045817747072076587 28760388068726620608114881)
        ·
          refine ⟨21570291051544965456086161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28760388068726620608114881 21570291051544965456086161)
          ·
            refine ⟨16177718288658724092064621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21570291051544965456086161 16177718288658724092064621)
            ·
              refine ⟨6066644358247021534524233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16177718288658724092064621 6066644358247021534524233)
              ·
                refine ⟨4549983268685266150893175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066644358247021534524233 4549983268685266150893175)
                ·
                  refine ⟨6824974903027899226339763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549983268685266150893175 6824974903027899226339763)
                  ·
                    refine ⟨10237462354541848839509645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6824974903027899226339763 10237462354541848839509645)
                    ·
                      refine ⟨3839048382953193314816117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237462354541848839509645 3839048382953193314816117)
                      ·
                        rfl

theorem cell23_7476520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7476520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476520 prefixEnd_7476520 := by exact prefixLift 7476520
  have htrace : WordTrace (prefixWord ++ tailWord_7476520) baseStart_7476520 baseEnd_7476520 := by
    simpa [prefixWord, tailWord_7476520, baseEnd_7476520] using wordTrace_append hprefix tailTrace_7476520
  have hstable : (prefixWord ++ tailWord_7476520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476520).length < 2 ^ (prefixWord ++ tailWord_7476520).sum := by decide
  have hdescent : baseEnd_7476520 < baseStart_7476520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476555 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_7476555 : Nat := 118140960795 + 7476555 * 2 ^ 59
def prefixEnd_7476555 : Nat := 4983230072969 + 3 ^ 40 * 7476555 * 2
def baseEnd_7476555 : Nat := 3839066354776100677878455

theorem tailTrace_7476555 : CollatzResearch.WordTrace tailWord_7476555 prefixEnd_7476555 3839066354776100677878455 := by
  unfold tailWord_7476555
  simp only [CollatzResearch.WordTrace]
  refine ⟨272692363428725603780391119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181794908952483735853594079 272692363428725603780391119)
  ·
    refine ⟨409038545143088405670586679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272692363428725603780391119 409038545143088405670586679)
    ·
      refine ⟨613557817714632608505880019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409038545143088405670586679 613557817714632608505880019)
      ·
        refine ⟨920336726571948912758820029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613557817714632608505880019 920336726571948912758820029)
        ·
          refine ⟨345126272464480842284557511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920336726571948912758820029 345126272464480842284557511)
          ·
            refine ⟨517689408696721263426836267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345126272464480842284557511 517689408696721263426836267)
            ·
              refine ⟨776534113045081895140254401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517689408696721263426836267 776534113045081895140254401)
              ·
                refine ⟨582400584783811421355190801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776534113045081895140254401 582400584783811421355190801)
                ·
                  refine ⟨436800438587858566016393101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582400584783811421355190801 436800438587858566016393101)
                  ·
                    refine ⟨163800164470446962256147413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436800438587858566016393101 163800164470446962256147413)
                    ·
                      refine ⟨3839066354776100677878455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163800164470446962256147413 3839066354776100677878455)
                      ·
                        rfl

theorem cell23_7476555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_7476555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476555 prefixEnd_7476555 := by exact prefixLift 7476555
  have htrace : WordTrace (prefixWord ++ tailWord_7476555) baseStart_7476555 baseEnd_7476555 := by
    simpa [prefixWord, tailWord_7476555, baseEnd_7476555] using wordTrace_append hprefix tailTrace_7476555
  have hstable : (prefixWord ++ tailWord_7476555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476555).length < 2 ^ (prefixWord ++ tailWord_7476555).sum := by decide
  have hdescent : baseEnd_7476555 < baseStart_7476555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476566 : List Nat := [5, 2, 3, 1, 12]
def baseStart_7476566 : Nat := 118140960795 + 7476566 * 2 ^ 59
def prefixEnd_7476566 : Nat := 4983230072969 + 3 ^ 40 * 7476566 * 2
def baseEnd_7476566 : Nat := 5266216739455830088945

theorem tailTrace_7476566 : CollatzResearch.WordTrace tailWord_7476566 prefixEnd_7476566 5266216739455830088945 := by
  unfold tailWord_7476566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043297789480359541190097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181795176421123835106027701 17043297789480359541190097)
  ·
    refine ⟨12782473342110269655892573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17043297789480359541190097 12782473342110269655892573)
    ·
      refine ⟨4793427503291351120959715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12782473342110269655892573 4793427503291351120959715)
      ·
        refine ⟨7190141254937026681439573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793427503291351120959715 7190141254937026681439573)
        ·
          refine ⟨5266216739455830088945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7190141254937026681439573 5266216739455830088945)
          ·
            rfl

theorem cell23_7476566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 12].length) (baseStart_7476566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476566 prefixEnd_7476566 := by exact prefixLift 7476566
  have htrace : WordTrace (prefixWord ++ tailWord_7476566) baseStart_7476566 baseEnd_7476566 := by
    simpa [prefixWord, tailWord_7476566, baseEnd_7476566] using wordTrace_append hprefix tailTrace_7476566
  have hstable : (prefixWord ++ tailWord_7476566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476566).length < 2 ^ (prefixWord ++ tailWord_7476566).sum := by decide
  have hdescent : baseEnd_7476566 < baseStart_7476566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476576 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3]
def baseStart_7476576 : Nat := 118140960795 + 7476576 * 2 ^ 59
def prefixEnd_7476576 : Nat := 4983230072969 + 3 ^ 40 * 7476576 * 2
def baseEnd_7476576 : Nat := 3839077137869845095715859

theorem tailTrace_7476576 : CollatzResearch.WordTrace tailWord_7476576 prefixEnd_7476576 3839077137869845095715859 := by
  unfold tailWord_7476576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136346564680824762183452791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181795419574433016244603721 136346564680824762183452791)
  ·
    refine ⟨204519847021237143275179187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136346564680824762183452791 204519847021237143275179187)
    ·
      refine ⟨306779770531855714912768781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204519847021237143275179187 306779770531855714912768781)
      ·
        refine ⟨115042413949445893092288293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306779770531855714912768781 115042413949445893092288293)
        ·
          refine ⟨21570452615521104954804055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115042413949445893092288293 21570452615521104954804055)
          ·
            refine ⟨32355678923281657432206083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21570452615521104954804055 32355678923281657432206083)
            ·
              refine ⟨48533518384922486148309125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32355678923281657432206083 48533518384922486148309125)
              ·
                refine ⟨9100034697172966152807961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48533518384922486148309125 9100034697172966152807961)
                ·
                  refine ⟨6825026022879724614605971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9100034697172966152807961 6825026022879724614605971)
                  ·
                    refine ⟨10237539034319586921908957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6825026022879724614605971 10237539034319586921908957)
                    ·
                      refine ⟨3839077137869845095715859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237539034319586921908957 3839077137869845095715859)
                      ·
                        rfl

theorem cell23_7476576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_7476576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476576 prefixEnd_7476576 := by exact prefixLift 7476576
  have htrace : WordTrace (prefixWord ++ tailWord_7476576) baseStart_7476576 baseEnd_7476576 := by
    simpa [prefixWord, tailWord_7476576, baseEnd_7476576] using wordTrace_append hprefix tailTrace_7476576
  have hstable : (prefixWord ++ tailWord_7476576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476576).length < 2 ^ (prefixWord ++ tailWord_7476576).sum := by decide
  have hdescent : baseEnd_7476576 < baseStart_7476576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476592 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_7476592 : Nat := 118140960795 + 7476592 * 2 ^ 59
def prefixEnd_7476592 : Nat := 4983230072969 + 3 ^ 40 * 7476592 * 2
def baseEnd_7476592 : Nat := 1279695117853439011038595

theorem tailTrace_7476592 : CollatzResearch.WordTrace tailWord_7476592 prefixEnd_7476592 1279695117853439011038595 := by
  unfold tailWord_7476592
  simp only [CollatzResearch.WordTrace]
  refine ⟨136346856464795779549744015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181795808619727706066325353 136346856464795779549744015)
  ·
    refine ⟨204520284697193669324616023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136346856464795779549744015 204520284697193669324616023)
    ·
      refine ⟨306780427045790503986924035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204520284697193669324616023 306780427045790503986924035)
      ·
        refine ⟨460170640568685755980386053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306780427045790503986924035 460170640568685755980386053)
        ·
          refine ⟨86281995106628579246322385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460170640568685755980386053 86281995106628579246322385)
          ·
            refine ⟨64711496329971434434741789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86281995106628579246322385 64711496329971434434741789)
            ·
              refine ⟨24266811123739287913028171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64711496329971434434741789 24266811123739287913028171)
              ·
                refine ⟨36400216685608931869542257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24266811123739287913028171 36400216685608931869542257)
                ·
                  refine ⟨27300162514206698902156693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36400216685608931869542257 27300162514206698902156693)
                  ·
                    refine ⟨1279695117853439011038595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27300162514206698902156693 1279695117853439011038595)
                    ·
                      rfl

theorem cell23_7476592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_7476592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476592 prefixEnd_7476592 := by exact prefixLift 7476592
  have htrace : WordTrace (prefixWord ++ tailWord_7476592) baseStart_7476592 baseEnd_7476592 := by
    simpa [prefixWord, tailWord_7476592, baseEnd_7476592] using wordTrace_append hprefix tailTrace_7476592
  have hstable : (prefixWord ++ tailWord_7476592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476592).length < 2 ^ (prefixWord ++ tailWord_7476592).sum := by decide
  have hdescent : baseEnd_7476592 < baseStart_7476592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476616 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7476616 : Nat := 118140960795 + 7476616 * 2 ^ 59
def prefixEnd_7476616 : Nat := 4983230072969 + 3 ^ 40 * 7476616 * 2
def baseEnd_7476616 : Nat := 3839097677096024939215675

theorem tailTrace_7476616 : CollatzResearch.WordTrace tailWord_7476616 prefixEnd_7476616 3839097677096024939215675 := by
  unfold tailWord_7476616
  simp only [CollatzResearch.WordTrace]
  refine ⟨136347294140752305599180851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181796392187669740798907801 136347294140752305599180851)
  ·
    refine ⟨204520941211128458398771277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136347294140752305599180851 204520941211128458398771277)
    ·
      refine ⟨76695352954173171899539229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204520941211128458398771277 76695352954173171899539229)
      ·
        refine ⟨28760757357814939462327211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76695352954173171899539229 28760757357814939462327211)
        ·
          refine ⟨43141136036722409193490817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28760757357814939462327211 43141136036722409193490817)
          ·
            refine ⟨32355852027541806895118113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43141136036722409193490817 32355852027541806895118113)
            ·
              refine ⟨24266889020656355171338585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32355852027541806895118113 24266889020656355171338585)
              ·
                refine ⟨18200166765492266378503939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24266889020656355171338585 18200166765492266378503939)
                ·
                  refine ⟨27300250148238399567755909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18200166765492266378503939 27300250148238399567755909)
                  ·
                    refine ⟨5118796902794699918954233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27300250148238399567755909 5118796902794699918954233)
                    ·
                      refine ⟨3839097677096024939215675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118796902794699918954233 3839097677096024939215675)
                      ·
                        rfl

theorem cell23_7476616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7476616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476616 prefixEnd_7476616 := by exact prefixLift 7476616
  have htrace : WordTrace (prefixWord ++ tailWord_7476616) baseStart_7476616 baseEnd_7476616 := by
    simpa [prefixWord, tailWord_7476616, baseEnd_7476616] using wordTrace_append hprefix tailTrace_7476616
  have hstable : (prefixWord ++ tailWord_7476616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476616).length < 2 ^ (prefixWord ++ tailWord_7476616).sum := by decide
  have hdescent : baseEnd_7476616 < baseStart_7476616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476633 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 2, 2, 2]
def baseStart_7476633 : Nat := 118140960795 + 7476633 * 2 ^ 59
def prefixEnd_7476633 : Nat := 4983230072969 + 3 ^ 40 * 7476633 * 2
def baseEnd_7476633 : Nat := 3839106406267151372703097

theorem tailTrace_7476633 : CollatzResearch.WordTrace tailWord_7476633 prefixEnd_7476633 3839106406267151372703097 := by
  unfold tailWord_7476633
  simp only [CollatzResearch.WordTrace]
  refine ⟨272695208322443023101730553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181796805548295348734487035 272695208322443023101730553)
  ·
    refine ⟨204521406241832267326297915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272695208322443023101730553 204521406241832267326297915)
    ·
      refine ⟨306782109362748400989446873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204521406241832267326297915 306782109362748400989446873)
      ·
        refine ⟨230086582022061300742085155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306782109362748400989446873 230086582022061300742085155)
        ·
          refine ⟨345129873033091951113127733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230086582022061300742085155 345129873033091951113127733)
          ·
            refine ⟨32355925596852370416855725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345129873033091951113127733 32355925596852370416855725)
            ·
              refine ⟨12133472098819638906320897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32355925596852370416855725 12133472098819638906320897)
              ·
                refine ⟨9100104074114729179740673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133472098819638906320897 9100104074114729179740673)
                ·
                  refine ⟨6825078055586046884805505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9100104074114729179740673 6825078055586046884805505)
                  ·
                    refine ⟨5118808541689535163604129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6825078055586046884805505 5118808541689535163604129)
                    ·
                      refine ⟨3839106406267151372703097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118808541689535163604129 3839106406267151372703097)
                      ·
                        rfl

theorem cell23_7476633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_7476633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476633 prefixEnd_7476633 := by exact prefixLift 7476633
  have htrace : WordTrace (prefixWord ++ tailWord_7476633) baseStart_7476633 baseEnd_7476633 := by
    simpa [prefixWord, tailWord_7476633, baseEnd_7476633] using wordTrace_append hprefix tailTrace_7476633
  have hstable : (prefixWord ++ tailWord_7476633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476633).length < 2 ^ (prefixWord ++ tailWord_7476633).sum := by decide
  have hdescent : baseEnd_7476633 < baseStart_7476633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476639 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 7]
def baseStart_7476639 : Nat := 118140960795 + 7476639 * 2 ^ 59
def prefixEnd_7476639 : Nat := 4983230072969 + 3 ^ 40 * 7476639 * 2
def baseEnd_7476639 : Nat := 426567720794564261025341

theorem tailTrace_7476639 : CollatzResearch.WordTrace tailWord_7476639 prefixEnd_7476639 426567720794564261025341 := by
  unfold tailWord_7476639
  simp only [CollatzResearch.WordTrace]
  refine ⟨272695427160421286126448971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181796951440280857417632647 272695427160421286126448971)
  ·
    refine ⟨409043140740631929189673457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272695427160421286126448971 409043140740631929189673457)
    ·
      refine ⟨306782355555473946892255093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409043140740631929189673457 306782355555473946892255093)
      ·
        refine ⟨28760845833325682521148915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306782355555473946892255093 28760845833325682521148915)
        ·
          refine ⟨43141268749988523781723373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28760845833325682521148915 43141268749988523781723373)
          ·
            refine ⟨16177975781245696418146265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43141268749988523781723373 16177975781245696418146265)
            ·
              refine ⟨12133481835934272313609699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16177975781245696418146265 12133481835934272313609699)
              ·
                refine ⟨18200222753901408470414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12133481835934272313609699 18200222753901408470414549)
                ·
                  refine ⟨426567720794564261025341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18200222753901408470414549 426567720794564261025341)
                  ·
                    rfl

theorem cell23_7476639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 7].length) (baseStart_7476639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476639 prefixEnd_7476639 := by exact prefixLift 7476639
  have htrace : WordTrace (prefixWord ++ tailWord_7476639) baseStart_7476639 baseEnd_7476639 := by
    simpa [prefixWord, tailWord_7476639, baseEnd_7476639] using wordTrace_append hprefix tailTrace_7476639
  have hstable : (prefixWord ++ tailWord_7476639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476639).length < 2 ^ (prefixWord ++ tailWord_7476639).sum := by decide
  have hdescent : baseEnd_7476639 < baseStart_7476639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476652 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_7476652 : Nat := 118140960795 + 7476652 * 2 ^ 59
def prefixEnd_7476652 : Nat := 4983230072969 + 3 ^ 40 * 7476652 * 2
def baseEnd_7476652 : Nat := 1279705387466528932788503

theorem tailTrace_7476652 : CollatzResearch.WordTrace tailWord_7476652 prefixEnd_7476652 1279705387466528932788503 := by
  unfold tailWord_7476652
  simp only [CollatzResearch.WordTrace]
  refine ⟨136347950654687094673336105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181797267539582792897781473 136347950654687094673336105)
  ·
    refine ⟨102260962991015321005002079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136347950654687094673336105 102260962991015321005002079)
    ·
      refine ⟨153391444486522981507503119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102260962991015321005002079 153391444486522981507503119)
      ·
        refine ⟨230087166729784472261254679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153391444486522981507503119 230087166729784472261254679)
        ·
          refine ⟨345130750094676708391882019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230087166729784472261254679 345130750094676708391882019)
          ·
            refine ⟨517696125142015062587823029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345130750094676708391882019 517696125142015062587823029)
            ·
              refine ⟨48534011732063912117608409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 517696125142015062587823029 48534011732063912117608409)
              ·
                refine ⟨36400508799047934088206307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48534011732063912117608409 36400508799047934088206307)
                ·
                  refine ⟨54600763198571901132309461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36400508799047934088206307 54600763198571901132309461)
                  ·
                    refine ⟨1279705387466528932788503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54600763198571901132309461 1279705387466528932788503)
                    ·
                      rfl

theorem cell23_7476652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_7476652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476652 prefixEnd_7476652 := by exact prefixLift 7476652
  have htrace : WordTrace (prefixWord ++ tailWord_7476652) baseStart_7476652 baseEnd_7476652 := by
    simpa [prefixWord, tailWord_7476652, baseEnd_7476652] using wordTrace_append hprefix tailTrace_7476652
  have hstable : (prefixWord ++ tailWord_7476652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476652).length < 2 ^ (prefixWord ++ tailWord_7476652).sum := by decide
  have hdescent : baseEnd_7476652 < baseStart_7476652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476659 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 5, 2]
def baseStart_7476659 : Nat := 118140960795 + 7476659 * 2 ^ 59
def prefixEnd_7476659 : Nat := 4983230072969 + 3 ^ 40 * 7476659 * 2
def baseEnd_7476659 : Nat := 3839119756764168270977977

theorem tailTrace_7476659 : CollatzResearch.WordTrace tailWord_7476659 prefixEnd_7476659 3839119756764168270977977 := by
  unfold tailWord_7476659
  simp only [CollatzResearch.WordTrace]
  refine ⟨272696156620348829542177031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181797437746899219694784687 272696156620348829542177031)
  ·
    refine ⟨409044234930523244313265547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272696156620348829542177031 409044234930523244313265547)
    ·
      refine ⟨613566352395784866469898321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409044234930523244313265547 613566352395784866469898321)
      ·
        refine ⟨460174764296838649852423741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613566352395784866469898321 460174764296838649852423741)
        ·
          refine ⟨172565536611314493694658903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460174764296838649852423741 172565536611314493694658903)
          ·
            refine ⟨258848304916971740541988355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172565536611314493694658903 258848304916971740541988355)
            ·
              refine ⟨388272457375457610812982533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258848304916971740541988355 388272457375457610812982533)
              ·
                refine ⟨72801085757898302027434225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388272457375457610812982533 72801085757898302027434225)
                ·
                  refine ⟨54600814318423726520575669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72801085757898302027434225 54600814318423726520575669)
                  ·
                    refine ⟨5118826342352224361303969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54600814318423726520575669 5118826342352224361303969)
                    ·
                      refine ⟨3839119756764168270977977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5118826342352224361303969 3839119756764168270977977)
                      ·
                        rfl

theorem cell23_7476659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5, 2].length) (baseStart_7476659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476659 prefixEnd_7476659 := by exact prefixLift 7476659
  have htrace : WordTrace (prefixWord ++ tailWord_7476659) baseStart_7476659 baseEnd_7476659 := by
    simpa [prefixWord, tailWord_7476659, baseEnd_7476659] using wordTrace_append hprefix tailTrace_7476659
  have hstable : (prefixWord ++ tailWord_7476659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476659).length < 2 ^ (prefixWord ++ tailWord_7476659).sum := by decide
  have hdescent : baseEnd_7476659 < baseStart_7476659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476669 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_7476669 : Nat := 118140960795 + 7476669 * 2 ^ 59
def prefixEnd_7476669 : Nat := 4983230072969 + 3 ^ 40 * 7476669 * 2
def baseEnd_7476669 : Nat := 1279708297190237743950977

theorem tailTrace_7476669 : CollatzResearch.WordTrace tailWord_7476669 prefixEnd_7476669 1279708297190237743950977 := by
  unfold tailWord_7476669
  simp only [CollatzResearch.WordTrace]
  refine ⟨272696521350312601250041061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181797680900208400833360707 272696521350312601250041061)
  ·
    refine ⟨51130597753183612734382699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272696521350312601250041061 51130597753183612734382699)
    ·
      refine ⟨76695896629775419101574049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51130597753183612734382699 76695896629775419101574049)
      ·
        refine ⟨57521922472331564326180537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76695896629775419101574049 57521922472331564326180537)
        ·
          refine ⟨43141441854248673244635403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57521922472331564326180537 43141441854248673244635403)
          ·
            refine ⟨64712162781373009866953105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43141441854248673244635403 64712162781373009866953105)
            ·
              refine ⟨48534122086029757400214829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64712162781373009866953105 48534122086029757400214829)
              ·
                refine ⟨18200295782261159025080561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48534122086029757400214829 18200295782261159025080561)
                ·
                  refine ⟨13650221836695869268810421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18200295782261159025080561 13650221836695869268810421)
                  ·
                    refine ⟨1279708297190237743950977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13650221836695869268810421 1279708297190237743950977)
                    ·
                      rfl

theorem cell23_7476669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_7476669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476669 prefixEnd_7476669 := by exact prefixLift 7476669
  have htrace : WordTrace (prefixWord ++ tailWord_7476669) baseStart_7476669 baseEnd_7476669 := by
    simpa [prefixWord, tailWord_7476669, baseEnd_7476669] using wordTrace_append hprefix tailTrace_7476669
  have hstable : (prefixWord ++ tailWord_7476669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476669).length < 2 ^ (prefixWord ++ tailWord_7476669).sum := by decide
  have hdescent : baseEnd_7476669 < baseStart_7476669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476746 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_7476746 : Nat := 118140960795 + 7476746 * 2 ^ 59
def prefixEnd_7476746 : Nat := 4983230072969 + 3 ^ 40 * 7476746 * 2
def baseEnd_7476746 : Nat := 426573825509012158954453

theorem tailTrace_7476746 : CollatzResearch.WordTrace tailWord_7476746 prefixEnd_7476746 426573825509012158954453 := by
  unfold tailWord_7476746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174832442758410850148523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181799553180689095600396061 68174832442758410850148523)
  ·
    refine ⟨102262248664137616275222785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68174832442758410850148523 102262248664137616275222785)
    ·
      refine ⟨76696686498103212206417089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102262248664137616275222785 76696686498103212206417089)
      ·
        refine ⟨57522514873577409154812817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76696686498103212206417089 57522514873577409154812817)
        ·
          refine ⟨43141886155183056866109613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57522514873577409154812817 43141886155183056866109613)
          ·
            refine ⟨16178207308193646324791105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43141886155183056866109613 16178207308193646324791105)
            ·
              refine ⟨12133655481145234743593329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16178207308193646324791105 12133655481145234743593329)
              ·
                refine ⟨9100241610858926057694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133655481145234743593329 9100241610858926057694997)
                ·
                  refine ⟨426573825509012158954453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9100241610858926057694997 426573825509012158954453)
                  ·
                    rfl

theorem cell23_7476746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_7476746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476746 prefixEnd_7476746 := by exact prefixLift 7476746
  have htrace : WordTrace (prefixWord ++ tailWord_7476746) baseStart_7476746 baseEnd_7476746 := by
    simpa [prefixWord, tailWord_7476746, baseEnd_7476746] using wordTrace_append hprefix tailTrace_7476746
  have hstable : (prefixWord ++ tailWord_7476746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476746).length < 2 ^ (prefixWord ++ tailWord_7476746).sum := by decide
  have hdescent : baseEnd_7476746 < baseStart_7476746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476750 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_7476750 : Nat := 118140960795 + 7476750 * 2 ^ 59
def prefixEnd_7476750 : Nat := 4983230072969 + 3 ^ 40 * 7476750 * 2
def baseEnd_7476750 : Nat := 1279722161167909138313353

theorem tailTrace_7476750 : CollatzResearch.WordTrace tailWord_7476750 prefixEnd_7476750 1279722161167909138313353 := by
  unfold tailWord_7476750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34087434457877394010467463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181799650442012768055826469 34087434457877394010467463)
  ·
    refine ⟨51131151686816091015701195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34087434457877394010467463 51131151686816091015701195)
    ·
      refine ⟨76696727530224136523551793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51131151686816091015701195 76696727530224136523551793)
      ·
        refine ⟨57522545647668102392663845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76696727530224136523551793 57522545647668102392663845)
        ·
          refine ⟨10785477308937769198624471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57522545647668102392663845 10785477308937769198624471)
          ·
            refine ⟨16178215963406653797936707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10785477308937769198624471 16178215963406653797936707)
            ·
              refine ⟨24267323945109980696905061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16178215963406653797936707 24267323945109980696905061)
              ·
                refine ⟨4550123239708121380669699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24267323945109980696905061 4550123239708121380669699)
                ·
                  refine ⟨6825184859562182071004549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550123239708121380669699 6825184859562182071004549)
                  ·
                    refine ⟨1279722161167909138313353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825184859562182071004549 1279722161167909138313353)
                    ·
                      rfl

theorem cell23_7476750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_7476750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476750 prefixEnd_7476750 := by exact prefixLift 7476750
  have htrace : WordTrace (prefixWord ++ tailWord_7476750) baseStart_7476750 baseEnd_7476750 := by
    simpa [prefixWord, tailWord_7476750, baseEnd_7476750] using wordTrace_append hprefix tailTrace_7476750
  have hstable : (prefixWord ++ tailWord_7476750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476750).length < 2 ^ (prefixWord ++ tailWord_7476750).sum := by decide
  have hdescent : baseEnd_7476750 < baseStart_7476750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476793 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 1, 5]
def baseStart_7476793 : Nat := 118140960795 + 7476793 * 2 ^ 59
def prefixEnd_7476793 : Nat := 4983230072969 + 3 ^ 40 * 7476793 * 2
def baseEnd_7476793 : Nat := 1279729521057290248900787

theorem tailTrace_7476793 : CollatzResearch.WordTrace tailWord_7476793 prefixEnd_7476793 1279729521057290248900787 := by
  unfold tailWord_7476793
  simp only [CollatzResearch.WordTrace]
  refine ⟨272701044001863370427555033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181800696001242246951703355 272701044001863370427555033)
  ·
    refine ⟨204525783001397527820666275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272701044001863370427555033 204525783001397527820666275)
    ·
      refine ⟨306788674502096291730999413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204525783001397527820666275 306788674502096291730999413)
      ·
        refine ⟨28761438234571527349781195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306788674502096291730999413 28761438234571527349781195)
        ·
          refine ⟨43142157351857291024671793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28761438234571527349781195 43142157351857291024671793)
          ·
            refine ⟨32356618013892968268503845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43142157351857291024671793 32356618013892968268503845)
            ·
              refine ⟨6066865877604931550344471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32356618013892968268503845 6066865877604931550344471)
              ·
                refine ⟨9100298816407397325516707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066865877604931550344471 9100298816407397325516707)
                ·
                  refine ⟨13650448224611095988275061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100298816407397325516707 13650448224611095988275061)
                  ·
                    refine ⟨1279729521057290248900787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13650448224611095988275061 1279729521057290248900787)
                    ·
                      rfl

theorem cell23_7476793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_7476793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476793 prefixEnd_7476793 := by exact prefixLift 7476793
  have htrace : WordTrace (prefixWord ++ tailWord_7476793) baseStart_7476793 baseEnd_7476793 := by
    simpa [prefixWord, tailWord_7476793, baseEnd_7476793] using wordTrace_append hprefix tailTrace_7476793
  have hstable : (prefixWord ++ tailWord_7476793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476793).length < 2 ^ (prefixWord ++ tailWord_7476793).sum := by decide
  have hdescent : baseEnd_7476793 < baseStart_7476793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476809 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_7476809 : Nat := 118140960795 + 7476809 * 2 ^ 59
def prefixEnd_7476809 : Nat := 4983230072969 + 3 ^ 40 * 7476809 * 2
def baseEnd_7476809 : Nat := 3839196778862342684102287

theorem tailTrace_7476809 : CollatzResearch.WordTrace tailWord_7476809 prefixEnd_7476809 3839196778862342684102287 := by
  unfold tailWord_7476809
  simp only [CollatzResearch.WordTrace]
  refine ⟨272701627569805405160137481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181801085046536936773424987 272701627569805405160137481)
  ·
    refine ⟨204526220677354053870103111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272701627569805405160137481 204526220677354053870103111)
    ·
      refine ⟨306789331016031080805154667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204526220677354053870103111 306789331016031080805154667)
      ·
        refine ⟨460183996524046621207732001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306789331016031080805154667 460183996524046621207732001)
        ·
          refine ⟨345137997393034965905799001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460183996524046621207732001 345137997393034965905799001)
          ·
            refine ⟨258853498044776224429349251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345137997393034965905799001 258853498044776224429349251)
            ·
              refine ⟨388280247067164336644023877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258853498044776224429349251 388280247067164336644023877)
              ·
                refine ⟨72802546325093313120754477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388280247067164336644023877 72802546325093313120754477)
                ·
                  refine ⟨27300954871909992420282929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72802546325093313120754477 27300954871909992420282929)
                  ·
                    refine ⟨20475716153932494315212197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27300954871909992420282929 20475716153932494315212197)
                    ·
                      refine ⟨3839196778862342684102287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20475716153932494315212197 3839196778862342684102287)
                      ·
                        rfl

theorem cell23_7476809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_7476809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476809 prefixEnd_7476809 := by exact prefixLift 7476809
  have htrace : WordTrace (prefixWord ++ tailWord_7476809) baseStart_7476809 baseEnd_7476809 := by
    simpa [prefixWord, tailWord_7476809, baseEnd_7476809] using wordTrace_append hprefix tailTrace_7476809
  have hstable : (prefixWord ++ tailWord_7476809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476809).length < 2 ^ (prefixWord ++ tailWord_7476809).sum := by decide
  have hdescent : baseEnd_7476809 < baseStart_7476809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476833 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_7476833 : Nat := 118140960795 + 7476833 * 2 ^ 59
def prefixEnd_7476833 : Nat := 4983230072969 + 3 ^ 40 * 7476833 * 2
def baseEnd_7476833 : Nat := 3839209102398050590202177

theorem tailTrace_7476833 : CollatzResearch.WordTrace tailWord_7476833 prefixEnd_7476833 3839209102398050590202177 := by
  unfold tailWord_7476833
  simp only [CollatzResearch.WordTrace]
  refine ⟨272702502921718457259011153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181801668614478971506007435 272702502921718457259011153)
  ·
    refine ⟨204526877191288842944258365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272702502921718457259011153 204526877191288842944258365)
    ·
      refine ⟨76697578946733316104096887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204526877191288842944258365 76697578946733316104096887)
      ·
        refine ⟨115046368420099974156145331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76697578946733316104096887 115046368420099974156145331)
        ·
          refine ⟨172569552630149961234217997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115046368420099974156145331 172569552630149961234217997)
          ·
            refine ⟨64713582236306235462831749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172569552630149961234217997 64713582236306235462831749)
            ·
              refine ⟨12133796669307419149280953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64713582236306235462831749 12133796669307419149280953)
              ·
                refine ⟨9100347501980564361960715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133796669307419149280953 9100347501980564361960715)
                ·
                  refine ⟨13650521252970846542941073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100347501980564361960715 13650521252970846542941073)
                  ·
                    refine ⟨10237890939728134907205805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13650521252970846542941073 10237890939728134907205805)
                    ·
                      refine ⟨3839209102398050590202177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237890939728134907205805 3839209102398050590202177)
                      ·
                        rfl

theorem cell23_7476833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_7476833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476833 prefixEnd_7476833 := by exact prefixLift 7476833
  have htrace : WordTrace (prefixWord ++ tailWord_7476833) baseStart_7476833 baseEnd_7476833 := by
    simpa [prefixWord, tailWord_7476833, baseEnd_7476833] using wordTrace_append hprefix tailTrace_7476833
  have hstable : (prefixWord ++ tailWord_7476833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476833).length < 2 ^ (prefixWord ++ tailWord_7476833).sum := by decide
  have hdescent : baseEnd_7476833 < baseStart_7476833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476836 : List Nat := [2, 3, 1, 1, 2, 3, 4, 7]
def baseStart_7476836 : Nat := 118140960795 + 7476836 * 2 ^ 59
def prefixEnd_7476836 : Nat := 4983230072969 + 3 ^ 40 * 7476836 * 2
def baseEnd_7476836 : Nat := 142192986771852373276469

theorem tailTrace_7476836 : CollatzResearch.WordTrace tailWord_7476836 prefixEnd_7476836 142192986771852373276469 := by
  unfold tailWord_7476836
  simp only [CollatzResearch.WordTrace]
  refine ⟨136351306170353794385685181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181801741560471725847580241 136351306170353794385685181)
  ·
    refine ⟨51131739813882672894631943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136351306170353794385685181 51131739813882672894631943)
    ·
      refine ⟨76697609720824009341947915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51131739813882672894631943 76697609720824009341947915)
      ·
        refine ⟨115046414581236014012921873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76697609720824009341947915 115046414581236014012921873)
        ·
          refine ⟨86284810935927010509691405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115046414581236014012921873 86284810935927010509691405)
          ·
            refine ⟨32356804100972628941134277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86284810935927010509691405 32356804100972628941134277)
            ·
              refine ⟨6066900768932367926462677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32356804100972628941134277 6066900768932367926462677)
              ·
                refine ⟨142192986771852373276469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6066900768932367926462677 142192986771852373276469)
                ·
                  rfl

theorem cell23_7476836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 7].length) (baseStart_7476836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476836 prefixEnd_7476836 := by exact prefixLift 7476836
  have htrace : WordTrace (prefixWord ++ tailWord_7476836) baseStart_7476836 baseEnd_7476836 := by
    simpa [prefixWord, tailWord_7476836, baseEnd_7476836] using wordTrace_append hprefix tailTrace_7476836
  have hstable : (prefixWord ++ tailWord_7476836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476836).length < 2 ^ (prefixWord ++ tailWord_7476836).sum := by decide
  have hdescent : baseEnd_7476836 < baseStart_7476836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476859 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_7476859 : Nat := 118140960795 + 7476859 * 2 ^ 59
def prefixEnd_7476859 : Nat := 4983230072969 + 3 ^ 40 * 7476859 * 2
def baseEnd_7476859 : Nat := 3839222452895067488477057

theorem tailTrace_7476859 : CollatzResearch.WordTrace tailWord_7476859 prefixEnd_7476859 3839222452895067488477057 := by
  unfold tailWord_7476859
  simp only [CollatzResearch.WordTrace]
  refine ⟨272703451219624263699457631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181802300813082842466305087 272703451219624263699457631)
  ·
    refine ⟨409055176829436395549186447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272703451219624263699457631 409055176829436395549186447)
    ·
      refine ⟨613582765244154593323779671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409055176829436395549186447 613582765244154593323779671)
      ·
        refine ⟨920374147866231889985669507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613582765244154593323779671 920374147866231889985669507)
        ·
          refine ⟨1380561221799347834978504261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920374147866231889985669507 1380561221799347834978504261)
          ·
            refine ⟨258855229087377719058469549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1380561221799347834978504261 258855229087377719058469549)
            ·
              refine ⟨97070710907766644646926081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258855229087377719058469549 97070710907766644646926081)
              ·
                refine ⟨72803033180824983485194561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97070710907766644646926081 72803033180824983485194561)
                ·
                  refine ⟨54602274885618737613895921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72803033180824983485194561 54602274885618737613895921)
                  ·
                    refine ⟨40951706164214053210421941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54602274885618737613895921 40951706164214053210421941)
                    ·
                      refine ⟨3839222452895067488477057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40951706164214053210421941 3839222452895067488477057)
                      ·
                        rfl

theorem cell23_7476859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_7476859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476859 prefixEnd_7476859 := by exact prefixLift 7476859
  have htrace : WordTrace (prefixWord ++ tailWord_7476859) baseStart_7476859 baseEnd_7476859 := by
    simpa [prefixWord, tailWord_7476859, baseEnd_7476859] using wordTrace_append hprefix tailTrace_7476859
  have hstable : (prefixWord ++ tailWord_7476859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476859).length < 2 ^ (prefixWord ++ tailWord_7476859).sum := by decide
  have hdescent : baseEnd_7476859 < baseStart_7476859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7476884 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7476884 : Nat := 118140960795 + 7476884 * 2 ^ 59
def prefixEnd_7476884 : Nat := 4983230072969 + 3 ^ 40 * 7476884 * 2
def baseEnd_7476884 : Nat := 3839235289911429890664443

theorem tailTrace_7476884 : CollatzResearch.WordTrace tailWord_7476884 prefixEnd_7476884 3839235289911429890664443 := by
  unfold tailWord_7476884
  simp only [CollatzResearch.WordTrace]
  refine ⟨136352181522266846484558853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181802908696355795312745137 136352181522266846484558853)
  ·
    refine ⟨25566034035425033715854785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136352181522266846484558853 25566034035425033715854785)
    ·
      refine ⟨19174525526568775286891089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25566034035425033715854785 19174525526568775286891089)
      ·
        refine ⟨14380894144926581465168317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19174525526568775286891089 14380894144926581465168317)
        ·
          refine ⟨5392835304347468049438119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14380894144926581465168317 5392835304347468049438119)
          ·
            refine ⟨8089252956521202074157179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392835304347468049438119 8089252956521202074157179)
            ·
              refine ⟨12133879434781803111235769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089252956521202074157179 12133879434781803111235769)
              ·
                refine ⟨9100409576086352333426827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133879434781803111235769 9100409576086352333426827)
                ·
                  refine ⟨13650614364129528500140241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100409576086352333426827 13650614364129528500140241)
                  ·
                    refine ⟨10237960773097146375105181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13650614364129528500140241 10237960773097146375105181)
                    ·
                      refine ⟨3839235289911429890664443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10237960773097146375105181 3839235289911429890664443)
                      ·
                        rfl

theorem cell23_7476884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7476884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7476884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7476884 prefixEnd_7476884 := by exact prefixLift 7476884
  have htrace : WordTrace (prefixWord ++ tailWord_7476884) baseStart_7476884 baseEnd_7476884 := by
    simpa [prefixWord, tailWord_7476884, baseEnd_7476884] using wordTrace_append hprefix tailTrace_7476884
  have hstable : (prefixWord ++ tailWord_7476884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7476884).length < 2 ^ (prefixWord ++ tailWord_7476884).sum := by decide
  have hdescent : baseEnd_7476884 < baseStart_7476884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7476884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477003 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 3, 4]
def baseStart_7477003 : Nat := 118140960795 + 7477003 * 2 ^ 59
def prefixEnd_7477003 : Nat := 4983230072969 + 3 ^ 40 * 7477003 * 2
def baseEnd_7477003 : Nat := 1279765464703104975025465

theorem tailTrace_7477003 : CollatzResearch.WordTrace tailWord_7477003 prefixEnd_7477003 1279765464703104975025465 := by
  unfold tailWord_7477003
  simp only [CollatzResearch.WordTrace]
  refine ⟨272708703331102576292699663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181805802220735050861799775 272708703331102576292699663)
  ·
    refine ⟨409063054996653864439049495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272708703331102576292699663 409063054996653864439049495)
    ·
      refine ⟨613594582494980796658574243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409063054996653864439049495 613594582494980796658574243)
      ·
        refine ⟨920391873742471194987861365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613594582494980796658574243 920391873742471194987861365)
        ·
          refine ⟨86286738163356674530112003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 920391873742471194987861365 86286738163356674530112003)
          ·
            refine ⟨129430107245035011795168005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86286738163356674530112003 129430107245035011795168005)
            ·
              refine ⟨24268145108444064711594001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129430107245035011795168005 24268145108444064711594001)
              ·
                refine ⟨18201108831333048533695501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24268145108444064711594001 18201108831333048533695501)
                ·
                  refine ⟨6825415811749893200135813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18201108831333048533695501 6825415811749893200135813)
                  ·
                    refine ⟨1279765464703104975025465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825415811749893200135813 1279765464703104975025465)
                    ·
                      rfl

theorem cell23_7477003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 4].length) (baseStart_7477003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477003 prefixEnd_7477003 := by exact prefixLift 7477003
  have htrace : WordTrace (prefixWord ++ tailWord_7477003) baseStart_7477003 baseEnd_7477003 := by
    simpa [prefixWord, tailWord_7477003, baseEnd_7477003] using wordTrace_append hprefix tailTrace_7477003
  have hstable : (prefixWord ++ tailWord_7477003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477003).length < 2 ^ (prefixWord ++ tailWord_7477003).sum := by decide
  have hdescent : baseEnd_7477003 < baseStart_7477003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477010 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7477010 : Nat := 118140960795 + 7477010 * 2 ^ 59
def prefixEnd_7477010 : Nat := 4983230072969 + 3 ^ 40 * 7477010 * 2
def baseEnd_7477010 : Nat := 3839299988473896397688863

theorem tailTrace_7477010 : CollatzResearch.WordTrace tailWord_7477010 prefixEnd_7477010 3839299988473896397688863 := by
  unfold tailWord_7477010
  simp only [CollatzResearch.WordTrace]
  refine ⟨68177239660519304122051121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181805972428051477658802989 68177239660519304122051121)
  ·
    refine ⟨51132929745389478091538341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68177239660519304122051121 51132929745389478091538341)
    ·
      refine ⟨9587424327260527142163439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51132929745389478091538341 9587424327260527142163439)
      ·
        refine ⟨14381136490890790713245159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9587424327260527142163439 14381136490890790713245159)
        ·
          refine ⟨21571704736336186069867739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14381136490890790713245159 21571704736336186069867739)
          ·
            refine ⟨32357557104504279104801609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21571704736336186069867739 32357557104504279104801609)
            ·
              refine ⟨24268167828378209328601207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32357557104504279104801609 24268167828378209328601207)
              ·
                refine ⟨36402251742567313992901811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24268167828378209328601207 36402251742567313992901811)
                ·
                  refine ⟨54603377613850970989352717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36402251742567313992901811 54603377613850970989352717)
                  ·
                    refine ⟨20476266605194114121007269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54603377613850970989352717 20476266605194114121007269)
                    ·
                      refine ⟨3839299988473896397688863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20476266605194114121007269 3839299988473896397688863)
                      ·
                        rfl

theorem cell23_7477010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7477010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477010 prefixEnd_7477010 := by exact prefixLift 7477010
  have htrace : WordTrace (prefixWord ++ tailWord_7477010) baseStart_7477010 baseEnd_7477010 := by
    simpa [prefixWord, tailWord_7477010, baseEnd_7477010] using wordTrace_append hprefix tailTrace_7477010
  have hstable : (prefixWord ++ tailWord_7477010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477010).length < 2 ^ (prefixWord ++ tailWord_7477010).sum := by decide
  have hdescent : baseEnd_7477010 < baseStart_7477010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477013 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_7477013 : Nat := 118140960795 + 7477013 * 2 ^ 59
def prefixEnd_7477013 : Nat := 4983230072969 + 3 ^ 40 * 7477013 * 2
def baseEnd_7477013 : Nat := 3839301528915859885951349

theorem tailTrace_7477013 : CollatzResearch.WordTrace tailWord_7477013 prefixEnd_7477013 3839301528915859885951349 := by
  unfold tailWord_7477013
  simp only [CollatzResearch.WordTrace]
  refine ⟨272709068061066348000563693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181806045374044232000375795 272709068061066348000563693)
  ·
    refine ⟨102265900522899880500211385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272709068061066348000563693 102265900522899880500211385)
    ·
      refine ⟨76699425392174910375158539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102265900522899880500211385 76699425392174910375158539)
      ·
        refine ⟨115049138088262365562737809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76699425392174910375158539 115049138088262365562737809)
        ·
          refine ⟨86286853566196774172053357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115049138088262365562737809 86286853566196774172053357)
          ·
            refine ⟨32357570087323790314520009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86286853566196774172053357 32357570087323790314520009)
            ·
              refine ⟨24268177565492842735890007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32357570087323790314520009 24268177565492842735890007)
              ·
                refine ⟨36402266348239264103835011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24268177565492842735890007 36402266348239264103835011)
                ·
                  refine ⟨54603399522358896155752517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36402266348239264103835011 54603399522358896155752517)
                  ·
                    refine ⟨10238137410442293029203597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54603399522358896155752517 10238137410442293029203597)
                    ·
                      refine ⟨3839301528915859885951349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238137410442293029203597 3839301528915859885951349)
                      ·
                        rfl

theorem cell23_7477013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_7477013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477013 prefixEnd_7477013 := by exact prefixLift 7477013
  have htrace : WordTrace (prefixWord ++ tailWord_7477013) baseStart_7477013 baseEnd_7477013 := by
    simpa [prefixWord, tailWord_7477013, baseEnd_7477013] using wordTrace_append hprefix tailTrace_7477013
  have hstable : (prefixWord ++ tailWord_7477013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477013).length < 2 ^ (prefixWord ++ tailWord_7477013).sum := by decide
  have hdescent : baseEnd_7477013 < baseStart_7477013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477016 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 8]
def baseStart_7477016 : Nat := 118140960795 + 7477016 * 2 ^ 59
def prefixEnd_7477016 : Nat := 4983230072969 + 3 ^ 40 * 7477016 * 2
def baseEnd_7477016 : Nat := 426589229928647041579315

theorem tailTrace_7477016 : CollatzResearch.WordTrace tailWord_7477016 prefixEnd_7477016 426589229928647041579315 := by
  unfold tailWord_7477016
  simp only [CollatzResearch.WordTrace]
  refine ⟨136354588740027739756461451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181806118320036986341948601 136354588740027739756461451)
  ·
    refine ⟨204531883110041609634692177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136354588740027739756461451 204531883110041609634692177)
    ·
      refine ⟨153398912332531207226019133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204531883110041609634692177 153398912332531207226019133)
      ·
        refine ⟨57524592124699202709757175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153398912332531207226019133 57524592124699202709757175)
        ·
          refine ⟨86286888187048804064635763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57524592124699202709757175 86286888187048804064635763)
          ·
            refine ⟨129430332280573206096953645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86286888187048804064635763 129430332280573206096953645)
            ·
              refine ⟨48536374605214952286357617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129430332280573206096953645 48536374605214952286357617)
              ·
                refine ⟨36402280953911214214768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48536374605214952286357617 36402280953911214214768213)
                ·
                  refine ⟨426589229928647041579315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36402280953911214214768213 426589229928647041579315)
                  ·
                    rfl

theorem cell23_7477016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_7477016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477016 prefixEnd_7477016 := by exact prefixLift 7477016
  have htrace : WordTrace (prefixWord ++ tailWord_7477016) baseStart_7477016 baseEnd_7477016 := by
    simpa [prefixWord, tailWord_7477016, baseEnd_7477016] using wordTrace_append hprefix tailTrace_7477016
  have hstable : (prefixWord ++ tailWord_7477016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477016).length < 2 ^ (prefixWord ++ tailWord_7477016).sum := by decide
  have hdescent : baseEnd_7477016 < baseStart_7477016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477050 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_7477050 : Nat := 118140960795 + 7477050 * 2 ^ 59
def prefixEnd_7477050 : Nat := 4983230072969 + 3 ^ 40 * 7477050 * 2
def baseEnd_7477050 : Nat := 426591169744452915687631

theorem tailTrace_7477050 : CollatzResearch.WordTrace tailWord_7477050 prefixEnd_7477050 426591169744452915687631 := by
  unfold tailWord_7477050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68177604390483075829915151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181806945041288202213107069 68177604390483075829915151)
  ·
    refine ⟨102266406585724613744872727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68177604390483075829915151 102266406585724613744872727)
    ·
      refine ⟨153399609878586920617309091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102266406585724613744872727 153399609878586920617309091)
      ·
        refine ⟨230099414817880380925963637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153399609878586920617309091 230099414817880380925963637)
        ·
          refine ⟨21571820139176285711809091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230099414817880380925963637 21571820139176285711809091)
          ·
            refine ⟨32357730208764428567713637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21571820139176285711809091 32357730208764428567713637)
            ·
              refine ⟨6067074414143330356446307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32357730208764428567713637 6067074414143330356446307)
              ·
                refine ⟨9100611621214995534669461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067074414143330356446307 9100611621214995534669461)
                ·
                  refine ⟨426591169744452915687631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9100611621214995534669461 426591169744452915687631)
                  ·
                    rfl

theorem cell23_7477050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_7477050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477050 prefixEnd_7477050 := by exact prefixLift 7477050
  have htrace : WordTrace (prefixWord ++ tailWord_7477050) baseStart_7477050 baseEnd_7477050 := by
    simpa [prefixWord, tailWord_7477050, baseEnd_7477050] using wordTrace_append hprefix tailTrace_7477050
  have hstable : (prefixWord ++ tailWord_7477050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477050).length < 2 ^ (prefixWord ++ tailWord_7477050).sum := by decide
  have hdescent : baseEnd_7477050 < baseStart_7477050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477120 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_7477120 : Nat := 118140960795 + 7477120 * 2 ^ 59
def prefixEnd_7477120 : Nat := 4983230072969 + 3 ^ 40 * 7477120 * 2
def baseEnd_7477120 : Nat := 3839356471345890967313357

theorem tailTrace_7477120 : CollatzResearch.WordTrace tailWord_7477120 prefixEnd_7477120 3839356471345890967313357 := by
  unfold tailWord_7477120
  simp only [CollatzResearch.WordTrace]
  refine ⟨136356485335839352637354407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181808647114452470183139209 136356485335839352637354407)
  ·
    refine ⟨204534728003759028956031611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136356485335839352637354407 204534728003759028956031611)
    ·
      refine ⟨306802092005638543434047417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204534728003759028956031611 306802092005638543434047417)
      ·
        refine ⟨230101569004228907575535563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306802092005638543434047417 230101569004228907575535563)
        ·
          refine ⟨345152353506343361363303345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230101569004228907575535563 345152353506343361363303345)
          ·
            refine ⟨258864265129757521022477509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345152353506343361363303345 258864265129757521022477509)
            ·
              refine ⟨48537049711829535191714533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258864265129757521022477509 48537049711829535191714533)
              ·
                refine ⟨9100696820968037848446475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48537049711829535191714533 9100696820968037848446475)
                ·
                  refine ⟨13651045231452056772669713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100696820968037848446475 13651045231452056772669713)
                  ·
                    refine ⟨10238283923589042579502285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13651045231452056772669713 10238283923589042579502285)
                    ·
                      refine ⟨3839356471345890967313357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238283923589042579502285 3839356471345890967313357)
                      ·
                        rfl

theorem cell23_7477120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_7477120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477120 prefixEnd_7477120 := by exact prefixLift 7477120
  have htrace : WordTrace (prefixWord ++ tailWord_7477120) baseStart_7477120 baseEnd_7477120 := by
    simpa [prefixWord, tailWord_7477120, baseEnd_7477120] using wordTrace_append hprefix tailTrace_7477120
  have hstable : (prefixWord ++ tailWord_7477120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477120).length < 2 ^ (prefixWord ++ tailWord_7477120).sum := by decide
  have hdescent : baseEnd_7477120 < baseStart_7477120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477121 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7477121 : Nat := 118140960795 + 7477121 * 2 ^ 59
def prefixEnd_7477121 : Nat := 4983230072969 + 3 ^ 40 * 7477121 * 2
def baseEnd_7477121 : Nat := 3839356984826545463400853

theorem tailTrace_7477121 : CollatzResearch.WordTrace tailWord_7477121 prefixEnd_7477121 3839356984826545463400853 := by
  unfold tailWord_7477121
  simp only [CollatzResearch.WordTrace]
  refine ⟨272713007144675082445495217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181808671429783388296996811 272713007144675082445495217)
  ·
    refine ⟨204534755358506311834121413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272713007144675082445495217 204534755358506311834121413)
    ·
      refine ⟨38350266629719933468897765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204534755358506311834121413 38350266629719933468897765)
      ·
        refine ⟨7190674993072487525418331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38350266629719933468897765 7190674993072487525418331)
        ·
          refine ⟨10786012489608731288127497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190674993072487525418331 10786012489608731288127497)
          ·
            refine ⟨8089509367206548466095623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786012489608731288127497 8089509367206548466095623)
            ·
              refine ⟨12134264050809822699143435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089509367206548466095623 12134264050809822699143435)
              ·
                refine ⟨18201396076214734048715153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134264050809822699143435 18201396076214734048715153)
                ·
                  refine ⟨13651047057161050536536365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18201396076214734048715153 13651047057161050536536365)
                  ·
                    refine ⟨5119142646435393951201137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13651047057161050536536365 5119142646435393951201137)
                    ·
                      refine ⟨3839356984826545463400853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119142646435393951201137 3839356984826545463400853)
                      ·
                        rfl

theorem cell23_7477121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7477121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477121 prefixEnd_7477121 := by exact prefixLift 7477121
  have htrace : WordTrace (prefixWord ++ tailWord_7477121) baseStart_7477121 baseEnd_7477121 := by
    simpa [prefixWord, tailWord_7477121, baseEnd_7477121] using wordTrace_append hprefix tailTrace_7477121
  have hstable : (prefixWord ++ tailWord_7477121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477121).length < 2 ^ (prefixWord ++ tailWord_7477121).sum := by decide
  have hdescent : baseEnd_7477121 < baseStart_7477121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477134 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7477134 : Nat := 118140960795 + 7477134 * 2 ^ 59
def prefixEnd_7477134 : Nat := 4983230072969 + 3 ^ 40 * 7477134 * 2
def baseEnd_7477134 : Nat := 3839363660075053912538293

theorem tailTrace_7477134 : CollatzResearch.WordTrace tailWord_7477134 prefixEnd_7477134 3839363660075053912538293 := by
  unfold tailWord_7477134
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089185161703498208214807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181808987529085323777145637 34089185161703498208214807)
  ·
    refine ⟨51133777742555247312322211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34089185161703498208214807 51133777742555247312322211)
    ·
      refine ⟨76700666613832870968483317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51133777742555247312322211 76700666613832870968483317)
      ·
        refine ⟨7190687495046831653295311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76700666613832870968483317 7190687495046831653295311)
        ·
          refine ⟨10786031242570247479942967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190687495046831653295311 10786031242570247479942967)
          ·
            refine ⟨16179046863855371219914451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10786031242570247479942967 16179046863855371219914451)
            ·
              refine ⟨24268570295783056829871677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16179046863855371219914451 24268570295783056829871677)
              ·
                refine ⟨9100713860918646311201879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24268570295783056829871677 9100713860918646311201879)
                ·
                  refine ⟨13651070791377969466802819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100713860918646311201879 13651070791377969466802819)
                  ·
                    refine ⟨20476606187066954200204229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13651070791377969466802819 20476606187066954200204229)
                    ·
                      refine ⟨3839363660075053912538293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20476606187066954200204229 3839363660075053912538293)
                      ·
                        rfl

theorem cell23_7477134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7477134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477134 prefixEnd_7477134 := by exact prefixLift 7477134
  have htrace : WordTrace (prefixWord ++ tailWord_7477134) baseStart_7477134 baseEnd_7477134 := by
    simpa [prefixWord, tailWord_7477134, baseEnd_7477134] using wordTrace_append hprefix tailTrace_7477134
  have hstable : (prefixWord ++ tailWord_7477134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477134).length < 2 ^ (prefixWord ++ tailWord_7477134).sum := by decide
  have hdescent : baseEnd_7477134 < baseStart_7477134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477137 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_7477137 : Nat := 118140960795 + 7477137 * 2 ^ 59
def prefixEnd_7477137 : Nat := 4983230072969 + 3 ^ 40 * 7477137 * 2
def baseEnd_7477137 : Nat := 3839365200517017400800779

theorem tailTrace_7477137 : CollatzResearch.WordTrace tailWord_7477137 prefixEnd_7477137 3839365200517017400800779 := by
  unfold tailWord_7477137
  simp only [CollatzResearch.WordTrace]
  refine ⟨272713590712617117178077665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181809060475078078118718443 272713590712617117178077665)
  ·
    refine ⟨204535193034462837883558249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272713590712617117178077665 204535193034462837883558249)
    ·
      refine ⟨153401394775847128412668687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204535193034462837883558249 153401394775847128412668687)
      ·
        refine ⟨230102092163770692619003031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153401394775847128412668687 230102092163770692619003031)
        ·
          refine ⟨345153138245656038928504547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230102092163770692619003031 345153138245656038928504547)
          ·
            refine ⟨517729707368484058392756821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345153138245656038928504547 517729707368484058392756821)
            ·
              refine ⟨6067145008224422559290119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 517729707368484058392756821 6067145008224422559290119)
              ·
                refine ⟨9100717512336633838935179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067145008224422559290119 9100717512336633838935179)
                ·
                  refine ⟨13651076268504950758402769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100717512336633838935179 13651076268504950758402769)
                  ·
                    refine ⟨10238307201378713068802077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13651076268504950758402769 10238307201378713068802077)
                    ·
                      refine ⟨3839365200517017400800779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238307201378713068802077 3839365200517017400800779)
                      ·
                        rfl

theorem cell23_7477137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_7477137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477137 prefixEnd_7477137 := by exact prefixLift 7477137
  have htrace : WordTrace (prefixWord ++ tailWord_7477137) baseStart_7477137 baseEnd_7477137 := by
    simpa [prefixWord, tailWord_7477137, baseEnd_7477137] using wordTrace_append hprefix tailTrace_7477137
  have hstable : (prefixWord ++ tailWord_7477137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477137).length < 2 ^ (prefixWord ++ tailWord_7477137).sum := by decide
  have hdescent : baseEnd_7477137 < baseStart_7477137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477193 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_7477193 : Nat := 118140960795 + 7477193 * 2 ^ 59
def prefixEnd_7477193 : Nat := 4983230072969 + 3 ^ 40 * 7477193 * 2
def baseEnd_7477193 : Nat := 3839393955433669181700521

theorem tailTrace_7477193 : CollatzResearch.WordTrace tailWord_7477193 prefixEnd_7477193 3839393955433669181700521 := by
  unfold tailWord_7477193
  simp only [CollatzResearch.WordTrace]
  refine ⟨272715633200414238742116233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181810422133609492494744155 272715633200414238742116233)
  ·
    refine ⟨204536724900310679056587175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272715633200414238742116233 204536724900310679056587175)
    ·
      refine ⟨306805087350466018584880763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204536724900310679056587175 306805087350466018584880763)
      ·
        refine ⟨460207631025699027877321145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306805087350466018584880763 460207631025699027877321145)
        ·
          refine ⟨345155723269274270907990859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460207631025699027877321145 345155723269274270907990859)
          ·
            refine ⟨517733584903911406361986289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345155723269274270907990859 517733584903911406361986289)
            ·
              refine ⟨388300188677933554771489717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517733584903911406361986289 388300188677933554771489717)
              ·
                refine ⟨36403142688556270759827161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388300188677933554771489717 36403142688556270759827161)
                ·
                  refine ⟨27302357016417203069870371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36403142688556270759827161 27302357016417203069870371)
                  ·
                    refine ⟨40953535524625804604805557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27302357016417203069870371 40953535524625804604805557)
                    ·
                      refine ⟨3839393955433669181700521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40953535524625804604805557 3839393955433669181700521)
                      ·
                        rfl

theorem cell23_7477193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_7477193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477193 prefixEnd_7477193 := by exact prefixLift 7477193
  have htrace : WordTrace (prefixWord ++ tailWord_7477193) baseStart_7477193 baseEnd_7477193 := by
    simpa [prefixWord, tailWord_7477193, baseEnd_7477193] using wordTrace_append hprefix tailTrace_7477193
  have hstable : (prefixWord ++ tailWord_7477193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477193).length < 2 ^ (prefixWord ++ tailWord_7477193).sum := by decide
  have hdescent : baseEnd_7477193 < baseStart_7477193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477207 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_7477207 : Nat := 118140960795 + 7477207 * 2 ^ 59
def prefixEnd_7477207 : Nat := 4983230072969 + 3 ^ 40 * 7477207 * 2
def baseEnd_7477207 : Nat := 3839401144162832126925457

theorem tailTrace_7477207 : CollatzResearch.WordTrace tailWord_7477207 prefixEnd_7477207 3839401144162832126925457 := by
  unfold tailWord_7477207
  simp only [CollatzResearch.WordTrace]
  refine ⟨272716143822363519133125875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181810762548242346088750583 272716143822363519133125875)
  ·
    refine ⟨409074215733545278699688813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272716143822363519133125875 409074215733545278699688813)
    ·
      refine ⟨153402830900079479512383305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409074215733545278699688813 153402830900079479512383305)
      ·
        refine ⟨115052123175059609634287479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153402830900079479512383305 115052123175059609634287479)
        ·
          refine ⟨172578184762589414451431219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115052123175059609634287479 172578184762589414451431219)
          ·
            refine ⟨258867277143884121677146829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172578184762589414451431219 258867277143884121677146829)
            ·
              refine ⟨97075228928956545628930061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258867277143884121677146829 97075228928956545628930061)
              ·
                refine ⟨36403210848358704610848773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97075228928956545628930061 36403210848358704610848773)
                ·
                  refine ⟨6825602034067257114534145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36403210848358704610848773 6825602034067257114534145)
                  ·
                    refine ⟨5119201525550442835900609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6825602034067257114534145 5119201525550442835900609)
                    ·
                      refine ⟨3839401144162832126925457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119201525550442835900609 3839401144162832126925457)
                      ·
                        rfl

theorem cell23_7477207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_7477207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477207 prefixEnd_7477207 := by exact prefixLift 7477207
  have htrace : WordTrace (prefixWord ++ tailWord_7477207) baseStart_7477207 baseEnd_7477207 := by
    simpa [prefixWord, tailWord_7477207, baseEnd_7477207] using wordTrace_append hprefix tailTrace_7477207
  have hstable : (prefixWord ++ tailWord_7477207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477207).length < 2 ^ (prefixWord ++ tailWord_7477207).sum := by decide
  have hdescent : baseEnd_7477207 < baseStart_7477207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477243 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 7]
def baseStart_7477243 : Nat := 118140960795 + 7477243 * 2 ^ 59
def prefixEnd_7477243 : Nat := 4983230072969 + 3 ^ 40 * 7477243 * 2
def baseEnd_7477243 : Nat := 1279806543155464662025097

theorem tailTrace_7477243 : CollatzResearch.WordTrace tailWord_7477243 prefixEnd_7477243 1279806543155464662025097 := by
  unfold tailWord_7477243
  simp only [CollatzResearch.WordTrace]
  refine ⟨272717456850233097281436383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181811637900155398187624255 272717456850233097281436383)
  ·
    refine ⟨409076185275349645922154575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272717456850233097281436383 409076185275349645922154575)
    ·
      refine ⟨613614277913024468883231863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409076185275349645922154575 613614277913024468883231863)
      ·
        refine ⟨920421416869536703324847795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613614277913024468883231863 920421416869536703324847795)
        ·
          refine ⟨1380632125304305054987271693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920421416869536703324847795 1380632125304305054987271693)
          ·
            refine ⟨517737046989114395620226885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1380632125304305054987271693 517737046989114395620226885)
            ·
              refine ⟨97075696310458949178792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517737046989114395620226885 97075696310458949178792541)
              ·
                refine ⟨36403386116422105942047203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97075696310458949178792541 36403386116422105942047203)
                ·
                  refine ⟨54605079174633158913070805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36403386116422105942047203 54605079174633158913070805)
                  ·
                    refine ⟨1279806543155464662025097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54605079174633158913070805 1279806543155464662025097)
                    ·
                      rfl

theorem cell23_7477243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_7477243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477243 prefixEnd_7477243 := by exact prefixLift 7477243
  have htrace : WordTrace (prefixWord ++ tailWord_7477243) baseStart_7477243 baseEnd_7477243 := by
    simpa [prefixWord, tailWord_7477243, baseEnd_7477243] using wordTrace_append hprefix tailTrace_7477243
  have hstable : (prefixWord ++ tailWord_7477243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477243).length < 2 ^ (prefixWord ++ tailWord_7477243).sum := by decide
  have hdescent : baseEnd_7477243 < baseStart_7477243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477260 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_7477260 : Nat := 118140960795 + 7477260 * 2 ^ 59
def prefixEnd_7477260 : Nat := 4983230072969 + 3 ^ 40 * 7477260 * 2
def baseEnd_7477260 : Nat := 1279809452879173473187571

theorem tailTrace_7477260 : CollatzResearch.WordTrace tailWord_7477260 prefixEnd_7477260 1279809452879173473187571 := by
  unfold tailWord_7477260
  simp only [CollatzResearch.WordTrace]
  refine ⟨136359038445585754592402617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181812051260781006123203489 136359038445585754592402617)
  ·
    refine ⟨102269278834189315944301963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136359038445585754592402617 102269278834189315944301963)
    ·
      refine ⟨153403918251283973916452945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102269278834189315944301963 153403918251283973916452945)
      ·
        refine ⟨115052938688462980437339709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153403918251283973916452945 115052938688462980437339709)
        ·
          refine ⟨43144852008173617664002391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115052938688462980437339709 43144852008173617664002391)
          ·
            refine ⟨64717278012260426496003587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43144852008173617664002391 64717278012260426496003587)
            ·
              refine ⟨97075917018390639744005381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64717278012260426496003587 97075917018390639744005381)
              ·
                refine ⟨18201734440948244952001009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97075917018390639744005381 18201734440948244952001009)
                ·
                  refine ⟨13651300830711183714000757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18201734440948244952001009 13651300830711183714000757)
                  ·
                    refine ⟨1279809452879173473187571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13651300830711183714000757 1279809452879173473187571)
                    ·
                      rfl

theorem cell23_7477260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_7477260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477260 prefixEnd_7477260 := by exact prefixLift 7477260
  have htrace : WordTrace (prefixWord ++ tailWord_7477260) baseStart_7477260 baseEnd_7477260 := by
    simpa [prefixWord, tailWord_7477260, baseEnd_7477260] using wordTrace_append hprefix tailTrace_7477260
  have hstable : (prefixWord ++ tailWord_7477260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477260).length < 2 ^ (prefixWord ++ tailWord_7477260).sum := by decide
  have hdescent : baseEnd_7477260 < baseStart_7477260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477273 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_7477273 : Nat := 118140960795 + 7477273 * 2 ^ 59
def prefixEnd_7477273 : Nat := 4983230072969 + 3 ^ 40 * 7477273 * 2
def baseEnd_7477273 : Nat := 1279811677962009622900051

theorem tailTrace_7477273 : CollatzResearch.WordTrace tailWord_7477273 prefixEnd_7477273 1279811677962009622900051 := by
  unfold tailWord_7477273
  simp only [CollatzResearch.WordTrace]
  refine ⟨272718551040124412405028473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181812367360082941603352315 272718551040124412405028473)
  ·
    refine ⟨204538913280093309303771355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272718551040124412405028473 204538913280093309303771355)
    ·
      refine ⟨306808369920139963955657033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204538913280093309303771355 306808369920139963955657033)
      ·
        refine ⟨230106277440104972966742775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306808369920139963955657033 230106277440104972966742775)
        ·
          refine ⟨345159416160157459450114163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230106277440104972966742775 345159416160157459450114163)
          ·
            refine ⟨517739124240236189175171245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345159416160157459450114163 517739124240236189175171245)
            ·
              refine ⟨194152171590088570940689217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517739124240236189175171245 194152171590088570940689217)
              ·
                refine ⟨145614128692566428205516913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194152171590088570940689217 145614128692566428205516913)
                ·
                  refine ⟨109210596519424821154137685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145614128692566428205516913 109210596519424821154137685)
                  ·
                    refine ⟨1279811677962009622900051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109210596519424821154137685 1279811677962009622900051)
                    ·
                      rfl

theorem cell23_7477273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_7477273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477273 prefixEnd_7477273 := by exact prefixLift 7477273
  have htrace : WordTrace (prefixWord ++ tailWord_7477273) baseStart_7477273 baseEnd_7477273 := by
    simpa [prefixWord, tailWord_7477273, baseEnd_7477273] using wordTrace_append hprefix tailTrace_7477273
  have hstable : (prefixWord ++ tailWord_7477273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477273).length < 2 ^ (prefixWord ++ tailWord_7477273).sum := by decide
  have hdescent : baseEnd_7477273 < baseStart_7477273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477294 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7477294 : Nat := 118140960795 + 7477294 * 2 ^ 59
def prefixEnd_7477294 : Nat := 4983230072969 + 3 ^ 40 * 7477294 * 2
def baseEnd_7477294 : Nat := 1279815272326591095512519

theorem tailTrace_7477294 : CollatzResearch.WordTrace tailWord_7477294 prefixEnd_7477294 1279815272326591095512519 := by
  unfold tailWord_7477294
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089914621631041623942867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181812877982032221994361957 34089914621631041623942867)
  ·
    refine ⟨51134871932446562435914301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34089914621631041623942867 51134871932446562435914301)
    ·
      refine ⟨19175576974667460913467863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51134871932446562435914301 19175576974667460913467863)
      ·
        refine ⟨28763365462001191370201795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19175576974667460913467863 28763365462001191370201795)
        ·
          refine ⟨43145048193001787055302693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28763365462001191370201795 43145048193001787055302693)
          ·
            refine ⟨8089696536187835072869255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43145048193001787055302693 8089696536187835072869255)
            ·
              refine ⟨12134544804281752609303883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089696536187835072869255 12134544804281752609303883)
              ·
                refine ⟨18201817206422628913955825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134544804281752609303883 18201817206422628913955825)
                ·
                  refine ⟨13651362904816971685466869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18201817206422628913955825 13651362904816971685466869)
                  ·
                    refine ⟨1279815272326591095512519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13651362904816971685466869 1279815272326591095512519)
                    ·
                      rfl

theorem cell23_7477294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7477294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477294 prefixEnd_7477294 := by exact prefixLift 7477294
  have htrace : WordTrace (prefixWord ++ tailWord_7477294) baseStart_7477294 baseEnd_7477294 := by
    simpa [prefixWord, tailWord_7477294, baseEnd_7477294] using wordTrace_append hprefix tailTrace_7477294
  have hstable : (prefixWord ++ tailWord_7477294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477294).length < 2 ^ (prefixWord ++ tailWord_7477294).sum := by decide
  have hdescent : baseEnd_7477294 < baseStart_7477294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477297 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_7477297 : Nat := 118140960795 + 7477297 * 2 ^ 59
def prefixEnd_7477297 : Nat := 4983230072969 + 3 ^ 40 * 7477297 * 2
def baseEnd_7477297 : Nat := 3839447357421736774800043

theorem tailTrace_7477297 : CollatzResearch.WordTrace tailWord_7477297 prefixEnd_7477297 3839447357421736774800043 := by
  unfold tailWord_7477297
  simp only [CollatzResearch.WordTrace]
  refine ⟨272719426392037464503902145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181812950928024976335934763 272719426392037464503902145)
  ·
    refine ⟨204539569794028098377926609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272719426392037464503902145 204539569794028098377926609)
    ·
      refine ⟨153404677345521073783444957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204539569794028098377926609 153404677345521073783444957)
      ·
        refine ⟨57526754004570402668791859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153404677345521073783444957 57526754004570402668791859)
        ·
          refine ⟨86290131006855604003187789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57526754004570402668791859 86290131006855604003187789)
          ·
            refine ⟨32358799127570851501195421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86290131006855604003187789 32358799127570851501195421)
            ·
              refine ⟨12134549672839069312948283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32358799127570851501195421 12134549672839069312948283)
              ·
                refine ⟨18201824509258603969422425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134549672839069312948283 18201824509258603969422425)
                ·
                  refine ⟨13651368381943952977066819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18201824509258603969422425 13651368381943952977066819)
                  ·
                    refine ⟨20477052572915929465600229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13651368381943952977066819 20477052572915929465600229)
                    ·
                      refine ⟨3839447357421736774800043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20477052572915929465600229 3839447357421736774800043)
                      ·
                        rfl

theorem cell23_7477297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_7477297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477297 prefixEnd_7477297 := by exact prefixLift 7477297
  have htrace : WordTrace (prefixWord ++ tailWord_7477297) baseStart_7477297 baseEnd_7477297 := by
    simpa [prefixWord, tailWord_7477297, baseEnd_7477297] using wordTrace_append hprefix tailTrace_7477297
  have hstable : (prefixWord ++ tailWord_7477297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477297).length < 2 ^ (prefixWord ++ tailWord_7477297).sum := by decide
  have hdescent : baseEnd_7477297 < baseStart_7477297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477320 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 6]
def baseStart_7477320 : Nat := 118140960795 + 7477320 * 2 ^ 59
def prefixEnd_7477320 : Nat := 4983230072969 + 3 ^ 40 * 7477320 * 2
def baseEnd_7477320 : Nat := 426606574164087798312493

theorem tailTrace_7477320 : CollatzResearch.WordTrace tailWord_7477320 prefixEnd_7477320 426606574164087798312493 := by
  unfold tailWord_7477320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136360132635477069715994707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181813510180636092954659609 136360132635477069715994707)
  ·
    refine ⟨204540198953215604573992061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136360132635477069715994707 204540198953215604573992061)
    ·
      refine ⟨76702574607455851715247023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204540198953215604573992061 76702574607455851715247023)
      ·
        refine ⟨115053861911183777572870535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76702574607455851715247023 115053861911183777572870535)
        ·
          refine ⟨172580792866775666359305803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115053861911183777572870535 172580792866775666359305803)
          ·
            refine ⟨258871189300163499538958705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172580792866775666359305803 258871189300163499538958705)
            ·
              refine ⟨194153391975122624654219029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258871189300163499538958705 194153391975122624654219029)
              ·
                refine ⟨9100940248833873030666517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194153391975122624654219029 9100940248833873030666517)
                ·
                  refine ⟨426606574164087798312493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9100940248833873030666517 426606574164087798312493)
                  ·
                    rfl

theorem cell23_7477320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_7477320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477320 prefixEnd_7477320 := by exact prefixLift 7477320
  have htrace : WordTrace (prefixWord ++ tailWord_7477320) baseStart_7477320 baseEnd_7477320 := by
    simpa [prefixWord, tailWord_7477320, baseEnd_7477320] using wordTrace_append hprefix tailTrace_7477320
  have hstable : (prefixWord ++ tailWord_7477320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477320).length < 2 ^ (prefixWord ++ tailWord_7477320).sum := by decide
  have hdescent : baseEnd_7477320 < baseStart_7477320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477324 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_7477324 : Nat := 118140960795 + 7477324 * 2 ^ 59
def prefixEnd_7477324 : Nat := 4983230072969 + 3 ^ 40 * 7477324 * 2
def baseEnd_7477324 : Nat := 1279820407133136056387473

theorem tailTrace_7477324 : CollatzResearch.WordTrace tailWord_7477324 prefixEnd_7477324 1279820407133136056387473 := by
  unfold tailWord_7477324
  simp only [CollatzResearch.WordTrace]
  refine ⟨136360205581469824057567513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181813607441959765410090017 136360205581469824057567513)
  ·
    refine ⟨102270154186102368043175635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136360205581469824057567513 102270154186102368043175635)
    ·
      refine ⟨153405231279153552064763453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102270154186102368043175635 153405231279153552064763453)
      ·
        refine ⟨57526961729682582024286295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153405231279153552064763453 57526961729682582024286295)
        ·
          refine ⟨86290442594523873036429443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57526961729682582024286295 86290442594523873036429443)
          ·
            refine ⟨129435663891785809554644165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86290442594523873036429443 129435663891785809554644165)
            ·
              refine ⟨24269186979709839291495781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129435663891785809554644165 24269186979709839291495781)
              ·
                refine ⟨4550472558695594867155459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24269186979709839291495781 4550472558695594867155459)
                ·
                  refine ⟨6825708838043392300733189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550472558695594867155459 6825708838043392300733189)
                  ·
                    refine ⟨1279820407133136056387473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825708838043392300733189 1279820407133136056387473)
                    ·
                      rfl

theorem cell23_7477324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_7477324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477324 prefixEnd_7477324 := by exact prefixLift 7477324
  have htrace : WordTrace (prefixWord ++ tailWord_7477324) baseStart_7477324 baseEnd_7477324 := by
    simpa [prefixWord, tailWord_7477324, baseEnd_7477324] using wordTrace_append hprefix tailTrace_7477324
  have hstable : (prefixWord ++ tailWord_7477324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477324).length < 2 ^ (prefixWord ++ tailWord_7477324).sum := by decide
  have hdescent : baseEnd_7477324 < baseStart_7477324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477337 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 6]
def baseStart_7477337 : Nat := 118140960795 + 7477337 * 2 ^ 59
def prefixEnd_7477337 : Nat := 4983230072969 + 3 ^ 40 * 7477337 * 2
def baseEnd_7477337 : Nat := 426607544071990735366651

theorem tailTrace_7477337 : CollatzResearch.WordTrace tailWord_7477337 prefixEnd_7477337 426607544071990735366651 := by
  unfold tailWord_7477337
  simp only [CollatzResearch.WordTrace]
  refine ⟨272720885311892551335358265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181813923541261700890238843 272720885311892551335358265)
  ·
    refine ⟨204540663983919413501518699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272720885311892551335358265 204540663983919413501518699)
    ·
      refine ⟨306810995975879120252278049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204540663983919413501518699 306810995975879120252278049)
      ·
        refine ⟨230108246981909340189208537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306810995975879120252278049 230108246981909340189208537)
        ·
          refine ⟨172581185236432005141906403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230108246981909340189208537 172581185236432005141906403)
          ·
            refine ⟨258871777854648007712859605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172581185236432005141906403 258871777854648007712859605)
            ·
              refine ⟨6067307293468312680770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 258871777854648007712859605 6067307293468312680770147)
              ·
                refine ⟨9100960940202469021155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067307293468312680770147 9100960940202469021155221)
                ·
                  refine ⟨426607544071990735366651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9100960940202469021155221 426607544071990735366651)
                  ·
                    rfl

theorem cell23_7477337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 6].length) (baseStart_7477337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477337 prefixEnd_7477337 := by exact prefixLift 7477337
  have htrace : WordTrace (prefixWord ++ tailWord_7477337) baseStart_7477337 baseEnd_7477337 := by
    simpa [prefixWord, tailWord_7477337, baseEnd_7477337] using wordTrace_append hprefix tailTrace_7477337
  have hstable : (prefixWord ++ tailWord_7477337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477337).length < 2 ^ (prefixWord ++ tailWord_7477337).sum := by decide
  have hdescent : baseEnd_7477337 < baseStart_7477337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477367 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 1, 5]
def baseStart_7477367 : Nat := 118140960795 + 7477367 * 2 ^ 59
def prefixEnd_7477367 : Nat := 4983230072969 + 3 ^ 40 * 7477367 * 2
def baseEnd_7477367 : Nat := 1279827767022517166974907

theorem tailTrace_7477367 : CollatzResearch.WordTrace tailWord_7477367 prefixEnd_7477367 1279827767022517166974907 := by
  unfold tailWord_7477367
  simp only [CollatzResearch.WordTrace]
  refine ⟨272721979501783866458950355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181814653001189244305966903 272721979501783866458950355)
  ·
    refine ⟨409082969252675799688425533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272721979501783866458950355 409082969252675799688425533)
    ·
      refine ⟨153406113469753424883159575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409082969252675799688425533 153406113469753424883159575)
      ·
        refine ⟨230109170204630137324739363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153406113469753424883159575 230109170204630137324739363)
        ·
          refine ⟨345163755306945205987109045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230109170204630137324739363 345163755306945205987109045)
          ·
            refine ⟨32359102060026113061291473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345163755306945205987109045 32359102060026113061291473)
            ·
              refine ⟨24269326545019584795968605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32359102060026113061291473 24269326545019584795968605)
              ·
                refine ⟨9100997454382344298488227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24269326545019584795968605 9100997454382344298488227)
                ·
                  refine ⟨13651496181573516447732341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9100997454382344298488227 13651496181573516447732341)
                  ·
                    refine ⟨1279827767022517166974907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13651496181573516447732341 1279827767022517166974907)
                    ·
                      rfl

theorem cell23_7477367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_7477367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477367 prefixEnd_7477367 := by exact prefixLift 7477367
  have htrace : WordTrace (prefixWord ++ tailWord_7477367) baseStart_7477367 baseEnd_7477367 := by
    simpa [prefixWord, tailWord_7477367, baseEnd_7477367] using wordTrace_append hprefix tailTrace_7477367
  have hstable : (prefixWord ++ tailWord_7477367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477367).length < 2 ^ (prefixWord ++ tailWord_7477367).sum := by decide
  have hdescent : baseEnd_7477367 < baseStart_7477367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477381 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_7477381 : Nat := 118140960795 + 7477381 * 2 ^ 59
def prefixEnd_7477381 : Nat := 4983230072969 + 3 ^ 40 * 7477381 * 2
def baseEnd_7477381 : Nat := 3839490489796714446149657

theorem tailTrace_7477381 : CollatzResearch.WordTrace tailWord_7477381 prefixEnd_7477381 3839490489796714446149657 := by
  unfold tailWord_7477381
  simp only [CollatzResearch.WordTrace]
  refine ⟨272722490123733146849959997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181814993415822097899973331 272722490123733146849959997)
  ·
    refine ⟨102270933796399930068734999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272722490123733146849959997 102270933796399930068734999)
    ·
      refine ⟨153406400694599895103102499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102270933796399930068734999 153406400694599895103102499)
      ·
        refine ⟨230109601041899842654653749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153406400694599895103102499 230109601041899842654653749)
        ·
          refine ⟨21572775097678110248873789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230109601041899842654653749 21572775097678110248873789)
          ·
            refine ⟨8089790661629291343327671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21572775097678110248873789 8089790661629291343327671)
            ·
              refine ⟨12134685992443937014991507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089790661629291343327671 12134685992443937014991507)
              ·
                refine ⟨18202028988665905522487261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134685992443937014991507 18202028988665905522487261)
                ·
                  refine ⟨6825760870749714570932723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18202028988665905522487261 6825760870749714570932723)
                  ·
                    refine ⟨10238641306124571856399085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6825760870749714570932723 10238641306124571856399085)
                    ·
                      refine ⟨3839490489796714446149657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238641306124571856399085 3839490489796714446149657)
                      ·
                        rfl

theorem cell23_7477381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_7477381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477381 prefixEnd_7477381 := by exact prefixLift 7477381
  have htrace : WordTrace (prefixWord ++ tailWord_7477381) baseStart_7477381 baseEnd_7477381 := by
    simpa [prefixWord, tailWord_7477381, baseEnd_7477381] using wordTrace_append hprefix tailTrace_7477381
  have hstable : (prefixWord ++ tailWord_7477381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477381).length < 2 ^ (prefixWord ++ tailWord_7477381).sum := by decide
  have hdescent : baseEnd_7477381 < baseStart_7477381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477418 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7477418 : Nat := 118140960795 + 7477418 * 2 ^ 59
def prefixEnd_7477418 : Nat := 4983230072969 + 3 ^ 40 * 7477418 * 2
def baseEnd_7477418 : Nat := 1279836496193643600462329

theorem tailTrace_7477418 : CollatzResearch.WordTrace tailWord_7477418 prefixEnd_7477418 1279836496193643600462329 := by
  unfold tailWord_7477418
  simp only [CollatzResearch.WordTrace]
  refine ⟨68180959906149775542264227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181815893083066068112704605 68180959906149775542264227)
  ·
    refine ⟨102271439859224663313396341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68180959906149775542264227 102271439859224663313396341)
    ·
      refine ⟨9587947486802312185630907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102271439859224663313396341 9587947486802312185630907)
      ·
        refine ⟨14381921230203468278446361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9587947486802312185630907 14381921230203468278446361)
        ·
          refine ⟨10786440922652601208834771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14381921230203468278446361 10786440922652601208834771)
          ·
            refine ⟨16179661383978901813252157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10786440922652601208834771 16179661383978901813252157)
            ·
              refine ⟨6067373018992088179969559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16179661383978901813252157 6067373018992088179969559)
              ·
                refine ⟨9101059528488132269954339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067373018992088179969559 9101059528488132269954339)
                ·
                  refine ⟨13651589292732198404931509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101059528488132269954339 13651589292732198404931509)
                  ·
                    refine ⟨1279836496193643600462329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13651589292732198404931509 1279836496193643600462329)
                    ·
                      rfl

theorem cell23_7477418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7477418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477418 prefixEnd_7477418 := by exact prefixLift 7477418
  have htrace : WordTrace (prefixWord ++ tailWord_7477418) baseStart_7477418 baseEnd_7477418 := by
    simpa [prefixWord, tailWord_7477418, baseEnd_7477418] using wordTrace_append hprefix tailTrace_7477418
  have hstable : (prefixWord ++ tailWord_7477418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477418).length < 2 ^ (prefixWord ++ tailWord_7477418).sum := by decide
  have hdescent : baseEnd_7477418 < baseStart_7477418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477437 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_7477437 : Nat := 118140960795 + 7477437 * 2 ^ 59
def prefixEnd_7477437 : Nat := 4983230072969 + 3 ^ 40 * 7477437 * 2
def baseEnd_7477437 : Nat := 3839519244713366227049399

theorem tailTrace_7477437 : CollatzResearch.WordTrace tailWord_7477437 prefixEnd_7477437 3839519244713366227049399 := by
  unfold tailWord_7477437
  simp only [CollatzResearch.WordTrace]
  refine ⟨272724532611530268413998565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181816355074353512275999043 272724532611530268413998565)
  ·
    refine ⟨51135849864661925327624731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272724532611530268413998565 51135849864661925327624731)
    ·
      refine ⟨76703774796992887991437097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51135849864661925327624731 76703774796992887991437097)
      ·
        refine ⟨57527831097744665993577823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76703774796992887991437097 57527831097744665993577823)
        ·
          refine ⟨86291746646616998990366735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57527831097744665993577823 86291746646616998990366735)
          ·
            refine ⟨129437619969925498485550103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86291746646616998990366735 129437619969925498485550103)
            ·
              refine ⟨194156429954888247728325155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129437619969925498485550103 194156429954888247728325155)
              ·
                refine ⟨291234644932332371592487733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194156429954888247728325155 291234644932332371592487733)
                ·
                  refine ⟨27303247962406159836795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291234644932332371592487733 27303247962406159836795725)
                  ·
                    refine ⟨10238717985902309938798397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27303247962406159836795725 10238717985902309938798397)
                    ·
                      refine ⟨3839519244713366227049399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238717985902309938798397 3839519244713366227049399)
                      ·
                        rfl

theorem cell23_7477437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_7477437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477437 prefixEnd_7477437 := by exact prefixLift 7477437
  have htrace : WordTrace (prefixWord ++ tailWord_7477437) baseStart_7477437 baseEnd_7477437 := by
    simpa [prefixWord, tailWord_7477437, baseEnd_7477437] using wordTrace_append hprefix tailTrace_7477437
  have hstable : (prefixWord ++ tailWord_7477437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477437).length < 2 ^ (prefixWord ++ tailWord_7477437).sum := by decide
  have hdescent : baseEnd_7477437 < baseStart_7477437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477444 : List Nat := [2, 3, 3, 1, 2, 3, 1, 8]
def baseStart_7477444 : Nat := 118140960795 + 7477444 * 2 ^ 59
def prefixEnd_7477444 : Nat := 4983230072969 + 3 ^ 40 * 7477444 * 2
def baseEnd_7477444 : Nat := 142204549595479544431921

theorem tailTrace_7477444 : CollatzResearch.WordTrace tailWord_7477444 prefixEnd_7477444 142204549595479544431921 := by
  unfold tailWord_7477444
  simp only [CollatzResearch.WordTrace]
  refine ⟨136362393961252454304751693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181816525281669939073002257 136362393961252454304751693)
  ·
    refine ⟨51135897735469670364281885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136362393961252454304751693 51135897735469670364281885)
    ·
      refine ⟨19175961650801126386605707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51135897735469670364281885 19175961650801126386605707)
      ·
        refine ⟨28763942476201689579908561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19175961650801126386605707 28763942476201689579908561)
        ·
          refine ⟨21572956857151267184931421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28763942476201689579908561 21572956857151267184931421)
          ·
            refine ⟨8089858821431725194349283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21572956857151267184931421 8089858821431725194349283)
            ·
              refine ⟨12134788232147587791523925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089858821431725194349283 12134788232147587791523925)
              ·
                refine ⟨142204549595479544431921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12134788232147587791523925 142204549595479544431921)
                ·
                  rfl

theorem cell23_7477444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 8].length) (baseStart_7477444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477444 prefixEnd_7477444 := by exact prefixLift 7477444
  have htrace : WordTrace (prefixWord ++ tailWord_7477444) baseStart_7477444 baseEnd_7477444 := by
    simpa [prefixWord, tailWord_7477444, baseEnd_7477444] using wordTrace_append hprefix tailTrace_7477444
  have hstable : (prefixWord ++ tailWord_7477444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477444).length < 2 ^ (prefixWord ++ tailWord_7477444).sum := by decide
  have hdescent : baseEnd_7477444 < baseStart_7477444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477454 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_7477454 : Nat := 118140960795 + 7477454 * 2 ^ 59
def prefixEnd_7477454 : Nat := 4983230072969 + 3 ^ 40 * 7477454 * 2
def baseEnd_7477454 : Nat := 3839527973884492660536821

theorem tailTrace_7477454 : CollatzResearch.WordTrace tailWord_7477454 prefixEnd_7477454 3839527973884492660536821 := by
  unfold tailWord_7477454
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090644081558585039670927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181816768434979120211578277 34090644081558585039670927)
  ·
    refine ⟨51135966122337877559506391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34090644081558585039670927 51135966122337877559506391)
    ·
      refine ⟨76703949183506816339259587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51135966122337877559506391 76703949183506816339259587)
      ·
        refine ⟨115055923775260224508889381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76703949183506816339259587 115055923775260224508889381)
        ·
          refine ⟨21572985707861292095416759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115055923775260224508889381 21572985707861292095416759)
          ·
            refine ⟨32359478561791938143125139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21572985707861292095416759 32359478561791938143125139)
            ·
              refine ⟨48539217842687907214687709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32359478561791938143125139 48539217842687907214687709)
              ·
                refine ⟨18202206691007965205507891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48539217842687907214687709 18202206691007965205507891)
                ·
                  refine ⟨27303310036511947808261837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18202206691007965205507891 27303310036511947808261837)
                  ·
                    refine ⟨10238741263691980428098189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27303310036511947808261837 10238741263691980428098189)
                    ·
                      refine ⟨3839527973884492660536821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238741263691980428098189 3839527973884492660536821)
                      ·
                        rfl

theorem cell23_7477454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_7477454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477454 prefixEnd_7477454 := by exact prefixLift 7477454
  have htrace : WordTrace (prefixWord ++ tailWord_7477454) baseStart_7477454 baseEnd_7477454 := by
    simpa [prefixWord, tailWord_7477454, baseEnd_7477454] using wordTrace_append hprefix tailTrace_7477454
  have hstable : (prefixWord ++ tailWord_7477454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477454).length < 2 ^ (prefixWord ++ tailWord_7477454).sum := by decide
  have hdescent : baseEnd_7477454 < baseStart_7477454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477475 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7477475 : Nat := 118140960795 + 7477475 * 2 ^ 59
def prefixEnd_7477475 : Nat := 4983230072969 + 3 ^ 40 * 7477475 * 2
def baseEnd_7477475 : Nat := 3839538756978237078374225

theorem tailTrace_7477475 : CollatzResearch.WordTrace tailWord_7477475 prefixEnd_7477475 3839538756978237078374225 := by
  unfold tailWord_7477475
  simp only [CollatzResearch.WordTrace]
  refine ⟨272725918585392600903881879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181817279056928400602587919 272725918585392600903881879)
  ·
    refine ⟨409088877878088901355822819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272725918585392600903881879 409088877878088901355822819)
    ·
      refine ⟨613633316817133352033734229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409088877878088901355822819 613633316817133352033734229)
      ·
        refine ⟨7191015431450781469145323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 613633316817133352033734229 7191015431450781469145323)
        ·
          refine ⟨10786523147176172203717985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191015431450781469145323 10786523147176172203717985)
          ·
            refine ⟨8089892360382129152788489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786523147176172203717985 8089892360382129152788489)
            ·
              refine ⟨6067419270286596864591367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8089892360382129152788489 6067419270286596864591367)
              ·
                refine ⟨9101128905429895296887051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067419270286596864591367 9101128905429895296887051)
                ·
                  refine ⟨13651693358144842945330577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101128905429895296887051 13651693358144842945330577)
                  ·
                    refine ⟨10238770018608632208997933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13651693358144842945330577 10238770018608632208997933)
                    ·
                      refine ⟨3839538756978237078374225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238770018608632208997933 3839538756978237078374225)
                      ·
                        rfl

theorem cell23_7477475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7477475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477475 prefixEnd_7477475 := by exact prefixLift 7477475
  have htrace : WordTrace (prefixWord ++ tailWord_7477475) baseStart_7477475 baseEnd_7477475 := by
    simpa [prefixWord, tailWord_7477475, baseEnd_7477475] using wordTrace_append hprefix tailTrace_7477475
  have hstable : (prefixWord ++ tailWord_7477475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477475).length < 2 ^ (prefixWord ++ tailWord_7477475).sum := by decide
  have hdescent : baseEnd_7477475 < baseStart_7477475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477487 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 2, 6]
def baseStart_7477487 : Nat := 118140960795 + 7477487 * 2 ^ 59
def prefixEnd_7477487 : Nat := 4983230072969 + 3 ^ 40 * 7477487 * 2
def baseEnd_7477487 : Nat := 1279848306248697010474723

theorem tailTrace_7477487 : CollatzResearch.WordTrace tailWord_7477487 prefixEnd_7477487 1279848306248697010474723 := by
  unfold tailWord_7477487
  simp only [CollatzResearch.WordTrace]
  refine ⟨272726356261349126953318715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181817570840899417968879143 272726356261349126953318715)
  ·
    refine ⟨409089534392023690429978073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272726356261349126953318715 409089534392023690429978073)
    ·
      refine ⟨306817150794017767822483555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409089534392023690429978073 306817150794017767822483555)
      ·
        refine ⟨460225726191026651733725333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306817150794017767822483555 460225726191026651733725333)
        ·
          refine ⟨21573080915204374300018375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 460225726191026651733725333 21573080915204374300018375)
          ·
            refine ⟨32359621372806561450027563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21573080915204374300018375 32359621372806561450027563)
            ·
              refine ⟨48539432059209842175041345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32359621372806561450027563 48539432059209842175041345)
              ·
                refine ⟨36404574044407381631281009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48539432059209842175041345 36404574044407381631281009)
                ·
                  refine ⟨27303430533305536223460757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36404574044407381631281009 27303430533305536223460757)
                  ·
                    refine ⟨1279848306248697010474723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27303430533305536223460757 1279848306248697010474723)
                    ·
                      rfl

theorem cell23_7477487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_7477487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477487 prefixEnd_7477487 := by exact prefixLift 7477487
  have htrace : WordTrace (prefixWord ++ tailWord_7477487) baseStart_7477487 baseEnd_7477487 := by
    simpa [prefixWord, tailWord_7477487, baseEnd_7477487] using wordTrace_append hprefix tailTrace_7477487
  have hstable : (prefixWord ++ tailWord_7477487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477487).length < 2 ^ (prefixWord ++ tailWord_7477487).sum := by decide
  have hdescent : baseEnd_7477487 < baseStart_7477487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477497 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_7477497 : Nat := 118140960795 + 7477497 * 2 ^ 59
def prefixEnd_7477497 : Nat := 4983230072969 + 3 ^ 40 * 7477497 * 2
def baseEnd_7477497 : Nat := 3839550053552635992299123

theorem tailTrace_7477497 : CollatzResearch.WordTrace tailWord_7477497 prefixEnd_7477497 3839550053552635992299123 := by
  unfold tailWord_7477497
  simp only [CollatzResearch.WordTrace]
  refine ⟨272726720991312898661182745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181817813994208599107455163 272726720991312898661182745)
  ·
    refine ⟨204545040743484673995887059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272726720991312898661182745 204545040743484673995887059)
    ·
      refine ⟨306817561115227010993830589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204545040743484673995887059 306817561115227010993830589)
      ·
        refine ⟨115056585418210129122686471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306817561115227010993830589 115056585418210129122686471)
        ·
          refine ⟨172584878127315193684029707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115056585418210129122686471 172584878127315193684029707)
          ·
            refine ⟨258877317190972790526044561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172584878127315193684029707 258877317190972790526044561)
            ·
              refine ⟨194157987893229592894533421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258877317190972790526044561 194157987893229592894533421)
              ·
                refine ⟨72809245459961097335450033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194157987893229592894533421 72809245459961097335450033)
                ·
                  refine ⟨54606934094970823001587525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72809245459961097335450033 54606934094970823001587525)
                  ·
                    refine ⟨10238800142807029312797661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54606934094970823001587525 10238800142807029312797661)
                    ·
                      refine ⟨3839550053552635992299123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10238800142807029312797661 3839550053552635992299123)
                      ·
                        rfl

theorem cell23_7477497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_7477497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477497 prefixEnd_7477497 := by exact prefixLift 7477497
  have htrace : WordTrace (prefixWord ++ tailWord_7477497) baseStart_7477497 baseEnd_7477497 := by
    simpa [prefixWord, tailWord_7477497, baseEnd_7477497] using wordTrace_append hprefix tailTrace_7477497
  have hstable : (prefixWord ++ tailWord_7477497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477497).length < 2 ^ (prefixWord ++ tailWord_7477497).sum := by decide
  have hdescent : baseEnd_7477497 < baseStart_7477497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477507 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_7477507 : Nat := 118140960795 + 7477507 * 2 ^ 59
def prefixEnd_7477507 : Nat := 4983230072969 + 3 ^ 40 * 7477507 * 2
def baseEnd_7477507 : Nat := 3839555188359180953174077

theorem tailTrace_7477507 : CollatzResearch.WordTrace tailWord_7477507 prefixEnd_7477507 3839555188359180953174077 := by
  unfold tailWord_7477507
  simp only [CollatzResearch.WordTrace]
  refine ⟨272727085721276670369046775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181818057147517780246031183 272727085721276670369046775)
  ·
    refine ⟨409090628581915005553570163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272727085721276670369046775 409090628581915005553570163)
    ·
      refine ⟨613635942872872508330355245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409090628581915005553570163 613635942872872508330355245)
      ·
        refine ⟨230113478577327190623883217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613635942872872508330355245 230113478577327190623883217)
        ·
          refine ⟨172585108932995392967912413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230113478577327190623883217 172585108932995392967912413)
          ·
            refine ⟨64719415849873272362967155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172585108932995392967912413 64719415849873272362967155)
            ·
              refine ⟨97079123774809908544450733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64719415849873272362967155 97079123774809908544450733)
              ·
                refine ⟨36404671415553715704169025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97079123774809908544450733 36404671415553715704169025)
                ·
                  refine ⟨27303503561665286778126769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36404671415553715704169025 27303503561665286778126769)
                  ·
                    refine ⟨20477627671248965083595077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27303503561665286778126769 20477627671248965083595077)
                    ·
                      refine ⟨3839555188359180953174077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20477627671248965083595077 3839555188359180953174077)
                      ·
                        rfl

theorem cell23_7477507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_7477507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477507 prefixEnd_7477507 := by exact prefixLift 7477507
  have htrace : WordTrace (prefixWord ++ tailWord_7477507) baseStart_7477507 baseEnd_7477507 := by
    simpa [prefixWord, tailWord_7477507, baseEnd_7477507] using wordTrace_append hprefix tailTrace_7477507
  have hstable : (prefixWord ++ tailWord_7477507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477507).length < 2 ^ (prefixWord ++ tailWord_7477507).sum := by decide
  have hdescent : baseEnd_7477507 < baseStart_7477507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477584 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_7477584 : Nat := 118140960795 + 7477584 * 2 ^ 59
def prefixEnd_7477584 : Nat := 4983230072969 + 3 ^ 40 * 7477584 * 2
def baseEnd_7477584 : Nat := 3839594726369577151911223

theorem tailTrace_7477584 : CollatzResearch.WordTrace tailWord_7477584 prefixEnd_7477584 3839594726369577151911223 := by
  unfold tailWord_7477584
  simp only [CollatzResearch.WordTrace]
  refine ⟨136364947070998856259799903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181819929427998475013066537 136364947070998856259799903)
  ·
    refine ⟨204547420606498284389699855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136364947070998856259799903 204547420606498284389699855)
    ·
      refine ⟨306821130909747426584549783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204547420606498284389699855 306821130909747426584549783)
      ·
        refine ⟨460231696364621139876824675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306821130909747426584549783 460231696364621139876824675)
        ·
          refine ⟨690347544546931709815237013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460231696364621139876824675 690347544546931709815237013)
          ·
            refine ⟨32360041150637423897589235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 690347544546931709815237013 32360041150637423897589235)
            ·
              refine ⟨48540061725956135846383853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32360041150637423897589235 48540061725956135846383853)
              ·
                refine ⟨18202523147233550942393945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48540061725956135846383853 18202523147233550942393945)
                ·
                  refine ⟨13651892360425163206795459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18202523147233550942393945 13651892360425163206795459)
                  ·
                    refine ⟨20477838540637744810193189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13651892360425163206795459 20477838540637744810193189)
                    ·
                      refine ⟨3839594726369577151911223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20477838540637744810193189 3839594726369577151911223)
                      ·
                        rfl

theorem cell23_7477584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_7477584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477584 prefixEnd_7477584 := by exact prefixLift 7477584
  have htrace : WordTrace (prefixWord ++ tailWord_7477584) baseStart_7477584 baseEnd_7477584 := by
    simpa [prefixWord, tailWord_7477584, baseEnd_7477584] using wordTrace_append hprefix tailTrace_7477584
  have hstable : (prefixWord ++ tailWord_7477584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477584).length < 2 ^ (prefixWord ++ tailWord_7477584).sum := by decide
  have hdescent : baseEnd_7477584 < baseStart_7477584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477611 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 1, 4]
def baseStart_7477611 : Nat := 118140960795 + 7477611 * 2 ^ 59
def prefixEnd_7477611 : Nat := 4983230072969 + 3 ^ 40 * 7477611 * 2
def baseEnd_7477611 : Nat := 1279869530115749515424533

theorem tailTrace_7477611 : CollatzResearch.WordTrace tailWord_7477611 prefixEnd_7477611 1279869530115749515424533 := by
  unfold tailWord_7477611
  simp only [CollatzResearch.WordTrace]
  refine ⟨272730878912899896130832687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181820585941933264087221791 272730878912899896130832687)
  ·
    refine ⟨409096318369349844196249031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272730878912899896130832687 409096318369349844196249031)
    ·
      refine ⟨613644477554024766294373547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409096318369349844196249031 613644477554024766294373547)
      ·
        refine ⟨920466716331037149441560321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613644477554024766294373547 920466716331037149441560321)
        ·
          refine ⟨690350037248277862081170241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920466716331037149441560321 690350037248277862081170241)
          ·
            refine ⟨517762527936208396560877681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690350037248277862081170241 517762527936208396560877681)
            ·
              refine ⟨388321895952156297420658261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517762527936208396560877681 388321895952156297420658261)
              ·
                refine ⟨4550647218189331610398339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 388321895952156297420658261 4550647218189331610398339)
                ·
                  refine ⟨6825970827283997415597509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550647218189331610398339 6825970827283997415597509)
                  ·
                    refine ⟨1279869530115749515424533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825970827283997415597509 1279869530115749515424533)
                    ·
                      rfl

theorem cell23_7477611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 1, 4].length) (baseStart_7477611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477611 prefixEnd_7477611 := by exact prefixLift 7477611
  have htrace : WordTrace (prefixWord ++ tailWord_7477611) baseStart_7477611 baseEnd_7477611 := by
    simpa [prefixWord, tailWord_7477611, baseEnd_7477611] using wordTrace_append hprefix tailTrace_7477611
  have hstable : (prefixWord ++ tailWord_7477611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477611).length < 2 ^ (prefixWord ++ tailWord_7477611).sum := by decide
  have hdescent : baseEnd_7477611 < baseStart_7477611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477718 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7477718 : Nat := 118140960795 + 7477718 * 2 ^ 59
def prefixEnd_7477718 : Nat := 4983230072969 + 3 ^ 40 * 7477718 * 2
def baseEnd_7477718 : Nat := 1279887844259093209211869

theorem tailTrace_7477718 : CollatzResearch.WordTrace tailWord_7477718 prefixEnd_7477718 1279887844259093209211869 := by
  unfold tailWord_7477718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17045923845219515837811113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181823187682341502269985205 17045923845219515837811113)
  ·
    refine ⟨12784442883914636878358335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17045923845219515837811113 12784442883914636878358335)
    ·
      refine ⟨19176664325871955317537503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784442883914636878358335 19176664325871955317537503)
      ·
        refine ⟨28764996488807932976306255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176664325871955317537503 28764996488807932976306255)
        ·
          refine ⟨43147494733211899464459383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28764996488807932976306255 43147494733211899464459383)
          ·
            refine ⟨64721242099817849196689075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43147494733211899464459383 64721242099817849196689075)
            ·
              refine ⟨97081863149726773795033613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64721242099817849196689075 97081863149726773795033613)
              ·
                refine ⟨36405698681147540173137605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97081863149726773795033613 36405698681147540173137605)
                ·
                  refine ⟨6826068502715163782463301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36405698681147540173137605 6826068502715163782463301)
                  ·
                    refine ⟨1279887844259093209211869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6826068502715163782463301 1279887844259093209211869)
                    ·
                      rfl

theorem cell23_7477718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7477718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477718 prefixEnd_7477718 := by exact prefixLift 7477718
  have htrace : WordTrace (prefixWord ++ tailWord_7477718) baseStart_7477718 baseEnd_7477718 := by
    simpa [prefixWord, tailWord_7477718, baseEnd_7477718] using wordTrace_append hprefix tailTrace_7477718
  have hstable : (prefixWord ++ tailWord_7477718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477718).length < 2 ^ (prefixWord ++ tailWord_7477718).sum := by decide
  have hdescent : baseEnd_7477718 < baseStart_7477718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477731 : List Nat := [1, 1, 1, 6, 3, 1, 2, 8]
def baseStart_7477731 : Nat := 118140960795 + 7477731 * 2 ^ 59
def prefixEnd_7477731 : Nat := 4983230072969 + 3 ^ 40 * 7477731 * 2
def baseEnd_7477731 : Nat := 142210007704658817658261

theorem tailTrace_7477731 : CollatzResearch.WordTrace tailWord_7477731 prefixEnd_7477731 142210007704658817658261 := by
  unfold tailWord_7477731
  simp only [CollatzResearch.WordTrace]
  refine ⟨272735255672465156625201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181823503781643437750134031 272735255672465156625201047)
  ·
    refine ⟨409102883508697734937801571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272735255672465156625201047 409102883508697734937801571)
    ·
      refine ⟨613654325263046602406702357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409102883508697734937801571 613654325263046602406702357)
      ·
        refine ⟨28765046496705309487814173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 613654325263046602406702357 28765046496705309487814173)
        ·
          refine ⟨10786892436264491057930315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28765046496705309487814173 10786892436264491057930315)
          ·
            refine ⟨16180338654396736586895473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10786892436264491057930315 16180338654396736586895473)
            ·
              refine ⟨12135253990797552440171605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16180338654396736586895473 12135253990797552440171605)
              ·
                refine ⟨142210007704658817658261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12135253990797552440171605 142210007704658817658261)
                ·
                  rfl

theorem cell23_7477731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 8].length) (baseStart_7477731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477731 prefixEnd_7477731 := by exact prefixLift 7477731
  have htrace : WordTrace (prefixWord ++ tailWord_7477731) baseStart_7477731 baseEnd_7477731 := by
    simpa [prefixWord, tailWord_7477731, baseEnd_7477731] using wordTrace_append hprefix tailTrace_7477731
  have hstable : (prefixWord ++ tailWord_7477731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477731).length < 2 ^ (prefixWord ++ tailWord_7477731).sum := by decide
  have hdescent : baseEnd_7477731 < baseStart_7477731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477754 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_7477754 : Nat := 118140960795 + 7477754 * 2 ^ 59
def prefixEnd_7477754 : Nat := 4983230072969 + 3 ^ 40 * 7477754 * 2
def baseEnd_7477754 : Nat := 3839682018080841486785441

theorem tailTrace_7477754 : CollatzResearch.WordTrace tailWord_7477754 prefixEnd_7477754 3839682018080841486785441 := by
  unfold tailWord_7477754
  simp only [CollatzResearch.WordTrace]
  refine ⟨68184023637845457888322079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181824063034254554368858877 68184023637845457888322079)
  ·
    refine ⟨102276035456768186832483119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68184023637845457888322079 102276035456768186832483119)
    ·
      refine ⟨153414053185152280248724679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102276035456768186832483119 153414053185152280248724679)
      ·
        refine ⟨230121079777728420373087019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153414053185152280248724679 230121079777728420373087019)
        ·
          refine ⟨345181619666592630559630529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230121079777728420373087019 345181619666592630559630529)
          ·
            refine ⟨258886214749944472919722897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345181619666592630559630529 258886214749944472919722897)
            ·
              refine ⟨194164661062458354689792173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258886214749944472919722897 194164661062458354689792173)
              ·
                refine ⟨72811747898421883008672065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194164661062458354689792173 72811747898421883008672065)
                ·
                  refine ⟨54608810923816412256504049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72811747898421883008672065 54608810923816412256504049)
                  ·
                    refine ⟨40956608192862309192378037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54608810923816412256504049 40956608192862309192378037)
                    ·
                      refine ⟨3839682018080841486785441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40956608192862309192378037 3839682018080841486785441)
                      ·
                        rfl

theorem cell23_7477754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_7477754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477754 prefixEnd_7477754 := by exact prefixLift 7477754
  have htrace : WordTrace (prefixWord ++ tailWord_7477754) baseStart_7477754 baseEnd_7477754 := by
    simpa [prefixWord, tailWord_7477754, baseEnd_7477754] using wordTrace_append hprefix tailTrace_7477754
  have hstable : (prefixWord ++ tailWord_7477754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477754).length < 2 ^ (prefixWord ++ tailWord_7477754).sum := by decide
  have hdescent : baseEnd_7477754 < baseStart_7477754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477762 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7477762 : Nat := 118140960795 + 7477762 * 2 ^ 59
def prefixEnd_7477762 : Nat := 4983230072969 + 3 ^ 40 * 7477762 * 2
def baseEnd_7477762 : Nat := 3839686125926077455485405

theorem tailTrace_7477762 : CollatzResearch.WordTrace tailWord_7477762 prefixEnd_7477762 3839686125926077455485405 := by
  unfold tailWord_7477762
  simp only [CollatzResearch.WordTrace]
  refine ⟨68184096583838212229894885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181824257556901899279719693 68184096583838212229894885)
  ·
    refine ⟨12784518109469664793105291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68184096583838212229894885 12784518109469664793105291)
    ·
      refine ⟨19176777164204497189657937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784518109469664793105291 19176777164204497189657937)
      ·
        refine ⟨14382582873153372892243453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19176777164204497189657937 14382582873153372892243453)
        ·
          refine ⟨5393468577432514834591295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14382582873153372892243453 5393468577432514834591295)
          ·
            refine ⟨8090202866148772251886943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393468577432514834591295 8090202866148772251886943)
            ·
              refine ⟨12135304299223158377830415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090202866148772251886943 12135304299223158377830415)
              ·
                refine ⟨18202956448834737566745623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12135304299223158377830415 18202956448834737566745623)
                ·
                  refine ⟨27304434673252106350118435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18202956448834737566745623 27304434673252106350118435)
                  ·
                    refine ⟨40956652009878159525177653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27304434673252106350118435 40956652009878159525177653)
                    ·
                      refine ⟨3839686125926077455485405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40956652009878159525177653 3839686125926077455485405)
                      ·
                        rfl

theorem cell23_7477762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7477762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477762 prefixEnd_7477762 := by exact prefixLift 7477762
  have htrace : WordTrace (prefixWord ++ tailWord_7477762) baseStart_7477762 baseEnd_7477762 := by
    simpa [prefixWord, tailWord_7477762, baseEnd_7477762] using wordTrace_append hprefix tailTrace_7477762
  have hstable : (prefixWord ++ tailWord_7477762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477762).length < 2 ^ (prefixWord ++ tailWord_7477762).sum := by decide
  have hdescent : baseEnd_7477762 < baseStart_7477762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477838 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_7477838 : Nat := 118140960795 + 7477838 * 2 ^ 59
def prefixEnd_7477838 : Nat := 4983230072969 + 3 ^ 40 * 7477838 * 2
def baseEnd_7477838 : Nat := 426636127828424350903895

theorem tailTrace_7477838 : CollatzResearch.WordTrace tailWord_7477838 prefixEnd_7477838 426636127828424350903895 := by
  unfold tailWord_7477838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34092394785384689237418271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181826105522051675932897445 34092394785384689237418271)
  ·
    refine ⟨51138592178077033856127407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34092394785384689237418271 51138592178077033856127407)
    ·
      refine ⟨76707888267115550784191111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51138592178077033856127407 76707888267115550784191111)
      ·
        refine ⟨115061832400673326176286667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76707888267115550784191111 115061832400673326176286667)
        ·
          refine ⟨172592748601009989264430001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115061832400673326176286667 172592748601009989264430001)
          ·
            refine ⟨129444561450757491948322501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172592748601009989264430001 129444561450757491948322501)
            ·
              refine ⟨24270855272017029740310469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129444561450757491948322501 24270855272017029740310469)
              ·
                refine ⟨4550785363503193076308213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24270855272017029740310469 4550785363503193076308213)
                ·
                  refine ⟨426636127828424350903895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550785363503193076308213 426636127828424350903895)
                  ·
                    rfl

theorem cell23_7477838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_7477838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477838 prefixEnd_7477838 := by exact prefixLift 7477838
  have htrace : WordTrace (prefixWord ++ tailWord_7477838) baseStart_7477838 baseEnd_7477838 := by
    simpa [prefixWord, tailWord_7477838, baseEnd_7477838] using wordTrace_append hprefix tailTrace_7477838
  have hstable : (prefixWord ++ tailWord_7477838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477838).length < 2 ^ (prefixWord ++ tailWord_7477838).sum := by decide
  have hdescent : baseEnd_7477838 < baseStart_7477838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477871 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_7477871 : Nat := 118140960795 + 7477871 * 2 ^ 59
def prefixEnd_7477871 : Nat := 4983230072969 + 3 ^ 40 * 7477871 * 2
def baseEnd_7477871 : Nat := 3839742095317417529022403

theorem tailTrace_7477871 : CollatzResearch.WordTrace tailWord_7477871 prefixEnd_7477871 3839742095317417529022403 := by
  unfold tailWord_7477871
  simp only [CollatzResearch.WordTrace]
  refine ⟨272740361891957960535297467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181826907927971973690198311 272740361891957960535297467)
  ·
    refine ⟨409110542837936940802946201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272740361891957960535297467 409110542837936940802946201)
    ·
      refine ⟨306832907128452705602209651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409110542837936940802946201 306832907128452705602209651)
      ·
        refine ⟨460249360692679058403314477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306832907128452705602209651 460249360692679058403314477)
        ·
          refine ⟨172593510259754646901242929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460249360692679058403314477 172593510259754646901242929)
          ·
            refine ⟨129445132694815985175932197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172593510259754646901242929 129445132694815985175932197)
            ·
              refine ⟨24270962380277997220487287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129445132694815985175932197 24270962380277997220487287)
              ·
                refine ⟨36406443570416995830730931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24270962380277997220487287 36406443570416995830730931)
                ·
                  refine ⟨54609665355625493746096397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36406443570416995830730931 54609665355625493746096397)
                  ·
                    refine ⟨20478624508359560154786149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54609665355625493746096397 20478624508359560154786149)
                    ·
                      refine ⟨3839742095317417529022403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20478624508359560154786149 3839742095317417529022403)
                      ·
                        rfl

theorem cell23_7477871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_7477871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477871 prefixEnd_7477871 := by exact prefixLift 7477871
  have htrace : WordTrace (prefixWord ++ tailWord_7477871) baseStart_7477871 baseEnd_7477871 := by
    simpa [prefixWord, tailWord_7477871, baseEnd_7477871] using wordTrace_append hprefix tailTrace_7477871
  have hstable : (prefixWord ++ tailWord_7477871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477871).length < 2 ^ (prefixWord ++ tailWord_7477871).sum := by decide
  have hdescent : baseEnd_7477871 < baseStart_7477871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477872 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 5]
def baseStart_7477872 : Nat := 118140960795 + 7477872 * 2 ^ 59
def prefixEnd_7477872 : Nat := 4983230072969 + 3 ^ 40 * 7477872 * 2
def baseEnd_7477872 : Nat := 426638067644230225012211

theorem tailTrace_7477872 : CollatzResearch.WordTrace tailWord_7477872 prefixEnd_7477872 426638067644230225012211 := by
  unfold tailWord_7477872
  simp only [CollatzResearch.WordTrace]
  refine ⟨136370199182477168853041935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181826932243302891804055913 136370199182477168853041935)
  ·
    refine ⟨204555298773715753279562903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136370199182477168853041935 204555298773715753279562903)
    ·
      refine ⟨306832948160573629919344355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204555298773715753279562903 306832948160573629919344355)
      ·
        refine ⟨460249422240860444879016533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306832948160573629919344355 460249422240860444879016533)
        ·
          refine ⟨5393547916885083338425975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 460249422240860444879016533 5393547916885083338425975)
          ·
            refine ⟨8090321875327625007638963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393547916885083338425975 8090321875327625007638963)
            ·
              refine ⟨12135482812991437511458445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090321875327625007638963 12135482812991437511458445)
              ·
                refine ⟨4550806054871789066796917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12135482812991437511458445 4550806054871789066796917)
                ·
                  refine ⟨426638067644230225012211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550806054871789066796917 426638067644230225012211)
                  ·
                    rfl

theorem cell23_7477872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 5].length) (baseStart_7477872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477872 prefixEnd_7477872 := by exact prefixLift 7477872
  have htrace : WordTrace (prefixWord ++ tailWord_7477872) baseStart_7477872 baseEnd_7477872 := by
    simpa [prefixWord, tailWord_7477872, baseEnd_7477872] using wordTrace_append hprefix tailTrace_7477872
  have hstable : (prefixWord ++ tailWord_7477872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477872).length < 2 ^ (prefixWord ++ tailWord_7477872).sum := by decide
  have hdescent : baseEnd_7477872 < baseStart_7477872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477888 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_7477888 : Nat := 118140960795 + 7477888 * 2 ^ 59
def prefixEnd_7477888 : Nat := 4983230072969 + 3 ^ 40 * 7477888 * 2
def baseEnd_7477888 : Nat := 3839750824488543962509825

theorem tailTrace_7477888 : CollatzResearch.WordTrace tailWord_7477888 prefixEnd_7477888 3839750824488543962509825 := by
  unfold tailWord_7477888
  simp only [CollatzResearch.WordTrace]
  refine ⟨136370490966448186219333159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181827321288597581625777545 136370490966448186219333159)
  ·
    refine ⟨204555736449672279328999739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136370490966448186219333159 204555736449672279328999739)
    ·
      refine ⟨306833604674508418993499609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204555736449672279328999739 306833604674508418993499609)
      ·
        refine ⟨230125203505881314245124707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306833604674508418993499609 230125203505881314245124707)
        ·
          refine ⟨345187805258821971367687061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230125203505881314245124707 345187805258821971367687061)
          ·
            refine ⟨16180678371507279907860331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 345187805258821971367687061 16180678371507279907860331)
            ·
              refine ⟨24271017557260919861790497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16180678371507279907860331 24271017557260919861790497)
              ·
                refine ⟨18203263167945689896342873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24271017557260919861790497 18203263167945689896342873)
                ·
                  refine ⟨13652447375959267422257155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18203263167945689896342873 13652447375959267422257155)
                  ·
                    refine ⟨20478671063938901133385733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13652447375959267422257155 20478671063938901133385733)
                    ·
                      refine ⟨3839750824488543962509825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20478671063938901133385733 3839750824488543962509825)
                      ·
                        rfl

theorem cell23_7477888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_7477888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477888 prefixEnd_7477888 := by exact prefixLift 7477888
  have htrace : WordTrace (prefixWord ++ tailWord_7477888) baseStart_7477888 baseEnd_7477888 := by
    simpa [prefixWord, tailWord_7477888, baseEnd_7477888] using wordTrace_append hprefix tailTrace_7477888
  have hstable : (prefixWord ++ tailWord_7477888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477888).length < 2 ^ (prefixWord ++ tailWord_7477888).sum := by decide
  have hdescent : baseEnd_7477888 < baseStart_7477888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477949 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_7477949 : Nat := 118140960795 + 7477949 * 2 ^ 59
def prefixEnd_7477949 : Nat := 4983230072969 + 3 ^ 40 * 7477949 * 2
def baseEnd_7477949 : Nat := 1279927382269489407949015

theorem tailTrace_7477949 : CollatzResearch.WordTrace tailWord_7477949 prefixEnd_7477949 1279927382269489407949015 := by
  unfold tailWord_7477949
  simp only [CollatzResearch.WordTrace]
  refine ⟨272743206785675379856636901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181828804523783586571091267 272743206785675379856636901)
  ·
    refine ⟨51139351272314133723119419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272743206785675379856636901 51139351272314133723119419)
    ·
      refine ⟨76709026908471200584679129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51139351272314133723119419 76709026908471200584679129)
      ·
        refine ⟨57531770181353400438509347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76709026908471200584679129 57531770181353400438509347)
        ·
          refine ⟨86297655272030100657764021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57531770181353400438509347 86297655272030100657764021)
          ·
            refine ⟨8090405181752821936665377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86297655272030100657764021 8090405181752821936665377)
            ·
              refine ⟨6067803886314616452499033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090405181752821936665377 6067803886314616452499033)
              ·
                refine ⟨4550852914735962339374275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6067803886314616452499033 4550852914735962339374275)
                ·
                  refine ⟨6826279372103943509061413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550852914735962339374275 6826279372103943509061413)
                  ·
                    refine ⟨1279927382269489407949015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6826279372103943509061413 1279927382269489407949015)
                    ·
                      rfl

theorem cell23_7477949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_7477949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477949 prefixEnd_7477949 := by exact prefixLift 7477949
  have htrace : WordTrace (prefixWord ++ tailWord_7477949) baseStart_7477949 baseEnd_7477949 := by
    simpa [prefixWord, tailWord_7477949, baseEnd_7477949] using wordTrace_append hprefix tailTrace_7477949
  have hstable : (prefixWord ++ tailWord_7477949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477949).length < 2 ^ (prefixWord ++ tailWord_7477949).sum := by decide
  have hdescent : baseEnd_7477949 < baseStart_7477949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477978 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_7477978 : Nat := 118140960795 + 7477978 * 2 ^ 59
def prefixEnd_7477978 : Nat := 4983230072969 + 3 ^ 40 * 7477978 * 2
def baseEnd_7477978 : Nat := 3839797037747448610384411

theorem tailTrace_7477978 : CollatzResearch.WordTrace tailWord_7477978 prefixEnd_7477978 3839797037747448610384411 := by
  unfold tailWord_7477978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68186066125642579452360647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181829509668380211872961725 68186066125642579452360647)
  ·
    refine ⟨102279099188463869178540971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68186066125642579452360647 102279099188463869178540971)
    ·
      refine ⟨153418648782695803767811457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102279099188463869178540971 153418648782695803767811457)
      ·
        refine ⟨115063986587021852825858593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153418648782695803767811457 115063986587021852825858593)
        ·
          refine ⟨86297989940266389619393945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115063986587021852825858593 86297989940266389619393945)
          ·
            refine ⟨64723492455199792214545459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86297989940266389619393945 64723492455199792214545459)
            ·
              refine ⟨97085238682799688321818189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64723492455199792214545459 97085238682799688321818189)
              ·
                refine ⟨36406964506049883120681821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97085238682799688321818189 36406964506049883120681821)
                ·
                  refine ⟨13652611689768706170255683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36406964506049883120681821 13652611689768706170255683)
                  ·
                    refine ⟨20478917534653059255383525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13652611689768706170255683 20478917534653059255383525)
                    ·
                      refine ⟨3839797037747448610384411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20478917534653059255383525 3839797037747448610384411)
                      ·
                        rfl

theorem cell23_7477978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_7477978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477978 prefixEnd_7477978 := by exact prefixLift 7477978
  have htrace : WordTrace (prefixWord ++ tailWord_7477978) baseStart_7477978 baseEnd_7477978 := by
    simpa [prefixWord, tailWord_7477978, baseEnd_7477978] using wordTrace_append hprefix tailTrace_7477978
  have hstable : (prefixWord ++ tailWord_7477978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477978).length < 2 ^ (prefixWord ++ tailWord_7477978).sum := by decide
  have hdescent : baseEnd_7477978 < baseStart_7477978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477988 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_7477988 : Nat := 118140960795 + 7477988 * 2 ^ 59
def prefixEnd_7477988 : Nat := 4983230072969 + 3 ^ 40 * 7477988 * 2
def baseEnd_7477988 : Nat := 1279934057517997857086455

theorem tailTrace_7477988 : CollatzResearch.WordTrace tailWord_7477988 prefixEnd_7477988 1279934057517997857086455 := by
  unfold tailWord_7477988
  simp only [CollatzResearch.WordTrace]
  refine ⟨136372314616267044758653309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181829752821689393011537745 136372314616267044758653309)
  ·
    refine ⟨51139617981100141784494991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136372314616267044758653309 51139617981100141784494991)
    ·
      refine ⟨76709426971650212676742487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51139617981100141784494991 76709426971650212676742487)
      ·
        refine ⟨115064140457475319015113731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76709426971650212676742487 115064140457475319015113731)
        ·
          refine ⟨172596210686212978522670597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115064140457475319015113731 172596210686212978522670597)
          ·
            refine ⟨32361789503664933473000737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172596210686212978522670597 32361789503664933473000737)
            ·
              refine ⟨24271342127748700104750553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32361789503664933473000737 24271342127748700104750553)
              ·
                refine ⟨18203506595811525078562915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24271342127748700104750553 18203506595811525078562915)
                ·
                  refine ⟨27305259893717287617844373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18203506595811525078562915 27305259893717287617844373)
                  ·
                    refine ⟨1279934057517997857086455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27305259893717287617844373 1279934057517997857086455)
                    ·
                      rfl

theorem cell23_7477988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_7477988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477988 prefixEnd_7477988 := by exact prefixLift 7477988
  have htrace : WordTrace (prefixWord ++ tailWord_7477988) baseStart_7477988 baseEnd_7477988 := by
    simpa [prefixWord, tailWord_7477988, baseEnd_7477988] using wordTrace_append hprefix tailTrace_7477988
  have hstable : (prefixWord ++ tailWord_7477988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477988).length < 2 ^ (prefixWord ++ tailWord_7477988).sum := by decide
  have hdescent : baseEnd_7477988 < baseStart_7477988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477989 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7477989 : Nat := 118140960795 + 7477989 * 2 ^ 59
def prefixEnd_7477989 : Nat := 4983230072969 + 3 ^ 40 * 7477989 * 2
def baseEnd_7477989 : Nat := 3839802686034648067346861

theorem tailTrace_7477989 : CollatzResearch.WordTrace tailWord_7477989 prefixEnd_7477989 3839802686034648067346861 := by
  unfold tailWord_7477989
  simp only [CollatzResearch.WordTrace]
  refine ⟨272744665705530466688093021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181829777137020311125395347 272744665705530466688093021)
  ·
    refine ⟨102279249639573925008034883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272744665705530466688093021 102279249639573925008034883)
    ·
      refine ⟨153418874459360887512052325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102279249639573925008034883 153418874459360887512052325)
      ·
        refine ⟨28766038961130166408509811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153418874459360887512052325 28766038961130166408509811)
        ·
          refine ⟨43149058441695249612764717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28766038961130166408509811 43149058441695249612764717)
          ·
            refine ⟨16180896915635718604786769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43149058441695249612764717 16180896915635718604786769)
            ·
              refine ⟨12135672686726788953590077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16180896915635718604786769 12135672686726788953590077)
              ·
                refine ⟨4550877257522545857596279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12135672686726788953590077 4550877257522545857596279)
                ·
                  refine ⟨6826315886283818786394419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550877257522545857596279 6826315886283818786394419)
                  ·
                    refine ⟨10239473829425728179591629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826315886283818786394419 10239473829425728179591629)
                    ·
                      refine ⟨3839802686034648067346861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10239473829425728179591629 3839802686034648067346861)
                      ·
                        rfl

theorem cell23_7477989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7477989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477989 prefixEnd_7477989 := by exact prefixLift 7477989
  have htrace : WordTrace (prefixWord ++ tailWord_7477989) baseStart_7477989 baseEnd_7477989 := by
    simpa [prefixWord, tailWord_7477989, baseEnd_7477989] using wordTrace_append hprefix tailTrace_7477989
  have hstable : (prefixWord ++ tailWord_7477989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477989).length < 2 ^ (prefixWord ++ tailWord_7477989).sum := by decide
  have hdescent : baseEnd_7477989 < baseStart_7477989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7477995 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 7, 2, 2]
def baseStart_7477995 : Nat := 118140960795 + 7477995 * 2 ^ 59
def prefixEnd_7477995 : Nat := 4983230072969 + 3 ^ 40 * 7477995 * 2
def baseEnd_7477995 : Nat := 3839805766918575043871833

theorem tailTrace_7477995 : CollatzResearch.WordTrace tailWord_7477995 prefixEnd_7477995 3839805766918575043871833 := by
  unfold tailWord_7477995
  simp only [CollatzResearch.WordTrace]
  refine ⟨272744884543508729712811439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181829923029005819808540959 272744884543508729712811439)
  ·
    refine ⟨409117326815263094569217159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272744884543508729712811439 409117326815263094569217159)
    ·
      refine ⟨613675990222894641853825739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409117326815263094569217159 613675990222894641853825739)
      ·
        refine ⟨920513985334341962780738609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613675990222894641853825739 920513985334341962780738609)
        ·
          refine ⟨690385489000756472085553957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920513985334341962780738609 690385489000756472085553957)
          ·
            refine ⟨129447279187641838516041367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 690385489000756472085553957 129447279187641838516041367)
            ·
              refine ⟨194170918781462757774062051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129447279187641838516041367 194170918781462757774062051)
              ·
                refine ⟨291256378172194136661093077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194170918781462757774062051 291256378172194136661093077)
                ·
                  refine ⟨6826321363410800077994369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 291256378172194136661093077 6826321363410800077994369)
                  ·
                    refine ⟨5119741022558100058495777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826321363410800077994369 5119741022558100058495777)
                    ·
                      refine ⟨3839805766918575043871833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119741022558100058495777 3839805766918575043871833)
                      ·
                        rfl

theorem cell23_7477995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2, 2].length) (baseStart_7477995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7477995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7477995 prefixEnd_7477995 := by exact prefixLift 7477995
  have htrace : WordTrace (prefixWord ++ tailWord_7477995) baseStart_7477995 baseEnd_7477995 := by
    simpa [prefixWord, tailWord_7477995, baseEnd_7477995] using wordTrace_append hprefix tailTrace_7477995
  have hstable : (prefixWord ++ tailWord_7477995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7477995).length < 2 ^ (prefixWord ++ tailWord_7477995).sum := by decide
  have hdescent : baseEnd_7477995 < baseStart_7477995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7477995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478001 : List Nat := [1, 2, 2, 2, 2, 2, 12]
def baseStart_7478001 : Nat := 118140960795 + 7478001 * 2 ^ 59
def prefixEnd_7478001 : Nat := 4983230072969 + 3 ^ 40 * 7478001 * 2
def baseEnd_7478001 : Nat := 47405047503734592844405

theorem tailTrace_7478001 : CollatzResearch.WordTrace tailWord_7478001 prefixEnd_7478001 47405047503734592844405 := by
  unfold tailWord_7478001
  simp only [CollatzResearch.WordTrace]
  refine ⟨272745103381486992737529857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181830068920991328491686571 272745103381486992737529857)
  ·
    refine ⟨204558827536115244553147393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272745103381486992737529857 204558827536115244553147393)
    ·
      refine ⟨153419120652086433414860545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204558827536115244553147393 153419120652086433414860545)
      ·
        refine ⟨115064340489064825061145409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153419120652086433414860545 115064340489064825061145409)
        ·
          refine ⟨86298255366798618795859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115064340489064825061145409 86298255366798618795859057)
          ·
            refine ⟨64723691525098964096894293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86298255366798618795859057 64723691525098964096894293)
            ·
              refine ⟨47405047503734592844405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 64723691525098964096894293 47405047503734592844405)
              ·
                rfl

theorem cell23_7478001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 12].length) (baseStart_7478001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478001 prefixEnd_7478001 := by exact prefixLift 7478001
  have htrace : WordTrace (prefixWord ++ tailWord_7478001) baseStart_7478001 baseEnd_7478001 := by
    simpa [prefixWord, tailWord_7478001, baseEnd_7478001] using wordTrace_append hprefix tailTrace_7478001
  have hstable : (prefixWord ++ tailWord_7478001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478001).length < 2 ^ (prefixWord ++ tailWord_7478001).sum := by decide
  have hdescent : baseEnd_7478001 < baseStart_7478001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478012 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_7478012 : Nat := 118140960795 + 7478012 * 2 ^ 59
def prefixEnd_7478012 : Nat := 4983230072969 + 3 ^ 40 * 7478012 * 2
def baseEnd_7478012 : Nat := 3839814496089701477359255

theorem tailTrace_7478012 : CollatzResearch.WordTrace tailWord_7478012 prefixEnd_7478012 3839814496089701477359255 := by
  unfold tailWord_7478012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136372752292223570808090145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181830336389631427744120193 136372752292223570808090145)
  ·
    refine ⟨102279564219167678106067609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136372752292223570808090145 102279564219167678106067609)
    ·
      refine ⟨76709673164375758579550707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102279564219167678106067609 76709673164375758579550707)
      ·
        refine ⟨115064509746563637869326061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76709673164375758579550707 115064509746563637869326061)
        ·
          refine ⟨43149191154961364200997273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115064509746563637869326061 43149191154961364200997273)
          ·
            refine ⟨32361893366221023150747955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43149191154961364200997273 32361893366221023150747955)
            ·
              refine ⟨48542840049331534726121933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32361893366221023150747955 48542840049331534726121933)
              ·
                refine ⟨18203565018499325522295725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48542840049331534726121933 18203565018499325522295725)
                ·
                  refine ⟨6826336881937247070860897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18203565018499325522295725 6826336881937247070860897)
                  ·
                    refine ⟨5119752661452935303145673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826336881937247070860897 5119752661452935303145673)
                    ·
                      refine ⟨3839814496089701477359255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119752661452935303145673 3839814496089701477359255)
                      ·
                        rfl

theorem cell23_7478012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_7478012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478012 prefixEnd_7478012 := by exact prefixLift 7478012
  have htrace : WordTrace (prefixWord ++ tailWord_7478012) baseStart_7478012 baseEnd_7478012 := by
    simpa [prefixWord, tailWord_7478012, baseEnd_7478012] using wordTrace_append hprefix tailTrace_7478012
  have hstable : (prefixWord ++ tailWord_7478012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478012).length < 2 ^ (prefixWord ++ tailWord_7478012).sum := by decide
  have hdescent : baseEnd_7478012 < baseStart_7478012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478079 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 2, 1, 3]
def baseStart_7478079 : Nat := 118140960795 + 7478079 * 2 ^ 59
def prefixEnd_7478079 : Nat := 4983230072969 + 3 ^ 40 * 7478079 * 2
def baseEnd_7478079 : Nat := 3839848899293552715221447

theorem tailTrace_7478079 : CollatzResearch.WordTrace tailWord_7478079 prefixEnd_7478079 3839848899293552715221447 := by
  unfold tailWord_7478079
  simp only [CollatzResearch.WordTrace]
  refine ⟨272747948275204412058869291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181831965516802941372579527 272747948275204412058869291)
  ·
    refine ⟨409121922412806618088303937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272747948275204412058869291 409121922412806618088303937)
    ·
      refine ⟨306841441809604963566227953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409121922412806618088303937 306841441809604963566227953)
      ·
        refine ⟨230131081357203722674670965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306841441809604963566227953 230131081357203722674670965)
        ·
          refine ⟨21574788877237849000750403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230131081357203722674670965 21574788877237849000750403)
          ·
            refine ⟨32362183315856773501125605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21574788877237849000750403 32362183315856773501125605)
            ·
              refine ⟨6067909371723145031461051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32362183315856773501125605 6067909371723145031461051)
              ·
                refine ⟨9101864057584717547191577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067909371723145031461051 9101864057584717547191577)
                ·
                  refine ⟨6826398043188538160393683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9101864057584717547191577 6826398043188538160393683)
                  ·
                    refine ⟨10239597064782807240590525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826398043188538160393683 10239597064782807240590525)
                    ·
                      refine ⟨3839848899293552715221447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10239597064782807240590525 3839848899293552715221447)
                      ·
                        rfl

theorem cell23_7478079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_7478079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478079 prefixEnd_7478079 := by exact prefixLift 7478079
  have htrace : WordTrace (prefixWord ++ tailWord_7478079) baseStart_7478079 baseEnd_7478079 := by
    simpa [prefixWord, tailWord_7478079, baseEnd_7478079] using wordTrace_append hprefix tailTrace_7478079
  have hstable : (prefixWord ++ tailWord_7478079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478079).length < 2 ^ (prefixWord ++ tailWord_7478079).sum := by decide
  have hdescent : baseEnd_7478079 < baseStart_7478079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478088 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_7478088 : Nat := 118140960795 + 7478088 * 2 ^ 59
def prefixEnd_7478088 : Nat := 4983230072969 + 3 ^ 40 * 7478088 * 2
def baseEnd_7478088 : Nat := 3839853520619443180008905

theorem tailTrace_7478088 : CollatzResearch.WordTrace tailWord_7478088 prefixEnd_7478088 3839853520619443180008905 := by
  unfold tailWord_7478088
  simp only [CollatzResearch.WordTrace]
  refine ⟨136374138266085903297973459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181832184354781204397297945 136374138266085903297973459)
  ·
    refine ⟨204561207399128854946960189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136374138266085903297973459 204561207399128854946960189)
    ·
      refine ⟨76710452774673320605110071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204561207399128854946960189 76710452774673320605110071)
      ·
        refine ⟨115065679162009980907665107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76710452774673320605110071 115065679162009980907665107)
        ·
          refine ⟨172598518743014971361497661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115065679162009980907665107 172598518743014971361497661)
          ·
            refine ⟨64724444528630614260561623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172598518743014971361497661 64724444528630614260561623)
            ·
              refine ⟨97086666792945921390842435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64724444528630614260561623 97086666792945921390842435)
              ·
                refine ⟨145630000189418882086263653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97086666792945921390842435 145630000189418882086263653)
                ·
                  refine ⟨27305625035516040391174435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145630000189418882086263653 27305625035516040391174435)
                  ·
                    refine ⟨40958437553274060586761653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27305625035516040391174435 40958437553274060586761653)
                    ·
                      refine ⟨3839853520619443180008905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40958437553274060586761653 3839853520619443180008905)
                      ·
                        rfl

theorem cell23_7478088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_7478088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478088 prefixEnd_7478088 := by exact prefixLift 7478088
  have htrace : WordTrace (prefixWord ++ tailWord_7478088) baseStart_7478088 baseEnd_7478088 := by
    simpa [prefixWord, tailWord_7478088, baseEnd_7478088] using wordTrace_append hprefix tailTrace_7478088
  have hstable : (prefixWord ++ tailWord_7478088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478088).length < 2 ^ (prefixWord ++ tailWord_7478088).sum := by decide
  have hdescent : baseEnd_7478088 < baseStart_7478088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478089 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 1, 3, 2]
def baseStart_7478089 : Nat := 118140960795 + 7478089 * 2 ^ 59
def prefixEnd_7478089 : Nat := 4983230072969 + 3 ^ 40 * 7478089 * 2
def baseEnd_7478089 : Nat := 3839854034100097676096401

theorem tailTrace_7478089 : CollatzResearch.WordTrace tailWord_7478089 prefixEnd_7478089 3839854034100097676096401 := by
  unfold tailWord_7478089
  simp only [CollatzResearch.WordTrace]
  refine ⟨272748313005168183766733321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181832208670112122511155547 272748313005168183766733321)
  ·
    refine ⟨204561234753876137825049991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272748313005168183766733321 204561234753876137825049991)
    ·
      refine ⟨306841852130814206737574987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204561234753876137825049991 306841852130814206737574987)
      ·
        refine ⟨460262778196221310106362481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306841852130814206737574987 460262778196221310106362481)
        ·
          refine ⟨345197083647165982579771861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460262778196221310106362481 345197083647165982579771861)
          ·
            refine ⟨8090556647980452716713403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 345197083647165982579771861 8090556647980452716713403)
            ·
              refine ⟨12135834971970679075070105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090556647980452716713403 12135834971970679075070105)
              ·
                refine ⟨9101876228978009306302579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12135834971970679075070105 9101876228978009306302579)
                ·
                  refine ⟨13652814343467013959453869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101876228978009306302579 13652814343467013959453869)
                  ·
                    refine ⟨5119805378800130234795201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13652814343467013959453869 5119805378800130234795201)
                    ·
                      refine ⟨3839854034100097676096401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119805378800130234795201 3839854034100097676096401)
                      ·
                        rfl

theorem cell23_7478089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3, 2].length) (baseStart_7478089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478089 prefixEnd_7478089 := by exact prefixLift 7478089
  have htrace : WordTrace (prefixWord ++ tailWord_7478089) baseStart_7478089 baseEnd_7478089 := by
    simpa [prefixWord, tailWord_7478089, baseEnd_7478089] using wordTrace_append hprefix tailTrace_7478089
  have hstable : (prefixWord ++ tailWord_7478089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478089).length < 2 ^ (prefixWord ++ tailWord_7478089).sum := by decide
  have hdescent : baseEnd_7478089 < baseStart_7478089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478119 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_7478119 : Nat := 118140960795 + 7478119 * 2 ^ 59
def prefixEnd_7478119 : Nat := 4983230072969 + 3 ^ 40 * 7478119 * 2
def baseEnd_7478119 : Nat := 3839869438519732558721263

theorem tailTrace_7478119 : CollatzResearch.WordTrace tailWord_7478119 prefixEnd_7478119 3839869438519732558721263 := by
  unfold tailWord_7478119
  simp only [CollatzResearch.WordTrace]
  refine ⟨272749407195059498890325411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181832938130039665926883607 272749407195059498890325411)
  ·
    refine ⟨409124110792589248335488117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272749407195059498890325411 409124110792589248335488117)
    ·
      refine ⟨38355385386805242031452011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409124110792589248335488117 38355385386805242031452011)
      ·
        refine ⟨57533078080207863047178017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38355385386805242031452011 57533078080207863047178017)
        ·
          refine ⟨43149808560155897285383513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57533078080207863047178017 43149808560155897285383513)
          ·
            refine ⟨32362356420116922964037635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43149808560155897285383513 32362356420116922964037635)
            ·
              refine ⟨48543534630175384446056453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32362356420116922964037635 48543534630175384446056453)
              ·
                refine ⟨9101912743157884583635585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48543534630175384446056453 9101912743157884583635585)
                ·
                  refine ⟨6826434557368413437726689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9101912743157884583635585 6826434557368413437726689)
                  ·
                    refine ⟨5119825918026310078295017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826434557368413437726689 5119825918026310078295017)
                    ·
                      refine ⟨3839869438519732558721263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119825918026310078295017 3839869438519732558721263)
                      ·
                        rfl

theorem cell23_7478119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_7478119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478119 prefixEnd_7478119 := by exact prefixLift 7478119
  have htrace : WordTrace (prefixWord ++ tailWord_7478119) baseStart_7478119 baseEnd_7478119 := by
    simpa [prefixWord, tailWord_7478119, baseEnd_7478119] using wordTrace_append hprefix tailTrace_7478119
  have hstable : (prefixWord ++ tailWord_7478119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478119).length < 2 ^ (prefixWord ++ tailWord_7478119).sum := by decide
  have hdescent : baseEnd_7478119 < baseStart_7478119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478138 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_7478138 : Nat := 118140960795 + 7478138 * 2 ^ 59
def prefixEnd_7478138 : Nat := 4983230072969 + 3 ^ 40 * 7478138 * 2
def baseEnd_7478138 : Nat := 1279959731550722661461225

theorem tailTrace_7478138 : CollatzResearch.WordTrace tailWord_7478138 prefixEnd_7478138 1279959731550722661461225 := by
  unfold tailWord_7478138
  simp only [CollatzResearch.WordTrace]
  refine ⟨68187525045497666283816767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181833400121327110090178045 68187525045497666283816767)
  ·
    refine ⟨102281287568246499425725151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68187525045497666283816767 102281287568246499425725151)
    ·
      refine ⟨153421931352369749138587727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102281287568246499425725151 153421931352369749138587727)
      ·
        refine ⟨230132897028554623707881591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153421931352369749138587727 230132897028554623707881591)
        ·
          refine ⟨345199345542831935561822387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230132897028554623707881591 345199345542831935561822387)
          ·
            refine ⟨517799018314247903342733581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345199345542831935561822387 517799018314247903342733581)
            ·
              refine ⟨194174631867842963753525093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517799018314247903342733581 194174631867842963753525093)
              ·
                refine ⟨36407743475220555703785955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194174631867842963753525093 36407743475220555703785955)
                ·
                  refine ⟨54611615212830833555678933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36407743475220555703785955 54611615212830833555678933)
                  ·
                    refine ⟨1279959731550722661461225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54611615212830833555678933 1279959731550722661461225)
                    ·
                      rfl

theorem cell23_7478138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_7478138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478138 prefixEnd_7478138 := by exact prefixLift 7478138
  have htrace : WordTrace (prefixWord ++ tailWord_7478138) baseStart_7478138 baseEnd_7478138 := by
    simpa [prefixWord, tailWord_7478138, baseEnd_7478138] using wordTrace_append hprefix tailTrace_7478138
  have hstable : (prefixWord ++ tailWord_7478138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478138).length < 2 ^ (prefixWord ++ tailWord_7478138).sum := by decide
  have hdescent : baseEnd_7478138 < baseStart_7478138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478155 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 2, 5]
def baseStart_7478155 : Nat := 118140960795 + 7478155 * 2 ^ 59
def prefixEnd_7478155 : Nat := 4983230072969 + 3 ^ 40 * 7478155 * 2
def baseEnd_7478155 : Nat := 1279962641274431472623699

theorem tailTrace_7478155 : CollatzResearch.WordTrace tailWord_7478155 prefixEnd_7478155 1279962641274431472623699 := by
  unfold tailWord_7478155
  simp only [CollatzResearch.WordTrace]
  refine ⟨272750720222929077038635919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181833813481952718025757279 272750720222929077038635919)
  ·
    refine ⟨409126080334393615557953879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272750720222929077038635919 409126080334393615557953879)
    ·
      refine ⟨613689120501590423336930819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409126080334393615557953879 613689120501590423336930819)
      ·
        refine ⟨920533680752385635005396229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613689120501590423336930819 920533680752385635005396229)
        ·
          refine ⟨172600065141072306563511793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 920533680752385635005396229 172600065141072306563511793)
          ·
            refine ⟨129450048855804229922633845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172600065141072306563511793 129450048855804229922633845)
            ·
              refine ⟨12135942080231646555246923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129450048855804229922633845 12135942080231646555246923)
              ·
                refine ⟨18203913120347469832870385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12135942080231646555246923 18203913120347469832870385)
                ·
                  refine ⟨13652934840260602374652789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18203913120347469832870385 13652934840260602374652789)
                  ·
                    refine ⟨1279962641274431472623699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13652934840260602374652789 1279962641274431472623699)
                    ·
                      rfl

theorem cell23_7478155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 5].length) (baseStart_7478155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478155 prefixEnd_7478155 := by exact prefixLift 7478155
  have htrace : WordTrace (prefixWord ++ tailWord_7478155) baseStart_7478155 baseEnd_7478155 := by
    simpa [prefixWord, tailWord_7478155, baseEnd_7478155] using wordTrace_append hprefix tailTrace_7478155
  have hstable : (prefixWord ++ tailWord_7478155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478155).length < 2 ^ (prefixWord ++ tailWord_7478155).sum := by decide
  have hdescent : baseEnd_7478155 < baseStart_7478155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478195 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3]
def baseStart_7478195 : Nat := 118140960795 + 7478195 * 2 ^ 59
def prefixEnd_7478195 : Nat := 4983230072969 + 3 ^ 40 * 7478195 * 2
def baseEnd_7478195 : Nat := 3839908463049474261370913

theorem tailTrace_7478195 : CollatzResearch.WordTrace tailWord_7478195 prefixEnd_7478195 3839908463049474261370913 := by
  unfold tailWord_7478195
  simp only [CollatzResearch.WordTrace]
  refine ⟨272752179142784163870092039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181834786095189442580061359 272752179142784163870092039)
  ·
    refine ⟨409128268714176245805138059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272752179142784163870092039 409128268714176245805138059)
    ·
      refine ⟨613692403071264368707707089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409128268714176245805138059 613692403071264368707707089)
      ·
        refine ⟨460269302303448276530780317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613692403071264368707707089 460269302303448276530780317)
        ·
          refine ⟨172600988363793103699042619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460269302303448276530780317 172600988363793103699042619)
          ·
            refine ⟨258901482545689655548563929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172600988363793103699042619 258901482545689655548563929)
            ·
              refine ⟨194176111909267241661422947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258901482545689655548563929 194176111909267241661422947)
              ·
                refine ⟨291264167863900862492134421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194176111909267241661422947 291264167863900862492134421)
                ·
                  refine ⟨13653007868620352929318801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 291264167863900862492134421 13653007868620352929318801)
                  ·
                    refine ⟨10239755901465264696989101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13653007868620352929318801 10239755901465264696989101)
                    ·
                      refine ⟨3839908463049474261370913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10239755901465264696989101 3839908463049474261370913)
                      ·
                        rfl

theorem cell23_7478195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_7478195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478195 prefixEnd_7478195 := by exact prefixLift 7478195
  have htrace : WordTrace (prefixWord ++ tailWord_7478195) baseStart_7478195 baseEnd_7478195 := by
    simpa [prefixWord, tailWord_7478195, baseEnd_7478195] using wordTrace_append hprefix tailTrace_7478195
  have hstable : (prefixWord ++ tailWord_7478195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478195).length < 2 ^ (prefixWord ++ tailWord_7478195).sum := by decide
  have hdescent : baseEnd_7478195 < baseStart_7478195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478219 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 1, 4]
def baseStart_7478219 : Nat := 118140960795 + 7478219 * 2 ^ 59
def prefixEnd_7478219 : Nat := 4983230072969 + 3 ^ 40 * 7478219 * 2
def baseEnd_7478219 : Nat := 1279973595528394055823601

theorem tailTrace_7478219 : CollatzResearch.WordTrace tailWord_7478219 prefixEnd_7478219 1279973595528394055823601 := by
  unfold tailWord_7478219
  simp only [CollatzResearch.WordTrace]
  refine ⟨272753054494697215968965711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181835369663131477312643807 272753054494697215968965711)
  ·
    refine ⟨409129581742045823953448567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272753054494697215968965711 409129581742045823953448567)
    ·
      refine ⟨613694372613068735930172851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409129581742045823953448567 613694372613068735930172851)
      ·
        refine ⟨920541558919603103895259277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613694372613068735930172851 920541558919603103895259277)
        ·
          refine ⟨345203084594851163960722229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920541558919603103895259277 345203084594851163960722229)
          ·
            refine ⟨32362789180767296621317709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345203084594851163960722229 32362789180767296621317709)
            ·
              refine ⟨12136045942787736232994141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32362789180767296621317709 12136045942787736232994141)
              ·
                refine ⟨4551017228545401087372803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12136045942787736232994141 4551017228545401087372803)
                ·
                  refine ⟨6826525842818101631059205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551017228545401087372803 6826525842818101631059205)
                  ·
                    refine ⟨1279973595528394055823601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6826525842818101631059205 1279973595528394055823601)
                    ·
                      rfl

theorem cell23_7478219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 4].length) (baseStart_7478219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478219 prefixEnd_7478219 := by exact prefixLift 7478219
  have htrace : WordTrace (prefixWord ++ tailWord_7478219) baseStart_7478219 baseEnd_7478219 := by
    simpa [prefixWord, tailWord_7478219, baseEnd_7478219] using wordTrace_append hprefix tailTrace_7478219
  have hstable : (prefixWord ++ tailWord_7478219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478219).length < 2 ^ (prefixWord ++ tailWord_7478219).sum := by decide
  have hdescent : baseEnd_7478219 < baseStart_7478219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478229 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7478229 : Nat := 118140960795 + 7478229 * 2 ^ 59
def prefixEnd_7478229 : Nat := 4983230072969 + 3 ^ 40 * 7478229 * 2
def baseEnd_7478229 : Nat := 3839925921391727128345757

theorem tailTrace_7478229 : CollatzResearch.WordTrace tailWord_7478229 prefixEnd_7478229 3839925921391727128345757 := by
  unfold tailWord_7478229
  simp only [CollatzResearch.WordTrace]
  refine ⟨272753419224660987676829741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181835612816440658451219827 272753419224660987676829741)
  ·
    refine ⟨102282532209247870378811153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272753419224660987676829741 102282532209247870378811153)
    ·
      refine ⟨76711899156935902784108365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102282532209247870378811153 76711899156935902784108365)
      ·
        refine ⟨28766962183850963544040637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76711899156935902784108365 28766962183850963544040637)
        ·
          refine ⟨10787610818944111329015239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28766962183850963544040637 10787610818944111329015239)
          ·
            refine ⟨16181416228416166993522859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787610818944111329015239 16181416228416166993522859)
            ·
              refine ⟨24272124342624250490284289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16181416228416166993522859 24272124342624250490284289)
              ·
                refine ⟨18204093256968187867713217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24272124342624250490284289 18204093256968187867713217)
                ·
                  refine ⟨13653069942726140900784913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18204093256968187867713217 13653069942726140900784913)
                  ·
                    refine ⟨10239802457044605675588685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13653069942726140900784913 10239802457044605675588685)
                    ·
                      refine ⟨3839925921391727128345757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10239802457044605675588685 3839925921391727128345757)
                      ·
                        rfl

theorem cell23_7478229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7478229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478229 prefixEnd_7478229 := by exact prefixLift 7478229
  have htrace : WordTrace (prefixWord ++ tailWord_7478229) baseStart_7478229 baseEnd_7478229 := by
    simpa [prefixWord, tailWord_7478229, baseEnd_7478229] using wordTrace_append hprefix tailTrace_7478229
  have hstable : (prefixWord ++ tailWord_7478229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478229).length < 2 ^ (prefixWord ++ tailWord_7478229).sum := by decide
  have hdescent : baseEnd_7478229 < baseStart_7478229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478260 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7478260 : Nat := 118140960795 + 7478260 * 2 ^ 59
def prefixEnd_7478260 : Nat := 4983230072969 + 3 ^ 40 * 7478260 * 2
def baseEnd_7478260 : Nat := 3839941839292016507058115

theorem tailTrace_7478260 : CollatzResearch.WordTrace tailWord_7478260 prefixEnd_7478260 3839941839292016507058115 := by
  unfold tailWord_7478260
  simp only [CollatzResearch.WordTrace]
  refine ⟨136377274943774339985604117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181836366591699119980805489 136377274943774339985604117)
  ·
    refine ⟨6392684762989422186825193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136377274943774339985604117 6392684762989422186825193)
    ·
      refine ⟨4794513572242066640118895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6392684762989422186825193 4794513572242066640118895)
      ·
        refine ⟨7191770358363099960178343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794513572242066640118895 7191770358363099960178343)
        ·
          refine ⟨10787655537544649940267515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191770358363099960178343 10787655537544649940267515)
          ·
            refine ⟨16181483306316974910401273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787655537544649940267515 16181483306316974910401273)
            ·
              refine ⟨12136112479737731182800955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16181483306316974910401273 12136112479737731182800955)
              ·
                refine ⟨18204168719606596774201433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12136112479737731182800955 18204168719606596774201433)
                ·
                  refine ⟨13653126539704947580651075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18204168719606596774201433 13653126539704947580651075)
                  ·
                    refine ⟨20479689809557421370976613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13653126539704947580651075 20479689809557421370976613)
                    ·
                      refine ⟨3839941839292016507058115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20479689809557421370976613 3839941839292016507058115)
                      ·
                        rfl

theorem cell23_7478260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7478260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478260 prefixEnd_7478260 := by exact prefixLift 7478260
  have htrace : WordTrace (prefixWord ++ tailWord_7478260) baseStart_7478260 baseEnd_7478260 := by
    simpa [prefixWord, tailWord_7478260, baseEnd_7478260] using wordTrace_append hprefix tailTrace_7478260
  have hstable : (prefixWord ++ tailWord_7478260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478260).length < 2 ^ (prefixWord ++ tailWord_7478260).sum := by decide
  have hdescent : baseEnd_7478260 < baseStart_7478260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478279 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 1, 5]
def baseStart_7478279 : Nat := 118140960795 + 7478279 * 2 ^ 59
def prefixEnd_7478279 : Nat := 4983230072969 + 3 ^ 40 * 7478279 * 2
def baseEnd_7478279 : Nat := 1279983865141483977573509

theorem tailTrace_7478279 : CollatzResearch.WordTrace tailWord_7478279 prefixEnd_7478279 1279983865141483977573509 := by
  unfold tailWord_7478279
  simp only [CollatzResearch.WordTrace]
  refine ⟨272755242874479846216149891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181836828582986564144099927 272755242874479846216149891)
  ·
    refine ⟨409132864311719769324224837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272755242874479846216149891 409132864311719769324224837)
    ·
      refine ⟨76712412058447456748292157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409132864311719769324224837 76712412058447456748292157)
      ·
        refine ⟨28767154521917796280609559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76712412058447456748292157 28767154521917796280609559)
        ·
          refine ⟨43150731782876694420914339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28767154521917796280609559 43150731782876694420914339)
          ·
            refine ⟨64726097674315041631371509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43150731782876694420914339 64726097674315041631371509)
            ·
              refine ⟨6068071656967035152941079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64726097674315041631371509 6068071656967035152941079)
              ·
                refine ⟨9102107485450552729411619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068071656967035152941079 9102107485450552729411619)
                ·
                  refine ⟨13653161228175829094117429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102107485450552729411619 13653161228175829094117429)
                  ·
                    refine ⟨1279983865141483977573509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13653161228175829094117429 1279983865141483977573509)
                    ·
                      rfl

theorem cell23_7478279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_7478279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478279 prefixEnd_7478279 := by exact prefixLift 7478279
  have htrace : WordTrace (prefixWord ++ tailWord_7478279) baseStart_7478279 baseEnd_7478279 := by
    simpa [prefixWord, tailWord_7478279, baseEnd_7478279] using wordTrace_append hprefix tailTrace_7478279
  have hstable : (prefixWord ++ tailWord_7478279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478279).length < 2 ^ (prefixWord ++ tailWord_7478279).sum := by decide
  have hdescent : baseEnd_7478279 < baseStart_7478279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478293 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_7478293 : Nat := 118140960795 + 7478293 * 2 ^ 59
def prefixEnd_7478293 : Nat := 4983230072969 + 3 ^ 40 * 7478293 * 2
def baseEnd_7478293 : Nat := 3839958784153614877945463

theorem tailTrace_7478293 : CollatzResearch.WordTrace tailWord_7478293 prefixEnd_7478293 3839958784153614877945463 := by
  unfold tailWord_7478293
  simp only [CollatzResearch.WordTrace]
  refine ⟨272755753496429126607159533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181837168997619417738106355 272755753496429126607159533)
  ·
    refine ⟨102283407561160922477684825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272755753496429126607159533 102283407561160922477684825)
    ·
      refine ⟨76712555670870691858263619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102283407561160922477684825 76712555670870691858263619)
      ·
        refine ⟨115068833506306037787395429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76712555670870691858263619 115068833506306037787395429)
        ·
          refine ⟨21575406282432382085136643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115068833506306037787395429 21575406282432382085136643)
          ·
            refine ⟨32363109423648573127704965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21575406282432382085136643 32363109423648573127704965)
            ·
              refine ⟨6068083016934107461444681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32363109423648573127704965 6068083016934107461444681)
              ·
                refine ⟨4551062262700580596083511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6068083016934107461444681 4551062262700580596083511)
                ·
                  refine ⟨6826593394050870894125267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551062262700580596083511 6826593394050870894125267)
                  ·
                    refine ⟨10239890091076306341187901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826593394050870894125267 10239890091076306341187901)
                    ·
                      refine ⟨3839958784153614877945463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10239890091076306341187901 3839958784153614877945463)
                      ·
                        rfl

theorem cell23_7478293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_7478293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478293 prefixEnd_7478293 := by exact prefixLift 7478293
  have htrace : WordTrace (prefixWord ++ tailWord_7478293) baseStart_7478293 baseEnd_7478293 := by
    simpa [prefixWord, tailWord_7478293, baseEnd_7478293] using wordTrace_append hprefix tailTrace_7478293
  have hstable : (prefixWord ++ tailWord_7478293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478293).length < 2 ^ (prefixWord ++ tailWord_7478293).sum := by decide
  have hdescent : baseEnd_7478293 < baseStart_7478293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478322 : List Nat := [3, 2, 1, 1, 2, 2, 5, 7]
def baseStart_7478322 : Nat := 118140960795 + 7478322 * 2 ^ 59
def prefixEnd_7478322 : Nat := 4983230072969 + 3 ^ 40 * 7478322 * 2
def baseEnd_7478322 : Nat := 142221247225651676462327

theorem tailTrace_7478322 : CollatzResearch.WordTrace tailWord_7478322 prefixEnd_7478322 142221247225651676462327 := by
  unfold tailWord_7478322
  simp only [CollatzResearch.WordTrace]
  refine ⟨68189202803331016139991305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181837874142216043039976813 68189202803331016139991305)
  ·
    refine ⟨51141902102498262104993479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68189202803331016139991305 51141902102498262104993479)
    ·
      refine ⟨76712853153747393157490219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51141902102498262104993479 76712853153747393157490219)
      ·
        refine ⟨115069279730621089736235329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76712853153747393157490219 115069279730621089736235329)
        ·
          refine ⟨86301959797965817302176497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115069279730621089736235329 86301959797965817302176497)
          ·
            refine ⟨64726469848474362976632373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86301959797965817302176497 64726469848474362976632373)
            ·
              refine ⟨6068106548294471529059285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64726469848474362976632373 6068106548294471529059285)
              ·
                refine ⟨142221247225651676462327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6068106548294471529059285 142221247225651676462327)
                ·
                  rfl

theorem cell23_7478322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_7478322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478322 prefixEnd_7478322 := by exact prefixLift 7478322
  have htrace : WordTrace (prefixWord ++ tailWord_7478322) baseStart_7478322 baseEnd_7478322 := by
    simpa [prefixWord, tailWord_7478322, baseEnd_7478322] using wordTrace_append hprefix tailTrace_7478322
  have hstable : (prefixWord ++ tailWord_7478322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478322).length < 2 ^ (prefixWord ++ tailWord_7478322).sum := by decide
  have hdescent : baseEnd_7478322 < baseStart_7478322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478333 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7478333 : Nat := 118140960795 + 7478333 * 2 ^ 59
def prefixEnd_7478333 : Nat := 4983230072969 + 3 ^ 40 * 7478333 * 2
def baseEnd_7478333 : Nat := 3839979323379794721445279

theorem tailTrace_7478333 : CollatzResearch.WordTrace tailWord_7478333 prefixEnd_7478333 3839979323379794721445279 := by
  unfold tailWord_7478333
  simp only [CollatzResearch.WordTrace]
  refine ⟨272757212416284213438615653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181838141610856142292410435 272757212416284213438615653)
  ·
    refine ⟨51141977328053290019740435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272757212416284213438615653 51141977328053290019740435)
    ·
      refine ⟨76712965992079935029610653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51141977328053290019740435 76712965992079935029610653)
      ·
        refine ⟨28767362247029975636103995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76712965992079935029610653 28767362247029975636103995)
        ·
          refine ⟨43151043370544963454155993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28767362247029975636103995 43151043370544963454155993)
          ·
            refine ⟨32363282527908722590616995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43151043370544963454155993 32363282527908722590616995)
            ·
              refine ⟨48544923791863083885925493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32363282527908722590616995 48544923791863083885925493)
              ·
                refine ⟨4551086605487164114305515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48544923791863083885925493 4551086605487164114305515)
                ·
                  refine ⟨6826629908230746171458273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551086605487164114305515 6826629908230746171458273)
                  ·
                    refine ⟨5119972431173059628593705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826629908230746171458273 5119972431173059628593705)
                    ·
                      refine ⟨3839979323379794721445279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5119972431173059628593705 3839979323379794721445279)
                      ·
                        rfl

theorem cell23_7478333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7478333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478333 prefixEnd_7478333 := by exact prefixLift 7478333
  have htrace : WordTrace (prefixWord ++ tailWord_7478333) baseStart_7478333 baseEnd_7478333 := by
    simpa [prefixWord, tailWord_7478333, baseEnd_7478333] using wordTrace_append hprefix tailTrace_7478333
  have hstable : (prefixWord ++ tailWord_7478333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478333).length < 2 ^ (prefixWord ++ tailWord_7478333).sum := by decide
  have hdescent : baseEnd_7478333 < baseStart_7478333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478345 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_7478345 : Nat := 118140960795 + 7478345 * 2 ^ 59
def prefixEnd_7478345 : Nat := 4983230072969 + 3 ^ 40 * 7478345 * 2
def baseEnd_7478345 : Nat := 3839985485147648674495223

theorem tailTrace_7478345 : CollatzResearch.WordTrace tailWord_7478345 prefixEnd_7478345 3839985485147648674495223 := by
  unfold tailWord_7478345
  simp only [CollatzResearch.WordTrace]
  refine ⟨272757650092240739488052489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181838433394827159658701659 272757650092240739488052489)
  ·
    refine ⟨204568237569180554616039367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272757650092240739488052489 204568237569180554616039367)
    ·
      refine ⟨306852356353770831924059051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204568237569180554616039367 306852356353770831924059051)
      ·
        refine ⟨460278534530656247886088577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306852356353770831924059051 460278534530656247886088577)
        ·
          refine ⟨345208900897992185914566433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460278534530656247886088577 345208900897992185914566433)
          ·
            refine ⟨258906675673494139435924825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345208900897992185914566433 258906675673494139435924825)
            ·
              refine ⟨194180006755120604576943619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258906675673494139435924825 194180006755120604576943619)
              ·
                refine ⟨291270010132680906865415429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194180006755120604576943619 291270010132680906865415429)
                ·
                  refine ⟨54613126899877670037265393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291270010132680906865415429 54613126899877670037265393)
                  ·
                    refine ⟨40959845174908252527949045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54613126899877670037265393 40959845174908252527949045)
                    ·
                      refine ⟨3839985485147648674495223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40959845174908252527949045 3839985485147648674495223)
                      ·
                        rfl

theorem cell23_7478345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_7478345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478345 prefixEnd_7478345 := by exact prefixLift 7478345
  have htrace : WordTrace (prefixWord ++ tailWord_7478345) baseStart_7478345 baseEnd_7478345 := by
    simpa [prefixWord, tailWord_7478345, baseEnd_7478345] using wordTrace_append hprefix tailTrace_7478345
  have hstable : (prefixWord ++ tailWord_7478345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478345).length < 2 ^ (prefixWord ++ tailWord_7478345).sum := by decide
  have hdescent : baseEnd_7478345 < baseStart_7478345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478395 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 9]
def baseStart_7478395 : Nat := 118140960795 + 7478395 * 2 ^ 59
def prefixEnd_7478395 : Nat := 4983230072969 + 3 ^ 40 * 7478395 * 2
def baseEnd_7478395 : Nat := 426667906575597053207777

theorem tailTrace_7478395 : CollatzResearch.WordTrace tailWord_7478395 prefixEnd_7478395 426667906575597053207777 := by
  unfold tailWord_7478395
  simp only [CollatzResearch.WordTrace]
  refine ⟨272759473742059598027372639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181839649161373065351581759 272759473742059598027372639)
  ·
    refine ⟨409139210613089397041058959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272759473742059598027372639 409139210613089397041058959)
    ·
      refine ⟨613708815919634095561588439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409139210613089397041058959 613708815919634095561588439)
      ·
        refine ⟨920563223879451143342382659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613708815919634095561588439 920563223879451143342382659)
        ·
          refine ⟨1380844835819176715013573989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920563223879451143342382659 1380844835819176715013573989)
          ·
            refine ⟨258908406716095634065045123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1380844835819176715013573989 258908406716095634065045123)
            ·
              refine ⟨388362610074143451097567685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258908406716095634065045123 388362610074143451097567685)
              ·
                refine ⟨72817989388901897080793941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388362610074143451097567685 72817989388901897080793941)
                ·
                  refine ⟨426667906575597053207777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72817989388901897080793941 426667906575597053207777)
                  ·
                    rfl

theorem cell23_7478395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 9].length) (baseStart_7478395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478395 prefixEnd_7478395 := by exact prefixLift 7478395
  have htrace : WordTrace (prefixWord ++ tailWord_7478395) baseStart_7478395 baseEnd_7478395 := by
    simpa [prefixWord, tailWord_7478395, baseEnd_7478395] using wordTrace_append hprefix tailTrace_7478395
  have hstable : (prefixWord ++ tailWord_7478395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478395).length < 2 ^ (prefixWord ++ tailWord_7478395).sum := by decide
  have hdescent : baseEnd_7478395 < baseStart_7478395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478423 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_7478423 : Nat := 118140960795 + 7478423 * 2 ^ 59
def prefixEnd_7478423 : Nat := 4983230072969 + 3 ^ 40 * 7478423 * 2
def baseEnd_7478423 : Nat := 3840025536638699369319865

theorem tailTrace_7478423 : CollatzResearch.WordTrace tailWord_7478423 prefixEnd_7478423 3840025536638699369319865 := by
  unfold tailWord_7478423
  simp only [CollatzResearch.WordTrace]
  refine ⟨272760494985958158809391923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181840329990638772539594615 272760494985958158809391923)
  ·
    refine ⟨409140742478937238214087885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272760494985958158809391923 409140742478937238214087885)
    ·
      refine ⟨153427778429601464330282957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409140742478937238214087885 153427778429601464330282957)
      ·
        refine ⟨57535416911100549123856109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153427778429601464330282957 57535416911100549123856109)
        ·
          refine ⟨21575781341662705921446041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57535416911100549123856109 21575781341662705921446041)
          ·
            refine ⟨16181836006247029441084531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21575781341662705921446041 16181836006247029441084531)
            ·
              refine ⟨24272754009370544161626797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16181836006247029441084531 24272754009370544161626797)
              ·
                refine ⟨9102282753513954060610049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24272754009370544161626797 9102282753513954060610049)
                ·
                  refine ⟨6826712065135465545457537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9102282753513954060610049 6826712065135465545457537)
                  ·
                    refine ⟨5120034048851599159093153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826712065135465545457537 5120034048851599159093153)
                    ·
                      refine ⟨3840025536638699369319865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120034048851599159093153 3840025536638699369319865)
                      ·
                        rfl

theorem cell23_7478423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_7478423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478423 prefixEnd_7478423 := by exact prefixLift 7478423
  have htrace : WordTrace (prefixWord ++ tailWord_7478423) baseStart_7478423 baseEnd_7478423 := by
    simpa [prefixWord, tailWord_7478423, baseEnd_7478423] using wordTrace_append hprefix tailTrace_7478423
  have hstable : (prefixWord ++ tailWord_7478423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478423).length < 2 ^ (prefixWord ++ tailWord_7478423).sum := by decide
  have hdescent : baseEnd_7478423 < baseStart_7478423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478470 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7478470 : Nat := 118140960795 + 7478470 * 2 ^ 59
def prefixEnd_7478470 : Nat := 4983230072969 + 3 ^ 40 * 7478470 * 2
def baseEnd_7478470 : Nat := 3840049670229460685432149

theorem tailTrace_7478470 : CollatzResearch.WordTrace tailWord_7478470 prefixEnd_7478470 3840049670229460685432149 := by
  unfold tailWord_7478470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8523819038024621432386027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181841472811191923890901909 8523819038024621432386027)
  ·
    refine ⟨12785728557036932148579041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8523819038024621432386027 12785728557036932148579041)
    ·
      refine ⟨9589296417777699111434281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12785728557036932148579041 9589296417777699111434281)
      ·
        refine ⟨7191972313333274333575711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9589296417777699111434281 7191972313333274333575711)
        ·
          refine ⟨10787958469999911500363567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191972313333274333575711 10787958469999911500363567)
          ·
            refine ⟨16181937704999867250545351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787958469999911500363567 16181937704999867250545351)
            ·
              refine ⟨24272906557499800875818027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16181937704999867250545351 24272906557499800875818027)
              ·
                refine ⟨36409359836249701313727041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24272906557499800875818027 36409359836249701313727041)
                ·
                  refine ⟨27307019877187275985295281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36409359836249701313727041 27307019877187275985295281)
                  ·
                    refine ⟨20480264907890456988971461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27307019877187275985295281 20480264907890456988971461)
                    ·
                      refine ⟨3840049670229460685432149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20480264907890456988971461 3840049670229460685432149)
                      ·
                        rfl

theorem cell23_7478470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7478470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478470 prefixEnd_7478470 := by exact prefixLift 7478470
  have htrace : WordTrace (prefixWord ++ tailWord_7478470) baseStart_7478470 baseEnd_7478470 := by
    simpa [prefixWord, tailWord_7478470, baseEnd_7478470] using wordTrace_append hprefix tailTrace_7478470
  have hstable : (prefixWord ++ tailWord_7478470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478470).length < 2 ^ (prefixWord ++ tailWord_7478470).sum := by decide
  have hdescent : baseEnd_7478470 < baseStart_7478470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478493 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7478493 : Nat := 118140960795 + 7478493 * 2 ^ 59
def prefixEnd_7478493 : Nat := 4983230072969 + 3 ^ 40 * 7478493 * 2
def baseEnd_7478493 : Nat := 1280020493428171365148181

theorem tailTrace_7478493 : CollatzResearch.WordTrace tailWord_7478493 prefixEnd_7478493 1280020493428171365148181 := by
  unfold tailWord_7478493
  simp only [CollatzResearch.WordTrace]
  refine ⟨272763048095704560764440133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181842032063803040509626755 272763048095704560764440133)
  ·
    refine ⟨51143071517944605143332525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272763048095704560764440133 51143071517944605143332525)
    ·
      refine ⟨19178651819229226928749697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51143071517944605143332525 19178651819229226928749697)
      ·
        refine ⟨14383988864421920196562273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19178651819229226928749697 14383988864421920196562273)
        ·
          refine ⟨10787991648316440147421705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14383988864421920196562273 10787991648316440147421705)
          ·
            refine ⟨8090993736237330110566279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10787991648316440147421705 8090993736237330110566279)
            ·
              refine ⟨12136490604355995165849419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090993736237330110566279 12136490604355995165849419)
              ·
                refine ⟨18204735906533992748774129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12136490604355995165849419 18204735906533992748774129)
                ·
                  refine ⟨13653551929900494561580597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18204735906533992748774129 13653551929900494561580597)
                  ·
                    refine ⟨1280020493428171365148181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13653551929900494561580597 1280020493428171365148181)
                    ·
                      rfl

theorem cell23_7478493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7478493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478493 prefixEnd_7478493 := by exact prefixLift 7478493
  have htrace : WordTrace (prefixWord ++ tailWord_7478493) baseStart_7478493 baseEnd_7478493 := by
    simpa [prefixWord, tailWord_7478493, baseEnd_7478493] using wordTrace_append hprefix tailTrace_7478493
  have hstable : (prefixWord ++ tailWord_7478493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478493).length < 2 ^ (prefixWord ++ tailWord_7478493).sum := by decide
  have hdescent : baseEnd_7478493 < baseStart_7478493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478496 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_7478496 : Nat := 118140960795 + 7478496 * 2 ^ 59
def prefixEnd_7478496 : Nat := 4983230072969 + 3 ^ 40 * 7478496 * 2
def baseEnd_7478496 : Nat := 3840063020726477583707029

theorem tailTrace_7478496 : CollatzResearch.WordTrace tailWord_7478496 prefixEnd_7478496 3840063020726477583707029 := by
  unfold tailWord_7478496
  simp only [CollatzResearch.WordTrace]
  refine ⟨136381578757346846138399671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181842105009795794851199561 136381578757346846138399671)
  ·
    refine ⟨204572368136020269207599507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136381578757346846138399671 204572368136020269207599507)
    ·
      refine ⟨306858552204030403811399261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204572368136020269207599507 306858552204030403811399261)
      ·
        refine ⟨115071957076511401429274723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306858552204030403811399261 115071957076511401429274723)
        ·
          refine ⟨172607935614767102143912085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115071957076511401429274723 172607935614767102143912085)
          ·
            refine ⟨8090996981942207912995879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172607935614767102143912085 8090996981942207912995879)
            ·
              refine ⟨12136495472913311869493819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090996981942207912995879 12136495472913311869493819)
              ·
                refine ⟨18204743209369967804240729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12136495472913311869493819 18204743209369967804240729)
                ·
                  refine ⟨13653557407027475853180547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18204743209369967804240729 13653557407027475853180547)
                  ·
                    refine ⟨20480336110541213779770821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13653557407027475853180547 20480336110541213779770821)
                    ·
                      refine ⟨3840063020726477583707029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20480336110541213779770821 3840063020726477583707029)
                      ·
                        rfl

theorem cell23_7478496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_7478496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478496 prefixEnd_7478496 := by exact prefixLift 7478496
  have htrace : WordTrace (prefixWord ++ tailWord_7478496) baseStart_7478496 baseEnd_7478496 := by
    simpa [prefixWord, tailWord_7478496, baseEnd_7478496] using wordTrace_append hprefix tailTrace_7478496
  have hstable : (prefixWord ++ tailWord_7478496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478496).length < 2 ^ (prefixWord ++ tailWord_7478496).sum := by decide
  have hdescent : baseEnd_7478496 < baseStart_7478496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478509 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7478509 : Nat := 118140960795 + 7478509 * 2 ^ 59
def prefixEnd_7478509 : Nat := 4983230072969 + 3 ^ 40 * 7478509 * 2
def baseEnd_7478509 : Nat := 3840069695974986032844469

theorem tailTrace_7478509 : CollatzResearch.WordTrace tailWord_7478509 prefixEnd_7478509 3840069695974986032844469 := by
  unfold tailWord_7478509
  simp only [CollatzResearch.WordTrace]
  refine ⟨272763631663646595497022581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181842421109097730331348387 272763631663646595497022581)
  ·
    refine ⟨25571590468466868327845867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272763631663646595497022581 25571590468466868327845867)
    ·
      refine ⟨38357385702700302491768801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25571590468466868327845867 38357385702700302491768801)
      ·
        refine ⟨28768039277025226868826601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38357385702700302491768801 28768039277025226868826601)
        ·
          refine ⟨21576029457768920151619951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28768039277025226868826601 21576029457768920151619951)
          ·
            refine ⟨32364044186653380227429927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21576029457768920151619951 32364044186653380227429927)
            ·
              refine ⟨48546066279980070341144891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32364044186653380227429927 48546066279980070341144891)
              ·
                refine ⟨72819099419970105511717337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48546066279980070341144891 72819099419970105511717337)
                ·
                  refine ⟨54614324564977579133788003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72819099419970105511717337 54614324564977579133788003)
                  ·
                    refine ⟨81921486847466368700682005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54614324564977579133788003 81921486847466368700682005)
                    ·
                      refine ⟨3840069695974986032844469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81921486847466368700682005 3840069695974986032844469)
                      ·
                        rfl

theorem cell23_7478509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7478509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478509 prefixEnd_7478509 := by exact prefixLift 7478509
  have htrace : WordTrace (prefixWord ++ tailWord_7478509) baseStart_7478509 baseEnd_7478509 := by
    simpa [prefixWord, tailWord_7478509, baseEnd_7478509] using wordTrace_append hprefix tailTrace_7478509
  have hstable : (prefixWord ++ tailWord_7478509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478509).length < 2 ^ (prefixWord ++ tailWord_7478509).sum := by decide
  have hdescent : baseEnd_7478509 < baseStart_7478509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478522 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_7478522 : Nat := 118140960795 + 7478522 * 2 ^ 59
def prefixEnd_7478522 : Nat := 4983230072969 + 3 ^ 40 * 7478522 * 2
def baseEnd_7478522 : Nat := 3840076371223494481981909

theorem tailTrace_7478522 : CollatzResearch.WordTrace tailWord_7478522 prefixEnd_7478522 3840076371223494481981909 := by
  unfold tailWord_7478522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68191026453149874679311455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181842737208399665811497213 68191026453149874679311455)
  ·
    refine ⟨102286539679724812018967183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68191026453149874679311455 102286539679724812018967183)
    ·
      refine ⟨153429809519587218028450775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102286539679724812018967183 153429809519587218028450775)
      ·
        refine ⟨230144714279380827042676163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153429809519587218028450775 230144714279380827042676163)
        ·
          refine ⟨345217071419071240564014245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230144714279380827042676163 345217071419071240564014245)
          ·
            refine ⟨64728200891075857605752671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345217071419071240564014245 64728200891075857605752671)
            ·
              refine ⟨97092301336613786408629007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64728200891075857605752671 97092301336613786408629007)
              ·
                refine ⟨145638452004920679612943511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97092301336613786408629007 145638452004920679612943511)
                ·
                  refine ⟨218457678007381019419415267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145638452004920679612943511 218457678007381019419415267)
                  ·
                    refine ⟨327686517011071529129122901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218457678007381019419415267 327686517011071529129122901)
                    ·
                      refine ⟨3840076371223494481981909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327686517011071529129122901 3840076371223494481981909)
                      ·
                        rfl

theorem cell23_7478522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_7478522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478522 prefixEnd_7478522 := by exact prefixLift 7478522
  have htrace : WordTrace (prefixWord ++ tailWord_7478522) baseStart_7478522 baseEnd_7478522 := by
    simpa [prefixWord, tailWord_7478522, baseEnd_7478522] using wordTrace_append hprefix tailTrace_7478522
  have hstable : (prefixWord ++ tailWord_7478522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478522).length < 2 ^ (prefixWord ++ tailWord_7478522).sum := by decide
  have hdescent : baseEnd_7478522 < baseStart_7478522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478556 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7478556 : Nat := 118140960795 + 7478556 * 2 ^ 59
def prefixEnd_7478556 : Nat := 4983230072969 + 3 ^ 40 * 7478556 * 2
def baseEnd_7478556 : Nat := 3840093829565747348956753

theorem tailTrace_7478556 : CollatzResearch.WordTrace tailWord_7478556 prefixEnd_7478556 3840093829565747348956753 := by
  unfold tailWord_7478556
  simp only [CollatzResearch.WordTrace]
  refine ⟨136382672947238161261991761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181843563929650881682655681 136382672947238161261991761)
  ·
    refine ⟨102287004710428620946493821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136382672947238161261991761 102287004710428620946493821)
    ·
      refine ⟨38357626766410732854935183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102287004710428620946493821 38357626766410732854935183)
      ·
        refine ⟨57536440149616099282402775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38357626766410732854935183 57536440149616099282402775)
        ·
          refine ⟨86304660224424148923604163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57536440149616099282402775 86304660224424148923604163)
          ·
            refine ⟨129456990336636223385406245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86304660224424148923604163 129456990336636223385406245)
            ·
              refine ⟨24273185688119291884763671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129456990336636223385406245 24273185688119291884763671)
              ·
                refine ⟨36409778532178937827145507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24273185688119291884763671 36409778532178937827145507)
                ·
                  refine ⟨54614667798268406740718261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36409778532178937827145507 54614667798268406740718261)
                  ·
                    refine ⟨5120125106087663131942337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54614667798268406740718261 5120125106087663131942337)
                    ·
                      refine ⟨3840093829565747348956753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120125106087663131942337 3840093829565747348956753)
                      ·
                        rfl

theorem cell23_7478556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7478556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478556 prefixEnd_7478556 := by exact prefixLift 7478556
  have htrace : WordTrace (prefixWord ++ tailWord_7478556) baseStart_7478556 baseEnd_7478556 := by
    simpa [prefixWord, tailWord_7478556, baseEnd_7478556] using wordTrace_append hprefix tailTrace_7478556
  have hstable : (prefixWord ++ tailWord_7478556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478556).length < 2 ^ (prefixWord ++ tailWord_7478556).sum := by decide
  have hdescent : baseEnd_7478556 < baseStart_7478556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478599 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_7478599 : Nat := 118140960795 + 7478599 * 2 ^ 59
def prefixEnd_7478599 : Nat := 4983230072969 + 3 ^ 40 * 7478599 * 2
def baseEnd_7478599 : Nat := 3840115909233890680719055

theorem tailTrace_7478599 : CollatzResearch.WordTrace tailWord_7478599 prefixEnd_7478599 3840115909233890680719055 := by
  unfold tailWord_7478599
  simp only [CollatzResearch.WordTrace]
  refine ⟨272766914233320540867798851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181844609488880360578532567 272766914233320540867798851)
  ·
    refine ⟨409150371349980811301698277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272766914233320540867798851 409150371349980811301698277)
    ·
      refine ⟨76715694628121402119068427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409150371349980811301698277 76715694628121402119068427)
      ·
        refine ⟨115073541942182103178602641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76715694628121402119068427 115073541942182103178602641)
        ·
          refine ⟨86305156456636577383951981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115073541942182103178602641 86305156456636577383951981)
          ·
            refine ⟨32364433671238716518981993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86305156456636577383951981 32364433671238716518981993)
            ·
              refine ⟨24273325253429037389236495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32364433671238716518981993 24273325253429037389236495)
              ·
                refine ⟨36409987880143556083854743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24273325253429037389236495 36409987880143556083854743)
                ·
                  refine ⟨54614981820215334125782115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36409987880143556083854743 54614981820215334125782115)
                  ·
                    refine ⟨81922472730323001188673173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54614981820215334125782115 81922472730323001188673173)
                    ·
                      refine ⟨3840115909233890680719055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81922472730323001188673173 3840115909233890680719055)
                      ·
                        rfl

theorem cell23_7478599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_7478599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478599 prefixEnd_7478599 := by exact prefixLift 7478599
  have htrace : WordTrace (prefixWord ++ tailWord_7478599) baseStart_7478599 baseEnd_7478599 := by
    simpa [prefixWord, tailWord_7478599, baseEnd_7478599] using wordTrace_append hprefix tailTrace_7478599
  have hstable : (prefixWord ++ tailWord_7478599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478599).length < 2 ^ (prefixWord ++ tailWord_7478599).sum := by decide
  have hdescent : baseEnd_7478599 < baseStart_7478599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478606 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_7478606 : Nat := 118140960795 + 7478606 * 2 ^ 59
def prefixEnd_7478606 : Nat := 4983230072969 + 3 ^ 40 * 7478606 * 2
def baseEnd_7478606 : Nat := 3840119503598472153331523

theorem tailTrace_7478606 : CollatzResearch.WordTrace tailWord_7478606 prefixEnd_7478606 3840119503598472153331523 := by
  unfold tailWord_7478606
  simp only [CollatzResearch.WordTrace]
  refine ⟨34095896193036897632912959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181844779696196787375535781 34095896193036897632912959)
  ·
    refine ⟨51143844289555346449369439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34095896193036897632912959 51143844289555346449369439)
    ·
      refine ⟨76715766434333019674054159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51143844289555346449369439 76715766434333019674054159)
      ·
        refine ⟨115073649651499529511081239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76715766434333019674054159 115073649651499529511081239)
        ·
          refine ⟨172610474477249294266621859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115073649651499529511081239 172610474477249294266621859)
          ·
            refine ⟨258915711715873941399932789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172610474477249294266621859 258915711715873941399932789)
            ·
              refine ⟨24273347973363182006243699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258915711715873941399932789 24273347973363182006243699)
              ·
                refine ⟨36410021960044773009365549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24273347973363182006243699 36410021960044773009365549)
                ·
                  refine ⟨13653758235016789878512081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36410021960044773009365549 13653758235016789878512081)
                  ·
                    refine ⟨10240318676262592408884061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13653758235016789878512081 10240318676262592408884061)
                    ·
                      refine ⟨3840119503598472153331523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240318676262592408884061 3840119503598472153331523)
                      ·
                        rfl

theorem cell23_7478606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_7478606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478606 prefixEnd_7478606 := by exact prefixLift 7478606
  have htrace : WordTrace (prefixWord ++ tailWord_7478606) baseStart_7478606 baseEnd_7478606 := by
    simpa [prefixWord, tailWord_7478606, baseEnd_7478606] using wordTrace_append hprefix tailTrace_7478606
  have hstable : (prefixWord ++ tailWord_7478606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478606).length < 2 ^ (prefixWord ++ tailWord_7478606).sum := by decide
  have hdescent : baseEnd_7478606 < baseStart_7478606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478637 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7478637 : Nat := 118140960795 + 7478637 * 2 ^ 59
def prefixEnd_7478637 : Nat := 4983230072969 + 3 ^ 40 * 7478637 * 2
def baseEnd_7478637 : Nat := 3840135421498761532043881

theorem tailTrace_7478637 : CollatzResearch.WordTrace tailWord_7478637 prefixEnd_7478637 3840135421498761532043881 := by
  unfold tailWord_7478637
  simp only [CollatzResearch.WordTrace]
  refine ⟨272768300207182873357682165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181845533471455248905121443 272768300207182873357682165)
  ·
    refine ⟨25572028144423394377282703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272768300207182873357682165 25572028144423394377282703)
    ·
      refine ⟨38358042216635091565924055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25572028144423394377282703 38358042216635091565924055)
      ·
        refine ⟨57537063324952637348886083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38358042216635091565924055 57537063324952637348886083)
        ·
          refine ⟨86305594987428956023329125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57537063324952637348886083 86305594987428956023329125)
          ·
            refine ⟨16182299060142929254374211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86305594987428956023329125 16182299060142929254374211)
            ·
              refine ⟨24273448590214393881561317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16182299060142929254374211 24273448590214393881561317)
              ·
                refine ⟨4551271610665198852792747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24273448590214393881561317 4551271610665198852792747)
                ·
                  refine ⟨6826907415997798279189121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551271610665198852792747 6826907415997798279189121)
                  ·
                    refine ⟨5120180561998348709391841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826907415997798279189121 5120180561998348709391841)
                    ·
                      refine ⟨3840135421498761532043881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120180561998348709391841 3840135421498761532043881)
                      ·
                        rfl

theorem cell23_7478637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7478637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478637 prefixEnd_7478637 := by exact prefixLift 7478637
  have htrace : WordTrace (prefixWord ++ tailWord_7478637) baseStart_7478637 baseEnd_7478637 := by
    simpa [prefixWord, tailWord_7478637, baseEnd_7478637] using wordTrace_append hprefix tailTrace_7478637
  have hstable : (prefixWord ++ tailWord_7478637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478637).length < 2 ^ (prefixWord ++ tailWord_7478637).sum := by decide
  have hdescent : baseEnd_7478637 < baseStart_7478637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478653 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_7478653 : Nat := 118140960795 + 7478653 * 2 ^ 59
def prefixEnd_7478653 : Nat := 4983230072969 + 3 ^ 40 * 7478653 * 2
def baseEnd_7478653 : Nat := 3840143637189233469443807

theorem tailTrace_7478653 : CollatzResearch.WordTrace tailWord_7478653 prefixEnd_7478653 3840143637189233469443807 := by
  unfold tailWord_7478653
  simp only [CollatzResearch.WordTrace]
  refine ⟨272768883775124908090264613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181845922516749938726843075 272768883775124908090264613)
  ·
    refine ⟨51144165707835920266924615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272768883775124908090264613 51144165707835920266924615)
    ·
      refine ⟨76716248561753880400386923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51144165707835920266924615 76716248561753880400386923)
      ·
        refine ⟨115074372842630820600580385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76716248561753880400386923 115074372842630820600580385)
        ·
          refine ⟨86305779631973115450435289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115074372842630820600580385 86305779631973115450435289)
          ·
            refine ⟨64729334723979836587826467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86305779631973115450435289 64729334723979836587826467)
            ·
              refine ⟨97094002085969754881739701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64729334723979836587826467 97094002085969754881739701)
              ·
                refine ⟨9102562695559664520163097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97094002085969754881739701 9102562695559664520163097)
                ·
                  refine ⟨6826922021669748390122323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9102562695559664520163097 6826922021669748390122323)
                  ·
                    refine ⟨10240383032504622585183485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826922021669748390122323 10240383032504622585183485)
                    ·
                      refine ⟨3840143637189233469443807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240383032504622585183485 3840143637189233469443807)
                      ·
                        rfl

theorem cell23_7478653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_7478653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478653 prefixEnd_7478653 := by exact prefixLift 7478653
  have htrace : WordTrace (prefixWord ++ tailWord_7478653) baseStart_7478653 baseEnd_7478653 := by
    simpa [prefixWord, tailWord_7478653, baseEnd_7478653] using wordTrace_append hprefix tailTrace_7478653
  have hstable : (prefixWord ++ tailWord_7478653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478653).length < 2 ^ (prefixWord ++ tailWord_7478653).sum := by decide
  have hdescent : baseEnd_7478653 < baseStart_7478653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478654 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7478654 : Nat := 118140960795 + 7478654 * 2 ^ 59
def prefixEnd_7478654 : Nat := 4983230072969 + 3 ^ 40 * 7478654 * 2
def baseEnd_7478654 : Nat := 3840144150669887965531303

theorem tailTrace_7478654 : CollatzResearch.WordTrace tailWord_7478654 prefixEnd_7478654 3840144150669887965531303 := by
  unfold tailWord_7478654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34096115031015160657631377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181845946832080856840700677 34096115031015160657631377)
  ·
    refine ⟨25572086273261370493223533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34096115031015160657631377 25572086273261370493223533)
    ·
      refine ⟨9589532352473013934958825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25572086273261370493223533 9589532352473013934958825)
      ·
        refine ⟨7192149264354760451219119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9589532352473013934958825 7192149264354760451219119)
        ·
          refine ⟨10788223896532140676828679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7192149264354760451219119 10788223896532140676828679)
          ·
            refine ⟨16182335844798211015243019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10788223896532140676828679 16182335844798211015243019)
            ·
              refine ⟨24273503767197316522864529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16182335844798211015243019 24273503767197316522864529)
              ·
                refine ⟨18205127825397987392148397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24273503767197316522864529 18205127825397987392148397)
                ·
                  refine ⟨6826922934524245272055649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18205127825397987392148397 6826922934524245272055649)
                  ·
                    refine ⟨5120192200893183954041737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826922934524245272055649 5120192200893183954041737)
                    ·
                      refine ⟨3840144150669887965531303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120192200893183954041737 3840144150669887965531303)
                      ·
                        rfl

theorem cell23_7478654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7478654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478654 prefixEnd_7478654 := by exact prefixLift 7478654
  have htrace : WordTrace (prefixWord ++ tailWord_7478654) baseStart_7478654 baseEnd_7478654 := by
    simpa [prefixWord, tailWord_7478654, baseEnd_7478654] using wordTrace_append hprefix tailTrace_7478654
  have hstable : (prefixWord ++ tailWord_7478654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478654).length < 2 ^ (prefixWord ++ tailWord_7478654).sum := by decide
  have hdescent : baseEnd_7478654 < baseStart_7478654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478663 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_7478663 : Nat := 118140960795 + 7478663 * 2 ^ 59
def prefixEnd_7478663 : Nat := 4983230072969 + 3 ^ 40 * 7478663 * 2
def baseEnd_7478663 : Nat := 3840148771995778430318761

theorem tailTrace_7478663 : CollatzResearch.WordTrace tailWord_7478663 prefixEnd_7478663 3840148771995778430318761 := by
  unfold tailWord_7478663
  simp only [CollatzResearch.WordTrace]
  refine ⟨272769248505088679798128643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181846165670059119865419095 272769248505088679798128643)
  ·
    refine ⟨409153872757633019697192965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272769248505088679798128643 409153872757633019697192965)
    ·
      refine ⟨76716351142056191193223681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409153872757633019697192965 76716351142056191193223681)
      ·
        refine ⟨57537263356542143394917761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76716351142056191193223681 57537263356542143394917761)
        ·
          refine ⟨43152947517406607546188321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57537263356542143394917761 43152947517406607546188321)
          ·
            refine ⟨32364710638054955659641241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43152947517406607546188321 32364710638054955659641241)
            ·
              refine ⟨24273532978541216744730931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32364710638054955659641241 24273532978541216744730931)
              ·
                refine ⟨36410299467811825117096397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24273532978541216744730931 36410299467811825117096397)
                ·
                  refine ⟨13653862300429434418911149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36410299467811825117096397 13653862300429434418911149)
                  ·
                    refine ⟨5120198362661037907091681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13653862300429434418911149 5120198362661037907091681)
                    ·
                      refine ⟨3840148771995778430318761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120198362661037907091681 3840148771995778430318761)
                      ·
                        rfl

theorem cell23_7478663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_7478663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478663 prefixEnd_7478663 := by exact prefixLift 7478663
  have htrace : WordTrace (prefixWord ++ tailWord_7478663) baseStart_7478663 baseEnd_7478663 := by
    simpa [prefixWord, tailWord_7478663, baseEnd_7478663] using wordTrace_append hprefix tailTrace_7478663
  have hstable : (prefixWord ++ tailWord_7478663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478663).length < 2 ^ (prefixWord ++ tailWord_7478663).sum := by decide
  have hdescent : baseEnd_7478663 < baseStart_7478663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478674 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7478674 : Nat := 118140960795 + 7478674 * 2 ^ 59
def prefixEnd_7478674 : Nat := 4983230072969 + 3 ^ 40 * 7478674 * 2
def baseEnd_7478674 : Nat := 3840154420282977887281211

theorem tailTrace_7478674 : CollatzResearch.WordTrace tailWord_7478674 prefixEnd_7478674 3840154420282977887281211 := by
  unfold tailWord_7478674
  simp only [CollatzResearch.WordTrace]
  refine ⟨68192412427012207169194769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181846433138699219117852717 68192412427012207169194769)
  ·
    refine ⟨51144309320259155376896077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68192412427012207169194769 51144309320259155376896077)
    ·
      refine ⟨19179115995097183266336029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51144309320259155376896077 19179115995097183266336029)
      ·
        refine ⟨7192168498161443724876011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19179115995097183266336029 7192168498161443724876011)
        ·
          refine ⟨10788252747242165587314017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7192168498161443724876011 10788252747242165587314017)
          ·
            refine ⟨8091189560431624190485513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10788252747242165587314017 8091189560431624190485513)
            ·
              refine ⟨6068392170323718142864135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8091189560431624190485513 6068392170323718142864135)
              ·
                refine ⟨9102588255485577214296203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068392170323718142864135 9102588255485577214296203)
                ·
                  refine ⟨13653882383228365821444305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102588255485577214296203 13653882383228365821444305)
                  ·
                    refine ⟨10240411787421274366083229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13653882383228365821444305 10240411787421274366083229)
                    ·
                      refine ⟨3840154420282977887281211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240411787421274366083229 3840154420282977887281211)
                      ·
                        rfl

theorem cell23_7478674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7478674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478674 prefixEnd_7478674 := by exact prefixLift 7478674
  have htrace : WordTrace (prefixWord ++ tailWord_7478674) baseStart_7478674 baseEnd_7478674 := by
    simpa [prefixWord, tailWord_7478674, baseEnd_7478674] using wordTrace_append hprefix tailTrace_7478674
  have hstable : (prefixWord ++ tailWord_7478674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478674).length < 2 ^ (prefixWord ++ tailWord_7478674).sum := by decide
  have hdescent : baseEnd_7478674 < baseStart_7478674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478679 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7478679 : Nat := 118140960795 + 7478679 * 2 ^ 59
def prefixEnd_7478679 : Nat := 4983230072969 + 3 ^ 40 * 7478679 * 2
def baseEnd_7478679 : Nat := 3840156987686250367718687

theorem tailTrace_7478679 : CollatzResearch.WordTrace tailWord_7478679 prefixEnd_7478679 3840156987686250367718687 := by
  unfold tailWord_7478679
  simp only [CollatzResearch.WordTrace]
  refine ⟨272769832073030714530711091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181846554715353809687140727 272769832073030714530711091)
  ·
    refine ⟨409154748109546071796066637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272769832073030714530711091 409154748109546071796066637)
    ·
      refine ⟨153433030541079776923524989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409154748109546071796066637 153433030541079776923524989)
      ·
        refine ⟨57537386452904916346321871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153433030541079776923524989 57537386452904916346321871)
        ·
          refine ⟨86306079679357374519482807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57537386452904916346321871 86306079679357374519482807)
          ·
            refine ⟨129459119519036061779224211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86306079679357374519482807 129459119519036061779224211)
            ·
              refine ⟨194188679278554092668836317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129459119519036061779224211 194188679278554092668836317)
              ·
                refine ⟨72820754729457784750813619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194188679278554092668836317 72820754729457784750813619)
                ·
                  refine ⟨109231132094186677126220429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72820754729457784750813619 109231132094186677126220429)
                  ·
                    refine ⟨40961674535320003922332661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109231132094186677126220429 40961674535320003922332661)
                    ·
                      refine ⟨3840156987686250367718687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40961674535320003922332661 3840156987686250367718687)
                      ·
                        rfl

theorem cell23_7478679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7478679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478679 prefixEnd_7478679 := by exact prefixLift 7478679
  have htrace : WordTrace (prefixWord ++ tailWord_7478679) baseStart_7478679 baseEnd_7478679 := by
    simpa [prefixWord, tailWord_7478679, baseEnd_7478679] using wordTrace_append hprefix tailTrace_7478679
  have hstable : (prefixWord ++ tailWord_7478679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478679).length < 2 ^ (prefixWord ++ tailWord_7478679).sum := by decide
  have hdescent : baseEnd_7478679 < baseStart_7478679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478722 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7478722 : Nat := 118140960795 + 7478722 * 2 ^ 59
def prefixEnd_7478722 : Nat := 4983230072969 + 3 ^ 40 * 7478722 * 2
def baseEnd_7478722 : Nat := 3840179067354393699480991

theorem tailTrace_7478722 : CollatzResearch.WordTrace tailWord_7478722 prefixEnd_7478722 3840179067354393699480991 := by
  unfold tailWord_7478722
  simp only [CollatzResearch.WordTrace]
  refine ⟨68192850102968733218631605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181847600274583288583017613 68192850102968733218631605)
  ·
    refine ⟨6393079697153318739246713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68192850102968733218631605 6393079697153318739246713)
    ·
      refine ⟨4794809772864989054435035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6393079697153318739246713 4794809772864989054435035)
      ·
        refine ⟨7192214659297483581652553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794809772864989054435035 7192214659297483581652553)
        ·
          refine ⟨5394160994473112686239415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192214659297483581652553 5394160994473112686239415)
          ·
            refine ⟨8091241491709669029359123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394160994473112686239415 8091241491709669029359123)
            ·
              refine ⟨12136862237564503544038685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091241491709669029359123 12136862237564503544038685)
              ·
                refine ⟨4551323339086688829014507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12136862237564503544038685 4551323339086688829014507)
                ·
                  refine ⟨6826985008630033243521761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551323339086688829014507 6826985008630033243521761)
                  ·
                    refine ⟨5120238756472524932641321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6826985008630033243521761 5120238756472524932641321)
                    ·
                      refine ⟨3840179067354393699480991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120238756472524932641321 3840179067354393699480991)
                      ·
                        rfl

theorem cell23_7478722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7478722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478722 prefixEnd_7478722 := by exact prefixLift 7478722
  have htrace : WordTrace (prefixWord ++ tailWord_7478722) baseStart_7478722 baseEnd_7478722 := by
    simpa [prefixWord, tailWord_7478722, baseEnd_7478722] using wordTrace_append hprefix tailTrace_7478722
  have hstable : (prefixWord ++ tailWord_7478722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478722).length < 2 ^ (prefixWord ++ tailWord_7478722).sum := by decide
  have hdescent : baseEnd_7478722 < baseStart_7478722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478746 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_7478746 : Nat := 118140960795 + 7478746 * 2 ^ 59
def prefixEnd_7478746 : Nat := 4983230072969 + 3 ^ 40 * 7478746 * 2
def baseEnd_7478746 : Nat := 1280063796963367201860293

theorem tailTrace_7478746 : CollatzResearch.WordTrace tailWord_7478746 prefixEnd_7478746 1280063796963367201860293 := by
  unfold tailWord_7478746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68193068940946996243350023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181848183842525323315600061 68193068940946996243350023)
  ·
    refine ⟨102289603411420494365025035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68193068940946996243350023 102289603411420494365025035)
    ·
      refine ⟨153434405117130741547537553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102289603411420494365025035 153434405117130741547537553)
      ·
        refine ⟨115075803837848056160653165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153434405117130741547537553 115075803837848056160653165)
        ·
          refine ⟨43153426439193021060244937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115075803837848056160653165 43153426439193021060244937)
          ·
            refine ⟨32365069829394765795183703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43153426439193021060244937 32365069829394765795183703)
            ·
              refine ⟨48547604744092148692775555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32365069829394765795183703 48547604744092148692775555)
              ·
                refine ⟨72821407116138223039163333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48547604744092148692775555 72821407116138223039163333)
                ·
                  refine ⟨13654013834275916819843125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72821407116138223039163333 13654013834275916819843125)
                  ·
                    refine ⟨1280063796963367201860293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13654013834275916819843125 1280063796963367201860293)
                    ·
                      rfl

theorem cell23_7478746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_7478746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478746 prefixEnd_7478746 := by exact prefixLift 7478746
  have htrace : WordTrace (prefixWord ++ tailWord_7478746) baseStart_7478746 baseEnd_7478746 := by
    simpa [prefixWord, tailWord_7478746, baseEnd_7478746] using wordTrace_append hprefix tailTrace_7478746
  have hstable : (prefixWord ++ tailWord_7478746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478746).length < 2 ^ (prefixWord ++ tailWord_7478746).sum := by decide
  have hdescent : baseEnd_7478746 < baseStart_7478746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478803 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3]
def baseStart_7478803 : Nat := 118140960795 + 7478803 * 2 ^ 59
def prefixEnd_7478803 : Nat := 4983230072969 + 3 ^ 40 * 7478803 * 2
def baseEnd_7478803 : Nat := 3840220659287407882568117

theorem tailTrace_7478803 : CollatzResearch.WordTrace tailWord_7478803 prefixEnd_7478803 3840220659287407882568117 := by
  unfold tailWord_7478803
  simp only [CollatzResearch.WordTrace]
  refine ⟨272774354724581483708225063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181849569816387655805483375 272774354724581483708225063)
  ·
    refine ⟨409161532086872225562337595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272774354724581483708225063 409161532086872225562337595)
    ·
      refine ⟨613742298130308338343506393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409161532086872225562337595 613742298130308338343506393)
      ·
        refine ⟨460306723597731253757629795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613742298130308338343506393 460306723597731253757629795)
        ·
          refine ⟨690460085396596880636444693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460306723597731253757629795 690460085396596880636444693)
          ·
            refine ⟨32365316502965478779833345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 690460085396596880636444693 32365316502965478779833345)
            ·
              refine ⟨24273987377224109084875009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32365316502965478779833345 24273987377224109084875009)
              ·
                refine ⟨18205490532918081813656257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24273987377224109084875009 18205490532918081813656257)
                ·
                  refine ⟨13654117899688561360242193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18205490532918081813656257 13654117899688561360242193)
                  ·
                    refine ⟨10240588424766421020181645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13654117899688561360242193 10240588424766421020181645)
                    ·
                      refine ⟨3840220659287407882568117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240588424766421020181645 3840220659287407882568117)
                      ·
                        rfl

theorem cell23_7478803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_7478803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478803 prefixEnd_7478803 := by exact prefixLift 7478803
  have htrace : WordTrace (prefixWord ++ tailWord_7478803) baseStart_7478803 baseEnd_7478803 := by
    simpa [prefixWord, tailWord_7478803, baseEnd_7478803] using wordTrace_append hprefix tailTrace_7478803
  have hstable : (prefixWord ++ tailWord_7478803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478803).length < 2 ^ (prefixWord ++ tailWord_7478803).sum := by decide
  have hdescent : baseEnd_7478803 < baseStart_7478803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478853 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_7478853 : Nat := 118140960795 + 7478853 * 2 ^ 59
def prefixEnd_7478853 : Nat := 4983230072969 + 3 ^ 40 * 7478853 * 2
def baseEnd_7478853 : Nat := 1280082111106710895647629

theorem tailTrace_7478853 : CollatzResearch.WordTrace tailWord_7478853 prefixEnd_7478853 1280082111106710895647629 := by
  unfold tailWord_7478853
  simp only [CollatzResearch.WordTrace]
  refine ⟨272776178374400342247545213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181850785582933561498363475 272776178374400342247545213)
  ·
    refine ⟨102291066890400128342829455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272776178374400342247545213 102291066890400128342829455)
    ·
      refine ⟨153436600335600192514244183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102291066890400128342829455 153436600335600192514244183)
      ·
        refine ⟨230154900503400288771366275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153436600335600192514244183 230154900503400288771366275)
        ·
          refine ⟨345232350755100433157049413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230154900503400288771366275 345232350755100433157049413)
          ·
            refine ⟨64731065766581331216946765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345232350755100433157049413 64731065766581331216946765)
            ·
              refine ⟨24274149662467999206355037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64731065766581331216946765 24274149662467999206355037)
              ·
                refine ⟨9102806123425499702383139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24274149662467999206355037 9102806123425499702383139)
                ·
                  refine ⟨13654209185138249553574709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102806123425499702383139 13654209185138249553574709)
                  ·
                    refine ⟨1280082111106710895647629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13654209185138249553574709 1280082111106710895647629)
                    ·
                      rfl

theorem cell23_7478853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_7478853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478853 prefixEnd_7478853 := by exact prefixLift 7478853
  have htrace : WordTrace (prefixWord ++ tailWord_7478853) baseStart_7478853 baseEnd_7478853 := by
    simpa [prefixWord, tailWord_7478853, baseEnd_7478853] using wordTrace_append hprefix tailTrace_7478853
  have hstable : (prefixWord ++ tailWord_7478853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478853).length < 2 ^ (prefixWord ++ tailWord_7478853).sum := by decide
  have hdescent : baseEnd_7478853 < baseStart_7478853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478883 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 1, 6]
def baseStart_7478883 : Nat := 118140960795 + 7478883 * 2 ^ 59
def prefixEnd_7478883 : Nat := 4983230072969 + 3 ^ 40 * 7478883 * 2
def baseEnd_7478883 : Nat := 1280087245913255856522583

theorem tailTrace_7478883 : CollatzResearch.WordTrace tailWord_7478883 prefixEnd_7478883 1280087245913255856522583 := by
  unfold tailWord_7478883
  simp only [CollatzResearch.WordTrace]
  refine ⟨272777272564291657371137303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181851515042861104914091535 272777272564291657371137303)
  ·
    refine ⟨409165908846437486056705955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272777272564291657371137303 409165908846437486056705955)
    ·
      refine ⟨613748863269656229085058933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409165908846437486056705955 613748863269656229085058933)
      ·
        refine ⟨57538955931530271476724275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 613748863269656229085058933 57538955931530271476724275)
        ·
          refine ⟨86308433897295407215086413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57538955931530271476724275 86308433897295407215086413)
          ·
            refine ⟨32365662711485777705657405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86308433897295407215086413 32365662711485777705657405)
            ·
              refine ⟨12137123516807166639621527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32365662711485777705657405 12137123516807166639621527)
              ·
                refine ⟨18205685275210749959432291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137123516807166639621527 18205685275210749959432291)
                ·
                  refine ⟨27308527912816124939148437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18205685275210749959432291 27308527912816124939148437)
                  ·
                    refine ⟨1280087245913255856522583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27308527912816124939148437 1280087245913255856522583)
                    ·
                      rfl

theorem cell23_7478883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 6].length) (baseStart_7478883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478883 prefixEnd_7478883 := by exact prefixLift 7478883
  have htrace : WordTrace (prefixWord ++ tailWord_7478883) baseStart_7478883 baseEnd_7478883 := by
    simpa [prefixWord, tailWord_7478883, baseEnd_7478883] using wordTrace_append hprefix tailTrace_7478883
  have hstable : (prefixWord ++ tailWord_7478883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478883).length < 2 ^ (prefixWord ++ tailWord_7478883).sum := by decide
  have hdescent : baseEnd_7478883 < baseStart_7478883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478890 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_7478890 : Nat := 118140960795 + 7478890 * 2 ^ 59
def prefixEnd_7478890 : Nat := 4983230072969 + 3 ^ 40 * 7478890 * 2
def baseEnd_7478890 : Nat := 3840265332104349042180217

theorem tailTrace_7478890 : CollatzResearch.WordTrace tailWord_7478890 prefixEnd_7478890 3840265332104349042180217 := by
  unfold tailWord_7478890
  simp only [CollatzResearch.WordTrace]
  refine ⟨68194381968816574391660531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181851685250177531711094749 68194381968816574391660531)
  ·
    refine ⟨102291572953224861587490797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68194381968816574391660531 102291572953224861587490797)
    ·
      refine ⟨38359339857459323095309049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102291572953224861587490797 38359339857459323095309049)
      ·
        refine ⟨28769504893094492321481787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38359339857459323095309049 28769504893094492321481787)
        ·
          refine ⟨43154257339641738482222681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28769504893094492321481787 43154257339641738482222681)
          ·
            refine ⟨32365693004731303861667011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43154257339641738482222681 32365693004731303861667011)
            ·
              refine ⟨48548539507096955792500517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32365693004731303861667011 48548539507096955792500517)
              ·
                refine ⟨9102851157580679211093847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48548539507096955792500517 9102851157580679211093847)
                ·
                  refine ⟨13654276736371018816640771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102851157580679211093847 13654276736371018816640771)
                  ·
                    refine ⟨20481415104556528224961157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13654276736371018816640771 20481415104556528224961157)
                    ·
                      refine ⟨3840265332104349042180217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20481415104556528224961157 3840265332104349042180217)
                      ·
                        rfl

theorem cell23_7478890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_7478890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478890 prefixEnd_7478890 := by exact prefixLift 7478890
  have htrace : WordTrace (prefixWord ++ tailWord_7478890) baseStart_7478890 baseEnd_7478890 := by
    simpa [prefixWord, tailWord_7478890, baseEnd_7478890] using wordTrace_append hprefix tailTrace_7478890
  have hstable : (prefixWord ++ tailWord_7478890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478890).length < 2 ^ (prefixWord ++ tailWord_7478890).sum := by decide
  have hdescent : baseEnd_7478890 < baseStart_7478890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478901 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7478901 : Nat := 118140960795 + 7478901 * 2 ^ 59
def prefixEnd_7478901 : Nat := 4983230072969 + 3 ^ 40 * 7478901 * 2
def baseEnd_7478901 : Nat := 3840270980391548499142667

theorem tailTrace_7478901 : CollatzResearch.WordTrace tailWord_7478901 prefixEnd_7478901 3840270980391548499142667 := by
  unfold tailWord_7478901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272777929078226446445292557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181851952718817630963528371 272777929078226446445292557)
  ·
    refine ⟨102291723404334917416984709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272777929078226446445292557 102291723404334917416984709)
    ·
      refine ⟨19179698138312797015684633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102291723404334917416984709 19179698138312797015684633)
      ·
        refine ⟨14384773603734597761763475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19179698138312797015684633 14384773603734597761763475)
        ·
          refine ⟨21577160405601896642645213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14384773603734597761763475 21577160405601896642645213)
          ·
            refine ⟨8091435152100711240991955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21577160405601896642645213 8091435152100711240991955)
            ·
              refine ⟨12137152728151066861487933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091435152100711240991955 12137152728151066861487933)
              ·
                refine ⟨4551432273056650073057975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12137152728151066861487933 4551432273056650073057975)
                ·
                  refine ⟨6827148409584975109586963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551432273056650073057975 6827148409584975109586963)
                  ·
                    refine ⟨10240722614377462664380445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827148409584975109586963 10240722614377462664380445)
                    ·
                      refine ⟨3840270980391548499142667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240722614377462664380445 3840270980391548499142667)
                      ·
                        rfl

theorem cell23_7478901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7478901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478901 prefixEnd_7478901 := by exact prefixLift 7478901
  have htrace : WordTrace (prefixWord ++ tailWord_7478901) baseStart_7478901 baseEnd_7478901 := by
    simpa [prefixWord, tailWord_7478901, baseEnd_7478901] using wordTrace_append hprefix tailTrace_7478901
  have hstable : (prefixWord ++ tailWord_7478901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478901).length < 2 ^ (prefixWord ++ tailWord_7478901).sum := by decide
  have hdescent : baseEnd_7478901 < baseStart_7478901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478913 : List Nat := [1, 2, 4, 2, 1, 4, 9]
def baseStart_7478913 : Nat := 118140960795 + 7478913 * 2 ^ 59
def prefixEnd_7478913 : Nat := 4983230072969 + 3 ^ 40 * 7478913 * 2
def baseEnd_7478913 : Nat := 47410828915548178422131

theorem tailTrace_7478913 : CollatzResearch.WordTrace tailWord_7478913 prefixEnd_7478913 47410828915548178422131 := by
  unfold tailWord_7478913
  simp only [CollatzResearch.WordTrace]
  refine ⟨272778366754182972494729393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181852244502788648329819595 272778366754182972494729393)
  ·
    refine ⟨204583775065637229371047045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272778366754182972494729393 204583775065637229371047045)
    ·
      refine ⟨38359457824806980507071321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204583775065637229371047045 38359457824806980507071321)
      ·
        refine ⟨28769593368605235380303491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38359457824806980507071321 28769593368605235380303491)
        ·
          refine ⟨43154390052907853070455237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28769593368605235380303491 43154390052907853070455237)
          ·
            refine ⟨8091448134920222450710357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43154390052907853070455237 8091448134920222450710357)
            ·
              refine ⟨47410828915548178422131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8091448134920222450710357 47410828915548178422131)
              ·
                rfl

theorem cell23_7478913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 9].length) (baseStart_7478913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478913 prefixEnd_7478913 := by exact prefixLift 7478913
  have htrace : WordTrace (prefixWord ++ tailWord_7478913) baseStart_7478913 baseEnd_7478913 := by
    simpa [prefixWord, tailWord_7478913, baseEnd_7478913] using wordTrace_append hprefix tailTrace_7478913
  have hstable : (prefixWord ++ tailWord_7478913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478913).length < 2 ^ (prefixWord ++ tailWord_7478913).sum := by decide
  have hdescent : baseEnd_7478913 < baseStart_7478913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478930 : List Nat := [3, 2, 3, 1, 3, 1, 2, 8]
def baseStart_7478930 : Nat := 118140960795 + 7478930 * 2 ^ 59
def prefixEnd_7478930 : Nat := 4983230072969 + 3 ^ 40 * 7478930 * 2
def baseEnd_7478930 : Nat := 142232810049278847617779

theorem tailTrace_7478930 : CollatzResearch.WordTrace tailWord_7478930 prefixEnd_7478930 142232810049278847617779 := by
  unfold tailWord_7478930
  simp only [CollatzResearch.WordTrace]
  refine ⟨68194746698780346099524561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181852657863414256265398829 68194746698780346099524561)
  ·
    refine ⟨51146060024085259574643421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68194746698780346099524561 51146060024085259574643421)
    ·
      refine ⟨19179772509031972340491283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51146060024085259574643421 19179772509031972340491283)
      ·
        refine ⟨28769658763547958510736925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19179772509031972340491283 28769658763547958510736925)
        ·
          refine ⟨10788622036330484441526347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28769658763547958510736925 10788622036330484441526347)
          ·
            refine ⟨16182933054495726662289521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10788622036330484441526347 16182933054495726662289521)
            ·
              refine ⟨12137199790871794996717141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16182933054495726662289521 12137199790871794996717141)
              ·
                refine ⟨142232810049278847617779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12137199790871794996717141 142232810049278847617779)
                ·
                  rfl

theorem cell23_7478930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_7478930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478930 prefixEnd_7478930 := by exact prefixLift 7478930
  have htrace : WordTrace (prefixWord ++ tailWord_7478930) baseStart_7478930 baseEnd_7478930 := by
    simpa [prefixWord, tailWord_7478930, baseEnd_7478930] using wordTrace_append hprefix tailTrace_7478930
  have hstable : (prefixWord ++ tailWord_7478930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478930).length < 2 ^ (prefixWord ++ tailWord_7478930).sum := by decide
  have hdescent : baseEnd_7478930 < baseStart_7478930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478973 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_7478973 : Nat := 118140960795 + 7478973 * 2 ^ 59
def prefixEnd_7478973 : Nat := 4983230072969 + 3 ^ 40 * 7478973 * 2
def baseEnd_7478973 : Nat := 1280102650332890739147445

theorem tailTrace_7478973 : CollatzResearch.WordTrace tailWord_7478973 prefixEnd_7478973 1280102650332890739147445 := by
  unfold tailWord_7478973
  simp only [CollatzResearch.WordTrace]
  refine ⟨272780555133965602741913573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181853703422643735161275715 272780555133965602741913573)
  ·
    refine ⟨51146354087618550514108795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272780555133965602741913573 51146354087618550514108795)
    ·
      refine ⟨76719531131427825771163193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51146354087618550514108795 76719531131427825771163193)
      ·
        refine ⟨57539648348570869328372395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76719531131427825771163193 57539648348570869328372395)
        ·
          refine ⟨86309472522856303992558593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57539648348570869328372395 86309472522856303992558593)
          ·
            refine ⟨64732104392142227994418945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86309472522856303992558593 64732104392142227994418945)
            ·
              refine ⟨48549078294106670995814209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64732104392142227994418945 48549078294106670995814209)
              ·
                refine ⟨36411808720580003246860657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48549078294106670995814209 36411808720580003246860657)
                ·
                  refine ⟨27308856540435002435145493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36411808720580003246860657 27308856540435002435145493)
                  ·
                    refine ⟨1280102650332890739147445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27308856540435002435145493 1280102650332890739147445)
                    ·
                      rfl

theorem cell23_7478973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_7478973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478973 prefixEnd_7478973 := by exact prefixLift 7478973
  have htrace : WordTrace (prefixWord ++ tailWord_7478973) baseStart_7478973 baseEnd_7478973 := by
    simpa [prefixWord, tailWord_7478973, baseEnd_7478973] using wordTrace_append hprefix tailTrace_7478973
  have hstable : (prefixWord ++ tailWord_7478973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478973).length < 2 ^ (prefixWord ++ tailWord_7478973).sum := by decide
  have hdescent : baseEnd_7478973 < baseStart_7478973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478974 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_7478974 : Nat := 118140960795 + 7478974 * 2 ^ 59
def prefixEnd_7478974 : Nat := 4983230072969 + 3 ^ 40 * 7478974 * 2
def baseEnd_7478974 : Nat := 3840308464479326713529831

theorem tailTrace_7478974 : CollatzResearch.WordTrace tailWord_7478974 prefixEnd_7478974 3840308464479326713529831 := by
  unfold tailWord_7478974
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097573950870247489087497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181853727737974653275133317 34097573950870247489087497)
  ·
    refine ⟨25573180463152685616815623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34097573950870247489087497 25573180463152685616815623)
    ·
      refine ⟨38359770694729028425223435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25573180463152685616815623 38359770694729028425223435)
      ·
        refine ⟨57539656042093542637835153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38359770694729028425223435 57539656042093542637835153)
        ·
          refine ⟨43154742031570156978376365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57539656042093542637835153 43154742031570156978376365)
          ·
            refine ⟨16183028261838808866891137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43154742031570156978376365 16183028261838808866891137)
            ·
              refine ⟨12137271196379106650168353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183028261838808866891137 12137271196379106650168353)
              ·
                refine ⟨9102953397284329987626265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12137271196379106650168353 9102953397284329987626265)
                ·
                  refine ⟨6827215047963247490719699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9102953397284329987626265 6827215047963247490719699)
                  ·
                    refine ⟨10240822571944871236079549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827215047963247490719699 10240822571944871236079549)
                    ·
                      refine ⟨3840308464479326713529831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240822571944871236079549 3840308464479326713529831)
                      ·
                        rfl

theorem cell23_7478974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_7478974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478974 prefixEnd_7478974 := by exact prefixLift 7478974
  have htrace : WordTrace (prefixWord ++ tailWord_7478974) baseStart_7478974 baseEnd_7478974 := by
    simpa [prefixWord, tailWord_7478974, baseEnd_7478974] using wordTrace_append hprefix tailTrace_7478974
  have hstable : (prefixWord ++ tailWord_7478974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478974).length < 2 ^ (prefixWord ++ tailWord_7478974).sum := by decide
  have hdescent : baseEnd_7478974 < baseStart_7478974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478983 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_7478983 : Nat := 118140960795 + 7478983 * 2 ^ 59
def prefixEnd_7478983 : Nat := 4983230072969 + 3 ^ 40 * 7478983 * 2
def baseEnd_7478983 : Nat := 3840313085805217178317289

theorem tailTrace_7478983 : CollatzResearch.WordTrace tailWord_7478983 prefixEnd_7478983 3840313085805217178317289 := by
  unfold tailWord_7478983
  simp only [CollatzResearch.WordTrace]
  refine ⟨272780919863929374449777603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181853946575952916299851735 272780919863929374449777603)
  ·
    refine ⟨409171379795894061674666405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272780919863929374449777603 409171379795894061674666405)
    ·
      refine ⟨76719633711730136563999951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409171379795894061674666405 76719633711730136563999951)
      ·
        refine ⟨115079450567595204845999927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76719633711730136563999951 115079450567595204845999927)
        ·
          refine ⟨172619175851392807268999891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115079450567595204845999927 172619175851392807268999891)
          ·
            refine ⟨258928763777089210903499837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172619175851392807268999891 258928763777089210903499837)
            ·
              refine ⟨97098286416408454088812439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258928763777089210903499837 97098286416408454088812439)
              ·
                refine ⟨145647429624612681133218659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97098286416408454088812439 145647429624612681133218659)
                ·
                  refine ⟨218471144436919021699827989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145647429624612681133218659 218471144436919021699827989)
                  ·
                    refine ⟨10240834895480579142179437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218471144436919021699827989 10240834895480579142179437)
                    ·
                      refine ⟨3840313085805217178317289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10240834895480579142179437 3840313085805217178317289)
                      ·
                        rfl

theorem cell23_7478983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_7478983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478983 prefixEnd_7478983 := by exact prefixLift 7478983
  have htrace : WordTrace (prefixWord ++ tailWord_7478983) baseStart_7478983 baseEnd_7478983 := by
    simpa [prefixWord, tailWord_7478983, baseEnd_7478983] using wordTrace_append hprefix tailTrace_7478983
  have hstable : (prefixWord ++ tailWord_7478983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478983).length < 2 ^ (prefixWord ++ tailWord_7478983).sum := by decide
  have hdescent : baseEnd_7478983 < baseStart_7478983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7478993 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_7478993 : Nat := 118140960795 + 7478993 * 2 ^ 59
def prefixEnd_7478993 : Nat := 4983230072969 + 3 ^ 40 * 7478993 * 2
def baseEnd_7478993 : Nat := 3840318220611762139192243

theorem tailTrace_7478993 : CollatzResearch.WordTrace tailWord_7478993 prefixEnd_7478993 3840318220611762139192243 := by
  unfold tailWord_7478993
  simp only [CollatzResearch.WordTrace]
  refine ⟨272781284593893146157641633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181854189729262097438427755 272781284593893146157641633)
  ·
    refine ⟨204585963445419859618231225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272781284593893146157641633 204585963445419859618231225)
    ·
      refine ⟨153439472584064894713673419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204585963445419859618231225 153439472584064894713673419)
      ·
        refine ⟨230159208876097342070510129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153439472584064894713673419 230159208876097342070510129)
        ·
          refine ⟨172619406657073006552882597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230159208876097342070510129 172619406657073006552882597)
          ·
            refine ⟨32366138748201188728665487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172619406657073006552882597 32366138748201188728665487)
            ·
              refine ⟨48549208122301783092998231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32366138748201188728665487 48549208122301783092998231)
              ·
                refine ⟨72823812183452674639497347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48549208122301783092998231 72823812183452674639497347)
                ·
                  refine ⟨109235718275179011959246021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72823812183452674639497347 109235718275179011959246021)
                  ·
                    refine ⟨20481697176596064742358629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109235718275179011959246021 20481697176596064742358629)
                    ·
                      refine ⟨3840318220611762139192243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20481697176596064742358629 3840318220611762139192243)
                      ·
                        rfl

theorem cell23_7478993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_7478993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7478993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7478993 prefixEnd_7478993 := by exact prefixLift 7478993
  have htrace : WordTrace (prefixWord ++ tailWord_7478993) baseStart_7478993 baseEnd_7478993 := by
    simpa [prefixWord, tailWord_7478993, baseEnd_7478993] using wordTrace_append hprefix tailTrace_7478993
  have hstable : (prefixWord ++ tailWord_7478993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7478993).length < 2 ^ (prefixWord ++ tailWord_7478993).sum := by decide
  have hdescent : baseEnd_7478993 < baseStart_7478993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7478993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479020 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 5]
def baseStart_7479020 : Nat := 118140960795 + 7479020 * 2 ^ 59
def prefixEnd_7479020 : Nat := 4983230072969 + 3 ^ 40 * 7479020 * 2
def baseEnd_7479020 : Nat := 426703564954381503728291

theorem tailTrace_7479020 : CollatzResearch.WordTrace tailWord_7479020 prefixEnd_7479020 426703564954381503728291 := by
  unfold tailWord_7479020
  simp only [CollatzResearch.WordTrace]
  refine ⟨136391134682397664884437257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181854846243196886512583009 136391134682397664884437257)
  ·
    refine ⟨102293351011798248663327943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136391134682397664884437257 102293351011798248663327943)
    ·
      refine ⟨153440026517697372994991915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102293351011798248663327943 153440026517697372994991915)
      ·
        refine ⟨230160039776546059492487873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153440026517697372994991915 230160039776546059492487873)
        ·
          refine ⟨172620029832409544619365905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230160039776546059492487873 172620029832409544619365905)
          ·
            refine ⟨129465022374307158464524429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172620029832409544619365905 129465022374307158464524429)
            ·
              refine ⟨48549383390365184424196661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129465022374307158464524429 48549383390365184424196661)
              ·
                refine ⟨4551504692846736039768437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48549383390365184424196661 4551504692846736039768437)
                ·
                  refine ⟨426703564954381503728291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4551504692846736039768437 426703564954381503728291)
                  ·
                    rfl

theorem cell23_7479020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_7479020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479020 prefixEnd_7479020 := by exact prefixLift 7479020
  have htrace : WordTrace (prefixWord ++ tailWord_7479020) baseStart_7479020 baseEnd_7479020 := by
    simpa [prefixWord, tailWord_7479020, baseEnd_7479020] using wordTrace_append hprefix tailTrace_7479020
  have hstable : (prefixWord ++ tailWord_7479020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479020).length < 2 ^ (prefixWord ++ tailWord_7479020).sum := by decide
  have hdescent : baseEnd_7479020 < baseStart_7479020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479043 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_7479043 : Nat := 118140960795 + 7479043 * 2 ^ 59
def prefixEnd_7479043 : Nat := 4983230072969 + 3 ^ 40 * 7479043 * 2
def baseEnd_7479043 : Nat := 3840343894644486943567013

theorem tailTrace_7479043 : CollatzResearch.WordTrace tailWord_7479043 prefixEnd_7479043 3840343894644486943567013 := by
  unfold tailWord_7479043
  simp only [CollatzResearch.WordTrace]
  refine ⟨272783108243712004696961783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181855405495808003131307855 272783108243712004696961783)
  ·
    refine ⟨409174662365568007045442675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272783108243712004696961783 409174662365568007045442675)
    ·
      refine ⟨613761993548352010568164013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409174662365568007045442675 613761993548352010568164013)
      ·
        refine ⟨230160747580632003963061505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613761993548352010568164013 230160747580632003963061505)
        ·
          refine ⟨172620560685474002972296129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230160747580632003963061505 172620560685474002972296129)
          ·
            refine ⟨129465420514105502229222097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172620560685474002972296129 129465420514105502229222097)
            ·
              refine ⟨97099065385579126671916573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129465420514105502229222097 97099065385579126671916573)
              ·
                refine ⟨36412149519592172501968715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97099065385579126671916573 36412149519592172501968715)
                ·
                  refine ⟨54618224279388258752953073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36412149519592172501968715 54618224279388258752953073)
                  ·
                    refine ⟨40963668209541194064714805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54618224279388258752953073 40963668209541194064714805)
                    ·
                      refine ⟨3840343894644486943567013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40963668209541194064714805 3840343894644486943567013)
                      ·
                        rfl

theorem cell23_7479043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_7479043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479043 prefixEnd_7479043 := by exact prefixLift 7479043
  have htrace : WordTrace (prefixWord ++ tailWord_7479043) baseStart_7479043 baseEnd_7479043 := by
    simpa [prefixWord, tailWord_7479043, baseEnd_7479043] using wordTrace_append hprefix tailTrace_7479043
  have hstable : (prefixWord ++ tailWord_7479043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479043).length < 2 ^ (prefixWord ++ tailWord_7479043).sum := by decide
  have hdescent : baseEnd_7479043 < baseStart_7479043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479083 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_7479083 : Nat := 118140960795 + 7479083 * 2 ^ 59
def prefixEnd_7479083 : Nat := 4983230072969 + 3 ^ 40 * 7479083 * 2
def baseEnd_7479083 : Nat := 3840364433870666787066829

theorem tailTrace_7479083 : CollatzResearch.WordTrace tailWord_7479083 prefixEnd_7479083 3840364433870666787066829 := by
  unfold tailWord_7479083
  simp only [CollatzResearch.WordTrace]
  refine ⟨272784567163567091528417903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181856378109044727685611935 272784567163567091528417903)
  ·
    refine ⟨409176850745350637292626855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272784567163567091528417903 409176850745350637292626855)
    ·
      refine ⟨613765276118025955938940283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409176850745350637292626855 613765276118025955938940283)
      ·
        refine ⟨920647914177038933908410425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613765276118025955938940283 920647914177038933908410425)
        ·
          refine ⟨690485935632779200431307819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920647914177038933908410425 690485935632779200431307819)
          ·
            refine ⟨1035728903449168800646961729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690485935632779200431307819 1035728903449168800646961729)
            ·
              refine ⟨776796677586876600485221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035728903449168800646961729 776796677586876600485221297)
              ·
                refine ⟨582597508190157450363915973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776796677586876600485221297 582597508190157450363915973)
                ·
                  refine ⟨109237032785654521943234245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582597508190157450363915973 109237032785654521943234245)
                  ·
                    refine ⟨20481943647310222864356421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109237032785654521943234245 20481943647310222864356421)
                    ·
                      refine ⟨3840364433870666787066829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20481943647310222864356421 3840364433870666787066829)
                      ·
                        rfl

theorem cell23_7479083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_7479083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479083 prefixEnd_7479083 := by exact prefixLift 7479083
  have htrace : WordTrace (prefixWord ++ tailWord_7479083) baseStart_7479083 baseEnd_7479083 := by
    simpa [prefixWord, tailWord_7479083, baseEnd_7479083] using wordTrace_append hprefix tailTrace_7479083
  have hstable : (prefixWord ++ tailWord_7479083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479083).length < 2 ^ (prefixWord ++ tailWord_7479083).sum := by decide
  have hdescent : baseEnd_7479083 < baseStart_7479083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479124 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_7479124 : Nat := 118140960795 + 7479124 * 2 ^ 59
def prefixEnd_7479124 : Nat := 4983230072969 + 3 ^ 40 * 7479124 * 2
def baseEnd_7479124 : Nat := 3840385486577501126654141

theorem tailTrace_7479124 : CollatzResearch.WordTrace tailWord_7479124 prefixEnd_7479124 3840385486577501126654141 := by
  unfold tailWord_7479124
  simp only [CollatzResearch.WordTrace]
  refine ⟨136393031278209277765330213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181857375037612370353773617 136393031278209277765330213)
  ·
    refine ⟨25573693364664239580999415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136393031278209277765330213 25573693364664239580999415)
    ·
      refine ⟨38360540046996359371499123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25573693364664239580999415 38360540046996359371499123)
      ·
        refine ⟨57540810070494539057248685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38360540046996359371499123 57540810070494539057248685)
        ·
          refine ⟨21577803776435452146468257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57540810070494539057248685 21577803776435452146468257)
          ·
            refine ⟨16183352832326589109851193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21577803776435452146468257 16183352832326589109851193)
            ·
              refine ⟨12137514624244941832388395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183352832326589109851193 12137514624244941832388395)
              ·
                refine ⟨18206271936367412748582593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137514624244941832388395 18206271936367412748582593)
                ·
                  refine ⟨13654703952275559561436945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18206271936367412748582593 13654703952275559561436945)
                  ·
                    refine ⟨10241027964206669671077709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13654703952275559561436945 10241027964206669671077709)
                    ·
                      refine ⟨3840385486577501126654141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241027964206669671077709 3840385486577501126654141)
                      ·
                        rfl

theorem cell23_7479124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_7479124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479124 prefixEnd_7479124 := by exact prefixLift 7479124
  have htrace : WordTrace (prefixWord ++ tailWord_7479124) baseStart_7479124 baseEnd_7479124 := by
    simpa [prefixWord, tailWord_7479124, baseEnd_7479124] using wordTrace_append hprefix tailTrace_7479124
  have hstable : (prefixWord ++ tailWord_7479124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479124).length < 2 ^ (prefixWord ++ tailWord_7479124).sum := by decide
  have hdescent : baseEnd_7479124 < baseStart_7479124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479177 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_7479177 : Nat := 118140960795 + 7479177 * 2 ^ 59
def prefixEnd_7479177 : Nat := 4983230072969 + 3 ^ 40 * 7479177 * 2
def baseEnd_7479177 : Nat := 3840412701052189419291397

theorem tailTrace_7479177 : CollatzResearch.WordTrace tailWord_7479177 prefixEnd_7479177 3840412701052189419291397 := by
  unfold tailWord_7479177
  simp only [CollatzResearch.WordTrace]
  refine ⟨272787995625226545582339785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181858663750151030388226523 272787995625226545582339785)
  ·
    refine ⟨204590996718919909186754839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272787995625226545582339785 204590996718919909186754839)
    ·
      refine ⟨306886495078379863780132259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204590996718919909186754839 306886495078379863780132259)
      ·
        refine ⟨460329742617569795670198389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306886495078379863780132259 460329742617569795670198389)
        ·
          refine ⟨43155913370397168344081099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460329742617569795670198389 43155913370397168344081099)
          ·
            refine ⟨64733870055595752516121649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43155913370397168344081099 64733870055595752516121649)
            ·
              refine ⟨48550402541696814387091237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64733870055595752516121649 48550402541696814387091237)
              ·
                refine ⟨9103200476568152697579607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48550402541696814387091237 9103200476568152697579607)
                ·
                  refine ⟨13654800714852229046369411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103200476568152697579607 13654800714852229046369411)
                  ·
                    refine ⟨20482201072278343569554117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13654800714852229046369411 20482201072278343569554117)
                    ·
                      refine ⟨3840412701052189419291397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20482201072278343569554117 3840412701052189419291397)
                      ·
                        rfl

theorem cell23_7479177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_7479177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479177 prefixEnd_7479177 := by exact prefixLift 7479177
  have htrace : WordTrace (prefixWord ++ tailWord_7479177) baseStart_7479177 baseEnd_7479177 := by
    simpa [prefixWord, tailWord_7479177, baseEnd_7479177] using wordTrace_append hprefix tailTrace_7479177
  have hstable : (prefixWord ++ tailWord_7479177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479177).length < 2 ^ (prefixWord ++ tailWord_7479177).sum := by decide
  have hdescent : baseEnd_7479177 < baseStart_7479177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479188 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7479188 : Nat := 118140960795 + 7479188 * 2 ^ 59
def prefixEnd_7479188 : Nat := 4983230072969 + 3 ^ 40 * 7479188 * 2
def baseEnd_7479188 : Nat := 3840418349339388876253847

theorem tailTrace_7479188 : CollatzResearch.WordTrace tailWord_7479188 prefixEnd_7479188 3840418349339388876253847 := by
  unfold tailWord_7479188
  simp only [CollatzResearch.WordTrace]
  refine ⟨136394198414093347230495109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181858931218791129640660145 136394198414093347230495109)
  ·
    refine ⟨25573912202642502605717833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136394198414093347230495109 25573912202642502605717833)
    ·
      refine ⟨19180434151981876954288375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25573912202642502605717833 19180434151981876954288375)
      ·
        refine ⟨28770651227972815431432563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19180434151981876954288375 28770651227972815431432563)
        ·
          refine ⟨43155976841959223147148845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28770651227972815431432563 43155976841959223147148845)
          ·
            refine ⟨16183491315734708680180817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43155976841959223147148845 16183491315734708680180817)
            ·
              refine ⟨12137618486801031510135613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183491315734708680180817 12137618486801031510135613)
              ·
                refine ⟨4551606932550386816300855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12137618486801031510135613 4551606932550386816300855)
                ·
                  refine ⟨6827410398825580224451283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551606932550386816300855 6827410398825580224451283)
                  ·
                    refine ⟨10241115598238370336676925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827410398825580224451283 10241115598238370336676925)
                    ·
                      refine ⟨3840418349339388876253847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241115598238370336676925 3840418349339388876253847)
                      ·
                        rfl

theorem cell23_7479188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7479188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479188 prefixEnd_7479188 := by exact prefixLift 7479188
  have htrace : WordTrace (prefixWord ++ tailWord_7479188) baseStart_7479188 baseEnd_7479188 := by
    simpa [prefixWord, tailWord_7479188, baseEnd_7479188] using wordTrace_append hprefix tailTrace_7479188
  have hstable : (prefixWord ++ tailWord_7479188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479188).length < 2 ^ (prefixWord ++ tailWord_7479188).sum := by decide
  have hdescent : baseEnd_7479188 < baseStart_7479188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479194 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7479194 : Nat := 118140960795 + 7479194 * 2 ^ 59
def prefixEnd_7479194 : Nat := 4983230072969 + 3 ^ 40 * 7479194 * 2
def baseEnd_7479194 : Nat := 3840421430223315852778819

theorem tailTrace_7479194 : CollatzResearch.WordTrace tailWord_7479194 prefixEnd_7479194 3840421430223315852778819 := by
  unfold tailWord_7479194
  simp only [CollatzResearch.WordTrace]
  refine ⟨68197153916541239371427159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181859077110776638323805757 68197153916541239371427159)
  ·
    refine ⟨102295730874811859057140739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68197153916541239371427159 102295730874811859057140739)
    ·
      refine ⟨153443596312217788585711109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102295730874811859057140739 153443596312217788585711109)
      ·
        refine ⟨28770674308540835359820833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153443596312217788585711109 28770674308540835359820833)
        ·
          refine ⟨21578005731405626519865625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28770674308540835359820833 21578005731405626519865625)
          ·
            refine ⟨16183504298554219889899219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21578005731405626519865625 16183504298554219889899219)
            ·
              refine ⟨24275256447831329834848829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16183504298554219889899219 24275256447831329834848829)
              ·
                refine ⟨9103221167936748688068311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24275256447831329834848829 9103221167936748688068311)
                ·
                  refine ⟨13654831751905123032102467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103221167936748688068311 13654831751905123032102467)
                  ·
                    refine ⟨20482247627857684548153701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13654831751905123032102467 20482247627857684548153701)
                    ·
                      refine ⟨3840421430223315852778819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20482247627857684548153701 3840421430223315852778819)
                      ·
                        rfl

theorem cell23_7479194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7479194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479194 prefixEnd_7479194 := by exact prefixLift 7479194
  have htrace : WordTrace (prefixWord ++ tailWord_7479194) baseStart_7479194 baseEnd_7479194 := by
    simpa [prefixWord, tailWord_7479194, baseEnd_7479194] using wordTrace_append hprefix tailTrace_7479194
  have hstable : (prefixWord ++ tailWord_7479194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479194).length < 2 ^ (prefixWord ++ tailWord_7479194).sum := by decide
  have hdescent : baseEnd_7479194 < baseStart_7479194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479204 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_7479204 : Nat := 118140960795 + 7479204 * 2 ^ 59
def prefixEnd_7479204 : Nat := 4983230072969 + 3 ^ 40 * 7479204 * 2
def baseEnd_7479204 : Nat := 1280142188343286937884591

theorem tailTrace_7479204 : CollatzResearch.WordTrace tailWord_7479204 prefixEnd_7479204 1280142188343286937884591 := by
  unfold tailWord_7479204
  simp only [CollatzResearch.WordTrace]
  refine ⟨136394490198064364596786333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181859320264085819462381777 136394490198064364596786333)
  ·
    refine ⟨51147933824274136723794875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136394490198064364596786333 51147933824274136723794875)
    ·
      refine ⟨76721900736411205085692313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51147933824274136723794875 76721900736411205085692313)
      ·
        refine ⟨57541425552308403814269235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76721900736411205085692313 57541425552308403814269235)
        ·
          refine ⟨86312138328462605721403853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57541425552308403814269235 86312138328462605721403853)
          ·
            refine ⟨32367051873173477145526445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86312138328462605721403853 32367051873173477145526445)
            ·
              refine ⟨12137644452440053929572417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32367051873173477145526445 12137644452440053929572417)
              ·
                refine ⟨9103233339330040447179313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12137644452440053929572417 9103233339330040447179313)
                ·
                  refine ⟨6827425004497530335384485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9103233339330040447179313 6827425004497530335384485)
                  ·
                    refine ⟨1280142188343286937884591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827425004497530335384485 1280142188343286937884591)
                    ·
                      rfl

theorem cell23_7479204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_7479204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479204 prefixEnd_7479204 := by exact prefixLift 7479204
  have htrace : WordTrace (prefixWord ++ tailWord_7479204) baseStart_7479204 baseEnd_7479204 := by
    simpa [prefixWord, tailWord_7479204, baseEnd_7479204] using wordTrace_append hprefix tailTrace_7479204
  have hstable : (prefixWord ++ tailWord_7479204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479204).length < 2 ^ (prefixWord ++ tailWord_7479204).sum := by decide
  have hdescent : baseEnd_7479204 < baseStart_7479204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479221 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7479221 : Nat := 118140960795 + 7479221 * 2 ^ 59
def prefixEnd_7479221 : Nat := 4983230072969 + 3 ^ 40 * 7479221 * 2
def baseEnd_7479221 : Nat := 1280145098066995749047065

theorem tailTrace_7479221 : CollatzResearch.WordTrace tailWord_7479221 prefixEnd_7479221 1280145098066995749047065 := by
  unfold tailWord_7479221
  simp only [CollatzResearch.WordTrace]
  refine ⟨272789600437067141096941517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181859733624711427397961011 272789600437067141096941517)
  ·
    refine ⟨102296100163900177911353069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272789600437067141096941517 102296100163900177911353069)
    ·
      refine ⟨38361037561462566716757401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102296100163900177911353069 38361037561462566716757401)
      ·
        refine ⟨28770778171096925037568051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38361037561462566716757401 28770778171096925037568051)
        ·
          refine ⟨43156167256645387556352077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28770778171096925037568051 43156167256645387556352077)
          ·
            refine ⟨16183562721242020333632029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43156167256645387556352077 16183562721242020333632029)
            ·
              refine ⟨6068836020465757625112011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16183562721242020333632029 6068836020465757625112011)
              ·
                refine ⟨9103254030698636437668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068836020465757625112011 9103254030698636437668017)
                ·
                  refine ⟨6827440523023977328251013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9103254030698636437668017 6827440523023977328251013)
                  ·
                    refine ⟨1280145098066995749047065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827440523023977328251013 1280145098066995749047065)
                    ·
                      rfl

theorem cell23_7479221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7479221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479221 prefixEnd_7479221 := by exact prefixLift 7479221
  have htrace : WordTrace (prefixWord ++ tailWord_7479221) baseStart_7479221 baseEnd_7479221 := by
    simpa [prefixWord, tailWord_7479221, baseEnd_7479221] using wordTrace_append hprefix tailTrace_7479221
  have hstable : (prefixWord ++ tailWord_7479221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479221).length < 2 ^ (prefixWord ++ tailWord_7479221).sum := by decide
  have hdescent : baseEnd_7479221 < baseStart_7479221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479227 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 3]
def baseStart_7479227 : Nat := 118140960795 + 7479227 * 2 ^ 59
def prefixEnd_7479227 : Nat := 4983230072969 + 3 ^ 40 * 7479227 * 2
def baseEnd_7479227 : Nat := 3840438375084914223666167

theorem tailTrace_7479227 : CollatzResearch.WordTrace tailWord_7479227 prefixEnd_7479227 3840438375084914223666167 := by
  unfold tailWord_7479227
  simp only [CollatzResearch.WordTrace]
  refine ⟨272789819275045404121659935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181859879516696936081106623 272789819275045404121659935)
  ·
    refine ⟨409184728912568106182489903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272789819275045404121659935 409184728912568106182489903)
    ·
      refine ⟨613777093368852159273734855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409184728912568106182489903 613777093368852159273734855)
      ·
        refine ⟨920665640053278238910602283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613777093368852159273734855 920665640053278238910602283)
        ·
          refine ⟨1380998460079917358365903425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920665640053278238910602283 1380998460079917358365903425)
          ·
            refine ⟨1035748845059938018774427569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380998460079917358365903425 1035748845059938018774427569)
            ·
              refine ⟨776811633794953514080820677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035748845059938018774427569 776811633794953514080820677)
              ·
                refine ⟨145652181336553783890153877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 776811633794953514080820677 145652181336553783890153877)
                ·
                  refine ⟨6827446000150958619850963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145652181336553783890153877 6827446000150958619850963)
                  ·
                    refine ⟨10241169000226437929776445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827446000150958619850963 10241169000226437929776445)
                    ·
                      refine ⟨3840438375084914223666167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241169000226437929776445 3840438375084914223666167)
                      ·
                        rfl

theorem cell23_7479227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 3].length) (baseStart_7479227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479227 prefixEnd_7479227 := by exact prefixLift 7479227
  have htrace : WordTrace (prefixWord ++ tailWord_7479227) baseStart_7479227 baseEnd_7479227 := by
    simpa [prefixWord, tailWord_7479227, baseEnd_7479227] using wordTrace_append hprefix tailTrace_7479227
  have hstable : (prefixWord ++ tailWord_7479227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479227).length < 2 ^ (prefixWord ++ tailWord_7479227).sum := by decide
  have hdescent : baseEnd_7479227 < baseStart_7479227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479244 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7479244 : Nat := 118140960795 + 7479244 * 2 ^ 59
def prefixEnd_7479244 : Nat := 4983230072969 + 3 ^ 40 * 7479244 * 2
def baseEnd_7479244 : Nat := 3840447104256040657153589

theorem tailTrace_7479244 : CollatzResearch.WordTrace tailWord_7479244 prefixEnd_7479244 3840447104256040657153589 := by
  unfold tailWord_7479244
  simp only [CollatzResearch.WordTrace]
  refine ⟨136395219657991908012514393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181860292877322544016685857 136395219657991908012514393)
  ·
    refine ⟨102296414743493931009385795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136395219657991908012514393 102296414743493931009385795)
    ·
      refine ⟨153444622115240896514078693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102296414743493931009385795 153444622115240896514078693)
      ·
        refine ⟨28770866646607668096389755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153444622115240896514078693 28770866646607668096389755)
        ·
          refine ⟨43156299969911502144584633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28770866646607668096389755 43156299969911502144584633)
          ·
            refine ⟨32367224977433626608438475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43156299969911502144584633 32367224977433626608438475)
            ·
              refine ⟨48550837466150439912657713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32367224977433626608438475 48550837466150439912657713)
              ·
                refine ⟨36413128099612829934493285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48550837466150439912657713 36413128099612829934493285)
                ·
                  refine ⟨6827461518677405612717491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36413128099612829934493285 6827461518677405612717491)
                  ·
                    refine ⟨10241192278016108419076237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827461518677405612717491 10241192278016108419076237)
                    ·
                      refine ⟨3840447104256040657153589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241192278016108419076237 3840447104256040657153589)
                      ·
                        rfl

theorem cell23_7479244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7479244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479244 prefixEnd_7479244 := by exact prefixLift 7479244
  have htrace : WordTrace (prefixWord ++ tailWord_7479244) baseStart_7479244 baseEnd_7479244 := by
    simpa [prefixWord, tailWord_7479244, baseEnd_7479244] using wordTrace_append hprefix tailTrace_7479244
  have hstable : (prefixWord ++ tailWord_7479244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479244).length < 2 ^ (prefixWord ++ tailWord_7479244).sum := by decide
  have hdescent : baseEnd_7479244 < baseStart_7479244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479278 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_7479278 : Nat := 118140960795 + 7479278 * 2 ^ 59
def prefixEnd_7479278 : Nat := 4983230072969 + 3 ^ 40 * 7479278 * 2
def baseEnd_7479278 : Nat := 3840464562598293524128433

theorem tailTrace_7479278 : CollatzResearch.WordTrace tailWord_7479278 prefixEnd_7479278 3840464562598293524128433 := by
  unfold tailWord_7479278
  simp only [CollatzResearch.WordTrace]
  refine ⟨34098959924732579978970811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181861119598573759887844325 34098959924732579978970811)
  ·
    refine ⟨51148439887098869968456217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34098959924732579978970811 51148439887098869968456217)
    ·
      refine ⟨38361329915324152476342163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51148439887098869968456217 38361329915324152476342163)
      ·
        refine ⟨57541994872986228714513245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38361329915324152476342163 57541994872986228714513245)
        ·
          refine ⟨21578248077369835767942467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57541994872986228714513245 21578248077369835767942467)
          ·
            refine ⟨32367372116054753651913701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21578248077369835767942467 32367372116054753651913701)
            ·
              refine ⟨6068882271760266309733819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32367372116054753651913701 6068882271760266309733819)
              ·
                refine ⟨9103323407640399464600729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068882271760266309733819 9103323407640399464600729)
                ·
                  refine ⟨6827492555730299598450547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9103323407640399464600729 6827492555730299598450547)
                  ·
                    refine ⟨10241238833595449397675821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827492555730299598450547 10241238833595449397675821)
                    ·
                      refine ⟨3840464562598293524128433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241238833595449397675821 3840464562598293524128433)
                      ·
                        rfl

theorem cell23_7479278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_7479278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479278 prefixEnd_7479278 := by exact prefixLift 7479278
  have htrace : WordTrace (prefixWord ++ tailWord_7479278) baseStart_7479278 baseEnd_7479278 := by
    simpa [prefixWord, tailWord_7479278, baseEnd_7479278] using wordTrace_append hprefix tailTrace_7479278
  have hstable : (prefixWord ++ tailWord_7479278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479278).length < 2 ^ (prefixWord ++ tailWord_7479278).sum := by decide
  have hdescent : baseEnd_7479278 < baseStart_7479278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479358 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_7479358 : Nat := 118140960795 + 7479358 * 2 ^ 59
def prefixEnd_7479358 : Nat := 4983230072969 + 3 ^ 40 * 7479358 * 2
def baseEnd_7479358 : Nat := 426722849005628134569785

theorem tailTrace_7479358 : CollatzResearch.WordTrace tailWord_7479358 prefixEnd_7479358 426722849005628134569785 := by
  unfold tailWord_7479358
  simp only [CollatzResearch.WordTrace]
  refine ⟨34099324654696351686834841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181863064825047208996452485 34099324654696351686834841)
  ·
    refine ⟨25574493491022263765126131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34099324654696351686834841 25574493491022263765126131)
    ·
      refine ⟨38361740236533395647689197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25574493491022263765126131 38361740236533395647689197)
      ·
        refine ⟨14385652588700023367883449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38361740236533395647689197 14385652588700023367883449)
        ·
          refine ⟨10789239441525017525912587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14385652588700023367883449 10789239441525017525912587)
          ·
            refine ⟨16183859162287526288868881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10789239441525017525912587 16183859162287526288868881)
            ·
              refine ⟨12137894371715644716651661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183859162287526288868881 12137894371715644716651661)
              ·
                refine ⟨4551710389393366768744373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12137894371715644716651661 4551710389393366768744373)
                ·
                  refine ⟨426722849005628134569785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4551710389393366768744373 426722849005628134569785)
                  ·
                    rfl

theorem cell23_7479358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_7479358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479358 prefixEnd_7479358 := by exact prefixLift 7479358
  have htrace : WordTrace (prefixWord ++ tailWord_7479358) baseStart_7479358 baseEnd_7479358 := by
    simpa [prefixWord, tailWord_7479358, baseEnd_7479358] using wordTrace_append hprefix tailTrace_7479358
  have hstable : (prefixWord ++ tailWord_7479358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479358).length < 2 ^ (prefixWord ++ tailWord_7479358).sum := by decide
  have hdescent : baseEnd_7479358 < baseStart_7479358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479384 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_7479384 : Nat := 118140960795 + 7479384 * 2 ^ 59
def prefixEnd_7479384 : Nat := 4983230072969 + 3 ^ 40 * 7479384 * 2
def baseEnd_7479384 : Nat := 1280172997182556703134315

theorem tailTrace_7479384 : CollatzResearch.WordTrace tailWord_7479384 prefixEnd_7479384 1280172997182556703134315 := by
  unfold tailWord_7479384
  simp only [CollatzResearch.WordTrace]
  refine ⟨136397772767738309967562603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181863697023651079956750137 136397772767738309967562603)
  ·
    refine ⟨204596659151607464951343905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136397772767738309967562603 204596659151607464951343905)
    ·
      refine ⟨153447494363705598713507929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204596659151607464951343905 153447494363705598713507929)
      ·
        refine ⟨115085620772779199035130947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153447494363705598713507929 115085620772779199035130947)
        ·
          refine ⟨172628431159168798552696421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115085620772779199035130947 172628431159168798552696421)
          ·
            refine ⟨32367830842344149728630579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172628431159168798552696421 32367830842344149728630579)
            ·
              refine ⟨48551746263516224592945869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32367830842344149728630579 48551746263516224592945869)
              ·
                refine ⟨18206904848818584222354701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48551746263516224592945869 18206904848818584222354701)
                ·
                  refine ⟨6827589318306969083383013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18206904848818584222354701 6827589318306969083383013)
                  ·
                    refine ⟨1280172997182556703134315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827589318306969083383013 1280172997182556703134315)
                    ·
                      rfl

theorem cell23_7479384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_7479384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479384 prefixEnd_7479384 := by exact prefixLift 7479384
  have htrace : WordTrace (prefixWord ++ tailWord_7479384) baseStart_7479384 baseEnd_7479384 := by
    simpa [prefixWord, tailWord_7479384, baseEnd_7479384] using wordTrace_append hprefix tailTrace_7479384
  have hstable : (prefixWord ++ tailWord_7479384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479384).length < 2 ^ (prefixWord ++ tailWord_7479384).sum := by decide
  have hdescent : baseEnd_7479384 < baseStart_7479384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479414 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_7479414 : Nat := 118140960795 + 7479414 * 2 ^ 59
def prefixEnd_7479414 : Nat := 4983230072969 + 3 ^ 40 * 7479414 * 2
def baseEnd_7479414 : Nat := 426726043996367221336423

theorem tailTrace_7479414 : CollatzResearch.WordTrace tailWord_7479414 prefixEnd_7479414 426726043996367221336423 := by
  unfold tailWord_7479414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17049789982835495941169831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181864426483578623372478197 17049789982835495941169831)
  ·
    refine ⟨25574684974253243911754747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17049789982835495941169831 25574684974253243911754747)
    ·
      refine ⟨38362027461379865867632121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25574684974253243911754747 38362027461379865867632121)
      ·
        refine ⟨28771520596034899400724091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38362027461379865867632121 28771520596034899400724091)
        ·
          refine ⟨43157280894052349101086137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28771520596034899400724091 43157280894052349101086137)
          ·
            refine ⟨32367960670539261825814603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43157280894052349101086137 32367960670539261825814603)
            ·
              refine ⟨48551941005808892738721905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32367960670539261825814603 48551941005808892738721905)
              ·
                refine ⟨36413955754356669554041429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48551941005808892738721905 36413955754356669554041429)
                ·
                  refine ⟨426726043996367221336423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36413955754356669554041429 426726043996367221336423)
                  ·
                    rfl

theorem cell23_7479414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_7479414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479414 prefixEnd_7479414 := by exact prefixLift 7479414
  have htrace : WordTrace (prefixWord ++ tailWord_7479414) baseStart_7479414 baseEnd_7479414 := by
    simpa [prefixWord, tailWord_7479414, baseEnd_7479414] using wordTrace_append hprefix tailTrace_7479414
  have hstable : (prefixWord ++ tailWord_7479414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479414).length < 2 ^ (prefixWord ++ tailWord_7479414).sum := by decide
  have hdescent : baseEnd_7479414 < baseStart_7479414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479448 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 6]
def baseStart_7479448 : Nat := 118140960795 + 7479448 * 2 ^ 59
def prefixEnd_7479448 : Nat := 4983230072969 + 3 ^ 40 * 7479448 * 2
def baseEnd_7479448 : Nat := 426727983812173095444739

theorem tailTrace_7479448 : CollatzResearch.WordTrace tailWord_7479448 prefixEnd_7479448 426727983812173095444739 := by
  unfold tailWord_7479448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136398939903622379432727499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181865253204829839243636665 136398939903622379432727499)
  ·
    refine ⟨204598409855433569149091249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136398939903622379432727499 204598409855433569149091249)
    ·
      refine ⟨153448807391575176861818437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204598409855433569149091249 153448807391575176861818437)
      ·
        refine ⟨28771651385920345661590957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153448807391575176861818437 28771651385920345661590957)
        ·
          refine ⟨10789369269720129623096609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28771651385920345661590957 10789369269720129623096609)
          ·
            refine ⟨8092026952290097217322457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10789369269720129623096609 8092026952290097217322457)
            ·
              refine ⟨6069020214217572912991843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092026952290097217322457 6069020214217572912991843)
              ·
                refine ⟨9103530321326359369487765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069020214217572912991843 9103530321326359369487765)
                ·
                  refine ⟨426727983812173095444739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9103530321326359369487765 426727983812173095444739)
                  ·
                    rfl

theorem cell23_7479448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 6].length) (baseStart_7479448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479448 prefixEnd_7479448 := by exact prefixLift 7479448
  have htrace : WordTrace (prefixWord ++ tailWord_7479448) baseStart_7479448 baseEnd_7479448 := by
    simpa [prefixWord, tailWord_7479448, baseEnd_7479448] using wordTrace_append hprefix tailTrace_7479448
  have hstable : (prefixWord ++ tailWord_7479448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479448).length < 2 ^ (prefixWord ++ tailWord_7479448).sum := by decide
  have hdescent : baseEnd_7479448 < baseStart_7479448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479474 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_7479474 : Nat := 118140960795 + 7479474 * 2 ^ 59
def prefixEnd_7479474 : Nat := 4983230072969 + 3 ^ 40 * 7479474 * 2
def baseEnd_7479474 : Nat := 1280188401602191585759177

theorem tailTrace_7479474 : CollatzResearch.WordTrace tailWord_7479474 prefixEnd_7479474 1280188401602191585759177 := by
  unfold tailWord_7479474
  simp only [CollatzResearch.WordTrace]
  refine ⟨68199707026287641326475369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181865885403433710203934317 68199707026287641326475369)
  ·
    refine ⟨51149780269715730994856527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68199707026287641326475369 51149780269715730994856527)
    ·
      refine ⟨76724670404573596492284791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51149780269715730994856527 76724670404573596492284791)
      ·
        refine ⟨115087005606860394738427187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76724670404573596492284791 115087005606860394738427187)
        ·
          refine ⟨172630508410290592107640781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115087005606860394738427187 172630508410290592107640781)
          ·
            refine ⟨64736440653858972040365293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172630508410290592107640781 64736440653858972040365293)
            ·
              refine ⟨24276165245197114515136985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64736440653858972040365293 24276165245197114515136985)
              ·
                refine ⟨18207123933897835886352739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24276165245197114515136985 18207123933897835886352739)
                ·
                  refine ⟨27310685900846753829529109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18207123933897835886352739 27310685900846753829529109)
                  ·
                    refine ⟨1280188401602191585759177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27310685900846753829529109 1280188401602191585759177)
                    ·
                      rfl

theorem cell23_7479474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_7479474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479474 prefixEnd_7479474 := by exact prefixLift 7479474
  have htrace : WordTrace (prefixWord ++ tailWord_7479474) baseStart_7479474 baseEnd_7479474 := by
    simpa [prefixWord, tailWord_7479474, baseEnd_7479474] using wordTrace_append hprefix tailTrace_7479474
  have hstable : (prefixWord ++ tailWord_7479474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479474).length < 2 ^ (prefixWord ++ tailWord_7479474).sum := by decide
  have hdescent : baseEnd_7479474 < baseStart_7479474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479492 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_7479492 : Nat := 118140960795 + 7479492 * 2 ^ 59
def prefixEnd_7479492 : Nat := 4983230072969 + 3 ^ 40 * 7479492 * 2
def baseEnd_7479492 : Nat := 3840574447458355686852449

theorem tailTrace_7479492 : CollatzResearch.WordTrace tailWord_7479492 prefixEnd_7479492 3840574447458355686852449 := by
  unfold tailWord_7479492
  simp only [CollatzResearch.WordTrace]
  refine ⟨136399742309542677190028365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181866323079390236253371153 136399742309542677190028365)
  ·
    refine ⟨51149903366078503946260637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136399742309542677190028365 51149903366078503946260637)
    ·
      refine ⟨19181213762279438979847739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51149903366078503946260637 19181213762279438979847739)
      ·
        refine ⟨28771820643419158469771609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19181213762279438979847739 28771820643419158469771609)
        ·
          refine ⟨21578865482564368852328707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28771820643419158469771609 21578865482564368852328707)
          ·
            refine ⟨32368298223846553278493061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21578865482564368852328707 32368298223846553278493061)
            ·
              refine ⟨6069055916971228739717449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32368298223846553278493061 6069055916971228739717449)
              ·
                refine ⟨4551791937728421554788087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6069055916971228739717449 4551791937728421554788087)
                ·
                  refine ⟨6827687906592632332182131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551791937728421554788087 6827687906592632332182131)
                  ·
                    refine ⟨10241531859888948498273197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827687906592632332182131 10241531859888948498273197)
                    ·
                      refine ⟨3840574447458355686852449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241531859888948498273197 3840574447458355686852449)
                      ·
                        rfl

theorem cell23_7479492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_7479492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479492 prefixEnd_7479492 := by exact prefixLift 7479492
  have htrace : WordTrace (prefixWord ++ tailWord_7479492) baseStart_7479492 baseEnd_7479492 := by
    simpa [prefixWord, tailWord_7479492, baseEnd_7479492] using wordTrace_append hprefix tailTrace_7479492
  have hstable : (prefixWord ++ tailWord_7479492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479492).length < 2 ^ (prefixWord ++ tailWord_7479492).sum := by decide
  have hdescent : baseEnd_7479492 < baseStart_7479492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479497 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_7479497 : Nat := 118140960795 + 7479497 * 2 ^ 59
def prefixEnd_7479497 : Nat := 4983230072969 + 3 ^ 40 * 7479497 * 2
def baseEnd_7479497 : Nat := 3840577014861628167289925

theorem tailTrace_7479497 : CollatzResearch.WordTrace tailWord_7479497 prefixEnd_7479497 3840577014861628167289925 := by
  unfold tailWord_7479497
  simp only [CollatzResearch.WordTrace]
  refine ⟨272799666984067240233988745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181866444656044826822659163 272799666984067240233988745)
  ·
    refine ⟨204599750238050430175491559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272799666984067240233988745 204599750238050430175491559)
    ·
      refine ⟨306899625357075645263237339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204599750238050430175491559 306899625357075645263237339)
      ·
        refine ⟨460349438035613467894856009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306899625357075645263237339 460349438035613467894856009)
        ·
          refine ⟨345262078526710100921142007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460349438035613467894856009 345262078526710100921142007)
          ·
            refine ⟨517893117790065151381713011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345262078526710100921142007 517893117790065151381713011)
            ·
              refine ⟨776839676685097727072569517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517893117790065151381713011 776839676685097727072569517)
              ·
                refine ⟨291314878756911647652213569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776839676685097727072569517 291314878756911647652213569)
                ·
                  refine ⟨218486159067683735739160177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291314878756911647652213569 218486159067683735739160177)
                  ·
                    refine ⟨163864619300762801804370133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218486159067683735739160177 163864619300762801804370133)
                    ·
                      refine ⟨3840577014861628167289925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163864619300762801804370133 3840577014861628167289925)
                      ·
                        rfl

theorem cell23_7479497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_7479497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479497 prefixEnd_7479497 := by exact prefixLift 7479497
  have htrace : WordTrace (prefixWord ++ tailWord_7479497) baseStart_7479497 baseEnd_7479497 := by
    simpa [prefixWord, tailWord_7479497, baseEnd_7479497] using wordTrace_append hprefix tailTrace_7479497
  have hstable : (prefixWord ++ tailWord_7479497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479497).length < 2 ^ (prefixWord ++ tailWord_7479497).sum := by decide
  have hdescent : baseEnd_7479497 < baseStart_7479497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479498 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_7479498 : Nat := 118140960795 + 7479498 * 2 ^ 59
def prefixEnd_7479498 : Nat := 4983230072969 + 3 ^ 40 * 7479498 * 2
def baseEnd_7479498 : Nat := 3840577528342282663377421

theorem tailTrace_7479498 : CollatzResearch.WordTrace tailWord_7479498 prefixEnd_7479498 3840577528342282663377421 := by
  unfold tailWord_7479498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68199925864265904351193787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181866468971375744936516765 68199925864265904351193787)
  ·
    refine ⟨102299888796398856526790681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68199925864265904351193787 102299888796398856526790681)
    ·
      refine ⟨76724916597299142395093011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102299888796398856526790681 76724916597299142395093011)
      ·
        refine ⟨115087374895948713592639517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76724916597299142395093011 115087374895948713592639517)
        ·
          refine ⟨43157765585980767597239819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115087374895948713592639517 43157765585980767597239819)
          ·
            refine ⟨64736648378971151395859729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43157765585980767597239819 64736648378971151395859729)
            ·
              refine ⟨48552486284228363546894797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64736648378971151395859729 48552486284228363546894797)
              ·
                refine ⟨18207182356585636330085549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48552486284228363546894797 18207182356585636330085549)
                ·
                  refine ⟨6827693383719613623782081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18207182356585636330085549 6827693383719613623782081)
                  ·
                    refine ⟨5120770037789710217836561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6827693383719613623782081 5120770037789710217836561)
                    ·
                      refine ⟨3840577528342282663377421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120770037789710217836561 3840577528342282663377421)
                      ·
                        rfl

theorem cell23_7479498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_7479498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479498 prefixEnd_7479498 := by exact prefixLift 7479498
  have htrace : WordTrace (prefixWord ++ tailWord_7479498) baseStart_7479498 baseEnd_7479498 := by
    simpa [prefixWord, tailWord_7479498, baseEnd_7479498] using wordTrace_append hprefix tailTrace_7479498
  have hstable : (prefixWord ++ tailWord_7479498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479498).length < 2 ^ (prefixWord ++ tailWord_7479498).sum := by decide
  have hdescent : baseEnd_7479498 < baseStart_7479498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479531 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 3]
def baseStart_7479531 : Nat := 118140960795 + 7479531 * 2 ^ 59
def prefixEnd_7479531 : Nat := 4983230072969 + 3 ^ 40 * 7479531 * 2
def baseEnd_7479531 : Nat := 3840594473203881034264769

theorem tailTrace_7479531 : CollatzResearch.WordTrace tailWord_7479531 prefixEnd_7479531 3840594473203881034264769 := by
  unfold tailWord_7479531
  simp only [CollatzResearch.WordTrace]
  refine ⟨272800907065944064040726447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181867271377296042693817631 272800907065944064040726447)
  ·
    refine ⟨409201360598916096061089671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272800907065944064040726447 409201360598916096061089671)
    ·
      refine ⟨613802040898374144091634507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409201360598916096061089671 613802040898374144091634507)
      ·
        refine ⟨920703061347561216137451761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613802040898374144091634507 920703061347561216137451761)
        ·
          refine ⟨690527296010670912103088821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920703061347561216137451761 690527296010670912103088821)
          ·
            refine ⟨64736934001000398009664577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 690527296010670912103088821 64736934001000398009664577)
            ·
              refine ⟨48552700500750298507248433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64736934001000398009664577 48552700500750298507248433)
              ·
                refine ⟨36414525375562723880436325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48552700500750298507248433 36414525375562723880436325)
                ·
                  refine ⟨6827723507918010727581811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36414525375562723880436325 6827723507918010727581811)
                  ·
                    refine ⟨10241585261877016091372717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827723507918010727581811 10241585261877016091372717)
                    ·
                      refine ⟨3840594473203881034264769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241585261877016091372717 3840594473203881034264769)
                      ·
                        rfl

theorem cell23_7479531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 3].length) (baseStart_7479531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479531 prefixEnd_7479531 := by exact prefixLift 7479531
  have htrace : WordTrace (prefixWord ++ tailWord_7479531) baseStart_7479531 baseEnd_7479531 := by
    simpa [prefixWord, tailWord_7479531, baseEnd_7479531] using wordTrace_append hprefix tailTrace_7479531
  have hstable : (prefixWord ++ tailWord_7479531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479531).length < 2 ^ (prefixWord ++ tailWord_7479531).sum := by decide
  have hdescent : baseEnd_7479531 < baseStart_7479531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479535 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 1, 2, 3]
def baseStart_7479535 : Nat := 118140960795 + 7479535 * 2 ^ 59
def prefixEnd_7479535 : Nat := 4983230072969 + 3 ^ 40 * 7479535 * 2
def baseEnd_7479535 : Nat := 3840596527126499018614751

theorem tailTrace_7479535 : CollatzResearch.WordTrace tailWord_7479535 prefixEnd_7479535 3840596527126499018614751 := by
  unfold tailWord_7479535
  simp only [CollatzResearch.WordTrace]
  refine ⟨272801052957929572723872059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181867368638619715149248039 272801052957929572723872059)
  ·
    refine ⟨409201579436894359085808089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272801052957929572723872059 409201579436894359085808089)
    ·
      refine ⟨306901184577670769314356067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409201579436894359085808089 306901184577670769314356067)
      ·
        refine ⟨460351776866506153971534101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306901184577670769314356067 460351776866506153971534101)
        ·
          refine ⟨21578989540617475967415661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 460351776866506153971534101 21578989540617475967415661)
          ·
            refine ⟨8092121077731553487780873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21578989540617475967415661 8092121077731553487780873)
            ·
              refine ⟨6069090808298665115835655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092121077731553487780873 6069090808298665115835655)
              ·
                refine ⟨9103636212447997673753483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069090808298665115835655 9103636212447997673753483)
                ·
                  refine ⟨13655454318671996510630225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103636212447997673753483 13655454318671996510630225)
                  ·
                    refine ⟨10241590739003997382972669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13655454318671996510630225 10241590739003997382972669)
                    ·
                      refine ⟨3840596527126499018614751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241590739003997382972669 3840596527126499018614751)
                      ·
                        rfl

theorem cell23_7479535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 2, 3].length) (baseStart_7479535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479535 prefixEnd_7479535 := by exact prefixLift 7479535
  have htrace : WordTrace (prefixWord ++ tailWord_7479535) baseStart_7479535 baseEnd_7479535 := by
    simpa [prefixWord, tailWord_7479535, baseEnd_7479535] using wordTrace_append hprefix tailTrace_7479535
  have hstable : (prefixWord ++ tailWord_7479535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479535).length < 2 ^ (prefixWord ++ tailWord_7479535).sum := by decide
  have hdescent : baseEnd_7479535 < baseStart_7479535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479548 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_7479548 : Nat := 118140960795 + 7479548 * 2 ^ 59
def prefixEnd_7479548 : Nat := 4983230072969 + 3 ^ 40 * 7479548 * 2
def baseEnd_7479548 : Nat := 3840603202375007467752191

theorem tailTrace_7479548 : CollatzResearch.WordTrace tailWord_7479548 prefixEnd_7479548 3840603202375007467752191 := by
  unfold tailWord_7479548
  simp only [CollatzResearch.WordTrace]
  refine ⟨136400763553441237972047649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181867684737921650629396865 136400763553441237972047649)
  ·
    refine ⟨102300572665080928479035737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136400763553441237972047649 102300572665080928479035737)
    ·
      refine ⟨76725429498810696359276803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102300572665080928479035737 76725429498810696359276803)
      ·
        refine ⟨115088144248216044538915205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76725429498810696359276803 115088144248216044538915205)
        ·
          refine ⟨21579027046540508351046601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115088144248216044538915205 21579027046540508351046601)
          ·
            refine ⟨16184270284905381263284951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21579027046540508351046601 16184270284905381263284951)
            ·
              refine ⟨24276405427358071894927427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16184270284905381263284951 24276405427358071894927427)
              ·
                refine ⟨36414608141037107842391141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24276405427358071894927427 36414608141037107842391141)
                ·
                  refine ⟨6827739026444457720448339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36414608141037107842391141 6827739026444457720448339)
                  ·
                    refine ⟨10241608539666686580672509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827739026444457720448339 10241608539666686580672509)
                    ·
                      refine ⟨3840603202375007467752191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241608539666686580672509 3840603202375007467752191)
                      ·
                        rfl

theorem cell23_7479548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_7479548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479548 prefixEnd_7479548 := by exact prefixLift 7479548
  have htrace : WordTrace (prefixWord ++ tailWord_7479548) baseStart_7479548 baseEnd_7479548 := by
    simpa [prefixWord, tailWord_7479548, baseEnd_7479548] using wordTrace_append hprefix tailTrace_7479548
  have hstable : (prefixWord ++ tailWord_7479548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479548).length < 2 ^ (prefixWord ++ tailWord_7479548).sum := by decide
  have hdescent : baseEnd_7479548 < baseStart_7479548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479564 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_7479564 : Nat := 118140960795 + 7479564 * 2 ^ 59
def prefixEnd_7479564 : Nat := 4983230072969 + 3 ^ 40 * 7479564 * 2
def baseEnd_7479564 : Nat := 1280203806021826468384039

theorem tailTrace_7479564 : CollatzResearch.WordTrace tailWord_7479564 prefixEnd_7479564 1280203806021826468384039 := by
  unfold tailWord_7479564
  simp only [CollatzResearch.WordTrace]
  refine ⟨136401055337412255338338873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181868073783216340451118497 136401055337412255338338873)
  ·
    refine ⟨102300791503059191503754155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136401055337412255338338873 102300791503059191503754155)
    ·
      refine ⟨153451187254588787255631233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102300791503059191503754155 153451187254588787255631233)
      ·
        refine ⟨115088390440941590441723425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153451187254588787255631233 115088390440941590441723425)
        ·
          refine ⟨86316292830706192831292569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115088390440941590441723425 86316292830706192831292569)
          ·
            refine ⟨64737219623029644623469427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86316292830706192831292569 64737219623029644623469427)
            ·
              refine ⟨97105829434544466935204141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64737219623029644623469427 97105829434544466935204141)
              ·
                refine ⟨36414686037954175100701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97105829434544466935204141 36414686037954175100701553)
                ·
                  refine ⟨27311014528465631325526165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36414686037954175100701553 27311014528465631325526165)
                  ·
                    refine ⟨1280203806021826468384039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27311014528465631325526165 1280203806021826468384039)
                    ·
                      rfl

theorem cell23_7479564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_7479564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479564 prefixEnd_7479564 := by exact prefixLift 7479564
  have htrace : WordTrace (prefixWord ++ tailWord_7479564) baseStart_7479564 baseEnd_7479564 := by
    simpa [prefixWord, tailWord_7479564, baseEnd_7479564] using wordTrace_append hprefix tailTrace_7479564
  have hstable : (prefixWord ++ tailWord_7479564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479564).length < 2 ^ (prefixWord ++ tailWord_7479564).sum := by decide
  have hdescent : baseEnd_7479564 < baseStart_7479564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479575 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_7479575 : Nat := 118140960795 + 7479575 * 2 ^ 59
def prefixEnd_7479575 : Nat := 4983230072969 + 3 ^ 40 * 7479575 * 2
def baseEnd_7479575 : Nat := 3840617066352678862114567

theorem tailTrace_7479575 : CollatzResearch.WordTrace tailWord_7479575 prefixEnd_7479575 3840617066352678862114567 := by
  unfold tailWord_7479575
  simp only [CollatzResearch.WordTrace]
  refine ⟨272802511877784659555328179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181868341251856439703552119 272802511877784659555328179)
  ·
    refine ⟨409203767816676989332992269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272802511877784659555328179 409203767816676989332992269)
    ·
      refine ⟨153451412931253870999872101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409203767816676989332992269 153451412931253870999872101)
      ·
        refine ⟨28772139924610100812476019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153451412931253870999872101 28772139924610100812476019)
        ·
          refine ⟨43158209886915151218714029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28772139924610100812476019 43158209886915151218714029)
          ·
            refine ⟨16184328707593181707017761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43158209886915151218714029 16184328707593181707017761)
            ·
              refine ⟨12138246530694886280263321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16184328707593181707017761 12138246530694886280263321)
              ·
                refine ⟨9103684898021164710197491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12138246530694886280263321 9103684898021164710197491)
                ·
                  refine ⟨13655527347031747065296237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103684898021164710197491 13655527347031747065296237)
                  ·
                    refine ⟨5120822755136905149486089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13655527347031747065296237 5120822755136905149486089)
                    ·
                      refine ⟨3840617066352678862114567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120822755136905149486089 3840617066352678862114567)
                      ·
                        rfl

theorem cell23_7479575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_7479575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479575 prefixEnd_7479575 := by exact prefixLift 7479575
  have htrace : WordTrace (prefixWord ++ tailWord_7479575) baseStart_7479575 baseEnd_7479575 := by
    simpa [prefixWord, tailWord_7479575, baseEnd_7479575] using wordTrace_append hprefix tailTrace_7479575
  have hstable : (prefixWord ++ tailWord_7479575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479575).length < 2 ^ (prefixWord ++ tailWord_7479575).sum := by decide
  have hdescent : baseEnd_7479575 < baseStart_7479575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479605 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_7479605 : Nat := 118140960795 + 7479605 * 2 ^ 59
def prefixEnd_7479605 : Nat := 4983230072969 + 3 ^ 40 * 7479605 * 2
def baseEnd_7479605 : Nat := 3840632470772313744739429

theorem tailTrace_7479605 : CollatzResearch.WordTrace tailWord_7479605 prefixEnd_7479605 3840632470772313744739429 := by
  unfold tailWord_7479605
  simp only [CollatzResearch.WordTrace]
  refine ⟨272803606067675974678920269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181869070711783983119280179 272803606067675974678920269)
  ·
    refine ⟨102301352275378490504595101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272803606067675974678920269 102301352275378490504595101)
    ·
      refine ⟨38363007103266933939223163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102301352275378490504595101 38363007103266933939223163)
      ·
        refine ⟨57544510654900400908834745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363007103266933939223163 57544510654900400908834745)
        ·
          refine ⟨43158382991175300681626059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57544510654900400908834745 43158382991175300681626059)
          ·
            refine ⟨64737574486762951022439089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43158382991175300681626059 64737574486762951022439089)
            ·
              refine ⟨48553180865072213266829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64737574486762951022439089 48553180865072213266829317)
              ·
                refine ⟨9103721412201039987530497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48553180865072213266829317 9103721412201039987530497)
                ·
                  refine ⟨6827791059150779990647873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9103721412201039987530497 6827791059150779990647873)
                  ·
                    refine ⟨5120843294363084992985905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6827791059150779990647873 5120843294363084992985905)
                    ·
                      refine ⟨3840632470772313744739429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120843294363084992985905 3840632470772313744739429)
                      ·
                        rfl

theorem cell23_7479605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_7479605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479605 prefixEnd_7479605 := by exact prefixLift 7479605
  have htrace : WordTrace (prefixWord ++ tailWord_7479605) baseStart_7479605 baseEnd_7479605 := by
    simpa [prefixWord, tailWord_7479605, baseEnd_7479605] using wordTrace_append hprefix tailTrace_7479605
  have hstable : (prefixWord ++ tailWord_7479605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479605).length < 2 ^ (prefixWord ++ tailWord_7479605).sum := by decide
  have hdescent : baseEnd_7479605 < baseStart_7479605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479624 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_7479624 : Nat := 118140960795 + 7479624 * 2 ^ 59
def prefixEnd_7479624 : Nat := 4983230072969 + 3 ^ 40 * 7479624 * 2
def baseEnd_7479624 : Nat := 1280214075634916390133947

theorem tailTrace_7479624 : CollatzResearch.WordTrace tailWord_7479624 prefixEnd_7479624 1280214075634916390133947 := by
  unfold tailWord_7479624
  simp only [CollatzResearch.WordTrace]
  refine ⟨136402149527303570461930963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181869532703071427282574617 136402149527303570461930963)
  ·
    refine ⟨204603224290955355692896445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136402149527303570461930963 204603224290955355692896445)
    ·
      refine ⟨76726209109108258384836167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204603224290955355692896445 76726209109108258384836167)
      ·
        refine ⟨115089313663662387577254251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76726209109108258384836167 115089313663662387577254251)
        ·
          refine ⟨172633970495493581365881377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115089313663662387577254251 172633970495493581365881377)
          ·
            refine ⟨129475477871620186024411033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172633970495493581365881377 129475477871620186024411033)
            ·
              refine ⟨97106608403715139518308275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129475477871620186024411033 97106608403715139518308275)
              ·
                refine ⟨145659912605572709277462413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97106608403715139518308275 145659912605572709277462413)
                ·
                  refine ⟨54622467227089765979048405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145659912605572709277462413 54622467227089765979048405)
                  ·
                    refine ⟨1280214075634916390133947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54622467227089765979048405 1280214075634916390133947)
                    ·
                      rfl

theorem cell23_7479624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_7479624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479624 prefixEnd_7479624 := by exact prefixLift 7479624
  have htrace : WordTrace (prefixWord ++ tailWord_7479624) baseStart_7479624 baseEnd_7479624 := by
    simpa [prefixWord, tailWord_7479624, baseEnd_7479624] using wordTrace_append hprefix tailTrace_7479624
  have hstable : (prefixWord ++ tailWord_7479624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479624).length < 2 ^ (prefixWord ++ tailWord_7479624).sum := by decide
  have hdescent : baseEnd_7479624 < baseStart_7479624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479631 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 5, 2]
def baseStart_7479631 : Nat := 118140960795 + 7479631 * 2 ^ 59
def prefixEnd_7479631 : Nat := 4983230072969 + 3 ^ 40 * 7479631 * 2
def baseEnd_7479631 : Nat := 3840645821269330643014309

theorem tailTrace_7479631 : CollatzResearch.WordTrace tailWord_7479631 prefixEnd_7479631 3840645821269330643014309 := by
  unfold tailWord_7479631
  simp only [CollatzResearch.WordTrace]
  refine ⟨272804554365581781119366747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181869702910387854079577831 272804554365581781119366747)
  ·
    refine ⟨409206831548372671679050121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272804554365581781119366747 409206831548372671679050121)
    ·
      refine ⟨306905123661279503759287591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409206831548372671679050121 306905123661279503759287591)
      ·
        refine ⟨460357685491919255638931387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306905123661279503759287591 460357685491919255638931387)
        ·
          refine ⟨690536528237878883458397081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460357685491919255638931387 690536528237878883458397081)
          ·
            refine ⟨517902396178409162593797811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690536528237878883458397081 517902396178409162593797811)
            ·
              refine ⟨776853594267613743890696717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517902396178409162593797811 776853594267613743890696717)
              ·
                refine ⟨291320097850355153959011269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776853594267613743890696717 291320097850355153959011269)
                ·
                  refine ⟨54622518346941591367314613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291320097850355153959011269 54622518346941591367314613)
                  ·
                    refine ⟨5120861095025774190685745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54622518346941591367314613 5120861095025774190685745)
                    ·
                      refine ⟨3840645821269330643014309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120861095025774190685745 3840645821269330643014309)
                      ·
                        rfl

theorem cell23_7479631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5, 2].length) (baseStart_7479631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479631 prefixEnd_7479631 := by exact prefixLift 7479631
  have htrace : WordTrace (prefixWord ++ tailWord_7479631) baseStart_7479631 baseEnd_7479631 := by
    simpa [prefixWord, tailWord_7479631, baseEnd_7479631] using wordTrace_append hprefix tailTrace_7479631
  have hstable : (prefixWord ++ tailWord_7479631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479631).length < 2 ^ (prefixWord ++ tailWord_7479631).sum := by decide
  have hdescent : baseEnd_7479631 < baseStart_7479631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479658 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_7479658 : Nat := 118140960795 + 7479658 * 2 ^ 59
def prefixEnd_7479658 : Nat := 4983230072969 + 3 ^ 40 * 7479658 * 2
def baseEnd_7479658 : Nat := 1280219895082334012458895

theorem tailTrace_7479658 : CollatzResearch.WordTrace tailWord_7479658 prefixEnd_7479658 1280219895082334012458895 := by
  unfold tailWord_7479658
  simp only [CollatzResearch.WordTrace]
  refine ⟨68201384784120991182649907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181870359424322643153733085 68201384784120991182649907)
  ·
    refine ⟨102302077176181486773974861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68201384784120991182649907 102302077176181486773974861)
    ·
      refine ⟨38363278941068057540240573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102302077176181486773974861 38363278941068057540240573)
      ·
        refine ⟨14386229602900521577590215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38363278941068057540240573 14386229602900521577590215)
        ·
          refine ⟨21579344404350782366385323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14386229602900521577590215 21579344404350782366385323)
          ·
            refine ⟨32369016606526173549577985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579344404350782366385323 32369016606526173549577985)
            ·
              refine ⟨24276762454894630162183489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32369016606526173549577985 24276762454894630162183489)
              ·
                refine ⟨18207571841170972621637617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24276762454894630162183489 18207571841170972621637617)
                ·
                  refine ⟨13655678880878229466228213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18207571841170972621637617 13655678880878229466228213)
                  ·
                    refine ⟨1280219895082334012458895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13655678880878229466228213 1280219895082334012458895)
                    ·
                      rfl

theorem cell23_7479658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_7479658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479658 prefixEnd_7479658 := by exact prefixLift 7479658
  have htrace : WordTrace (prefixWord ++ tailWord_7479658) baseStart_7479658 baseEnd_7479658 := by
    simpa [prefixWord, tailWord_7479658, baseEnd_7479658] using wordTrace_append hprefix tailTrace_7479658
  have hstable : (prefixWord ++ tailWord_7479658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479658).length < 2 ^ (prefixWord ++ tailWord_7479658).sum := by decide
  have hdescent : baseEnd_7479658 < baseStart_7479658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479688 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_7479688 : Nat := 118140960795 + 7479688 * 2 ^ 59
def prefixEnd_7479688 : Nat := 4983230072969 + 3 ^ 40 * 7479688 * 2
def baseEnd_7479688 : Nat := 1280225029888878973333849

theorem tailTrace_7479688 : CollatzResearch.WordTrace tailWord_7479688 prefixEnd_7479688 1280225029888878973333849 := by
  unfold tailWord_7479688
  simp only [CollatzResearch.WordTrace]
  refine ⟨136403316663187639927095859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181871088884250186569461145 136403316663187639927095859)
  ·
    refine ⟨204604974994781459890643789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136403316663187639927095859 204604974994781459890643789)
    ·
      refine ⟨76726865623043047458991421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204604974994781459890643789 76726865623043047458991421)
      ·
        refine ⟨28772574608641142797121783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76726865623043047458991421 28772574608641142797121783)
        ·
          refine ⟨43158861912961714195682675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28772574608641142797121783 43158861912961714195682675)
          ·
            refine ⟨64738292869442571293524013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43158861912961714195682675 64738292869442571293524013)
            ·
              refine ⟨24276859826040964235071505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64738292869442571293524013 24276859826040964235071505)
              ·
                refine ⟨18207644869530723176303629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24276859826040964235071505 18207644869530723176303629)
                ·
                  refine ⟨6827866826074021191113861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18207644869530723176303629 6827866826074021191113861)
                  ·
                    refine ⟨1280225029888878973333849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827866826074021191113861 1280225029888878973333849)
                    ·
                      rfl

theorem cell23_7479688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_7479688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479688 prefixEnd_7479688 := by exact prefixLift 7479688
  have htrace : WordTrace (prefixWord ++ tailWord_7479688) baseStart_7479688 baseEnd_7479688 := by
    simpa [prefixWord, tailWord_7479688, baseEnd_7479688] using wordTrace_append hprefix tailTrace_7479688
  have hstable : (prefixWord ++ tailWord_7479688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479688).length < 2 ^ (prefixWord ++ tailWord_7479688).sum := by decide
  have hdescent : baseEnd_7479688 < baseStart_7479688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479705 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 1, 4]
def baseStart_7479705 : Nat := 118140960795 + 7479705 * 2 ^ 59
def prefixEnd_7479705 : Nat := 4983230072969 + 3 ^ 40 * 7479705 * 2
def baseEnd_7479705 : Nat := 1280227939612587784496323

theorem tailTrace_7479705 : CollatzResearch.WordTrace tailWord_7479705 prefixEnd_7479705 1280227939612587784496323 := by
  unfold tailWord_7479705
  simp only [CollatzResearch.WordTrace]
  refine ⟨272807253367313691757560569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181871502244875794505040379 272807253367313691757560569)
  ·
    refine ⟨204605440025485268818170427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272807253367313691757560569 204605440025485268818170427)
    ·
      refine ⟨306908160038227903227255641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204605440025485268818170427 306908160038227903227255641)
      ·
        refine ⟨230181120028670927420441731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306908160038227903227255641 230181120028670927420441731)
        ·
          refine ⟨345271680043006391130662597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230181120028670927420441731 345271680043006391130662597)
          ·
            refine ⟨64738440008063698336999237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345271680043006391130662597 64738440008063698336999237)
            ·
              refine ⟨12138457501511943438187357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64738440008063698336999237 12138457501511943438187357)
              ·
                refine ⟨4551921563066978789320259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12138457501511943438187357 4551921563066978789320259)
                ·
                  refine ⟨6827882344600468183980389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551921563066978789320259 6827882344600468183980389)
                  ·
                    refine ⟨1280227939612587784496323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827882344600468183980389 1280227939612587784496323)
                    ·
                      rfl

theorem cell23_7479705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 1, 4].length) (baseStart_7479705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479705 prefixEnd_7479705 := by exact prefixLift 7479705
  have htrace : WordTrace (prefixWord ++ tailWord_7479705) baseStart_7479705 baseEnd_7479705 := by
    simpa [prefixWord, tailWord_7479705, baseEnd_7479705] using wordTrace_append hprefix tailTrace_7479705
  have hstable : (prefixWord ++ tailWord_7479705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479705).length < 2 ^ (prefixWord ++ tailWord_7479705).sum := by decide
  have hdescent : baseEnd_7479705 < baseStart_7479705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479761 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_7479761 : Nat := 118140960795 + 7479761 * 2 ^ 59
def prefixEnd_7479761 : Nat := 4983230072969 + 3 ^ 40 * 7479761 * 2
def baseEnd_7479761 : Nat := 1280237524584805044796237

theorem tailTrace_7479761 : CollatzResearch.WordTrace tailWord_7479761 prefixEnd_7479761 1280237524584805044796237 := by
  unfold tailWord_7479761
  simp only [CollatzResearch.WordTrace]
  refine ⟨272809295855110813321599137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181872863903407208881066091 272809295855110813321599137)
  ·
    refine ⟨204606971891333109991199353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272809295855110813321599137 204606971891333109991199353)
    ·
      refine ⟨153455228918499832493399515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204606971891333109991199353 153455228918499832493399515)
      ·
        refine ⟨230182843377749748740099273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153455228918499832493399515 230182843377749748740099273)
        ·
          refine ⟨172637132533312311555074455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230182843377749748740099273 172637132533312311555074455)
          ·
            refine ⟨258955698799968467332611683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172637132533312311555074455 258955698799968467332611683)
            ·
              refine ⟨388433548199952700998917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258955698799968467332611683 388433548199952700998917525)
              ·
                refine ⟨18207822571872782859324259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388433548199952700998917525 18207822571872782859324259)
                ·
                  refine ⟨27311733857809174288986389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18207822571872782859324259 27311733857809174288986389)
                  ·
                    refine ⟨1280237524584805044796237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27311733857809174288986389 1280237524584805044796237)
                    ·
                      rfl

theorem cell23_7479761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_7479761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479761 prefixEnd_7479761 := by exact prefixLift 7479761
  have htrace : WordTrace (prefixWord ++ tailWord_7479761) baseStart_7479761 baseEnd_7479761 := by
    simpa [prefixWord, tailWord_7479761, baseEnd_7479761] using wordTrace_append hprefix tailTrace_7479761
  have hstable : (prefixWord ++ tailWord_7479761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479761).length < 2 ^ (prefixWord ++ tailWord_7479761).sum := by decide
  have hdescent : baseEnd_7479761 < baseStart_7479761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479779 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 3, 1, 3]
def baseStart_7479779 : Nat := 118140960795 + 7479779 * 2 ^ 59
def prefixEnd_7479779 : Nat := 4983230072969 + 3 ^ 40 * 7479779 * 2
def baseEnd_7479779 : Nat := 3840721816406196063963629

theorem tailTrace_7479779 : CollatzResearch.WordTrace tailWord_7479779 prefixEnd_7479779 3840721816406196063963629 := by
  unfold tailWord_7479779
  simp only [CollatzResearch.WordTrace]
  refine ⟨272809952369045602395754391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181873301579363734930502927 272809952369045602395754391)
  ·
    refine ⟨409214928553568403593631587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272809952369045602395754391 409214928553568403593631587)
    ·
      refine ⟨613822392830352605390447381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409214928553568403593631587 613822392830352605390447381)
      ·
        refine ⟨28772924663922778377677221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 613822392830352605390447381 28772924663922778377677221)
        ·
          refine ⟨5394923374485520945814479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28772924663922778377677221 5394923374485520945814479)
          ·
            refine ⟨8092385061728281418721719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394923374485520945814479 8092385061728281418721719)
            ·
              refine ⟨12138577592592422128082579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092385061728281418721719 12138577592592422128082579)
              ·
                refine ⟨18207866388888633192123869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138577592592422128082579 18207866388888633192123869)
                ·
                  refine ⟨6827949895833237447046451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18207866388888633192123869 6827949895833237447046451)
                  ·
                    refine ⟨10241924843749856170569677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6827949895833237447046451 10241924843749856170569677)
                    ·
                      refine ⟨3840721816406196063963629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241924843749856170569677 3840721816406196063963629)
                      ·
                        rfl

theorem cell23_7479779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_7479779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479779 prefixEnd_7479779 := by exact prefixLift 7479779
  have htrace : WordTrace (prefixWord ++ tailWord_7479779) baseStart_7479779 baseEnd_7479779 := by
    simpa [prefixWord, tailWord_7479779, baseEnd_7479779] using wordTrace_append hprefix tailTrace_7479779
  have hstable : (prefixWord ++ tailWord_7479779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479779).length < 2 ^ (prefixWord ++ tailWord_7479779).sum := by decide
  have hdescent : baseEnd_7479779 < baseStart_7479779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479785 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 3, 2, 2]
def baseStart_7479785 : Nat := 118140960795 + 7479785 * 2 ^ 59
def prefixEnd_7479785 : Nat := 4983230072969 + 3 ^ 40 * 7479785 * 2
def baseEnd_7479785 : Nat := 3840724897290123040488601

theorem tailTrace_7479785 : CollatzResearch.WordTrace tailWord_7479785 prefixEnd_7479785 3840724897290123040488601 := by
  unfold tailWord_7479785
  simp only [CollatzResearch.WordTrace]
  refine ⟨272810171207023865420472809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181873447471349243613648539 272810171207023865420472809)
  ·
    refine ⟨204607628405267899065354607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272810171207023865420472809 204607628405267899065354607)
    ·
      refine ⟨306911442607901848598031911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204607628405267899065354607 306911442607901848598031911)
      ·
        refine ⟨460367163911852772897047867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306911442607901848598031911 460367163911852772897047867)
        ·
          refine ⟨690550745867779159345571801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460367163911852772897047867 690550745867779159345571801)
          ·
            refine ⟨517913059400834369509178851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690550745867779159345571801 517913059400834369509178851)
            ·
              refine ⟨776869589101251554263768277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517913059400834369509178851 776869589101251554263768277)
              ·
                refine ⟨18207880994560583303057069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 776869589101251554263768277 18207880994560583303057069)
                ·
                  refine ⟨6827955372960218738646401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18207880994560583303057069 6827955372960218738646401)
                  ·
                    refine ⟨5120966529720164053984801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6827955372960218738646401 5120966529720164053984801)
                    ·
                      refine ⟨3840724897290123040488601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5120966529720164053984801 3840724897290123040488601)
                      ·
                        rfl

theorem cell23_7479785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2, 2].length) (baseStart_7479785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479785 prefixEnd_7479785 := by exact prefixLift 7479785
  have htrace : WordTrace (prefixWord ++ tailWord_7479785) baseStart_7479785 baseEnd_7479785 := by
    simpa [prefixWord, tailWord_7479785, baseEnd_7479785] using wordTrace_append hprefix tailTrace_7479785
  have hstable : (prefixWord ++ tailWord_7479785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479785).length < 2 ^ (prefixWord ++ tailWord_7479785).sum := by decide
  have hdescent : baseEnd_7479785 < baseStart_7479785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479788 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_7479788 : Nat := 118140960795 + 7479788 * 2 ^ 59
def prefixEnd_7479788 : Nat := 4983230072969 + 3 ^ 40 * 7479788 * 2
def baseEnd_7479788 : Nat := 3840726437732086528751087

theorem tailTrace_7479788 : CollatzResearch.WordTrace tailWord_7479788 prefixEnd_7479788 3840726437732086528751087 := by
  unfold tailWord_7479788
  simp only [CollatzResearch.WordTrace]
  refine ⟨136405140313006498466416009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181873520417341997955221345 136405140313006498466416009)
  ·
    refine ⟨102303855234754873849812007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136405140313006498466416009 102303855234754873849812007)
    ·
      refine ⟨153455782852132310774718011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102303855234754873849812007 153455782852132310774718011)
      ·
        refine ⟨230183674278198466162077017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153455782852132310774718011 230183674278198466162077017)
        ·
          refine ⟨172637755708648849621557763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230183674278198466162077017 172637755708648849621557763)
          ·
            refine ⟨258956633562973274432336645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172637755708648849621557763 258956633562973274432336645)
            ·
              refine ⟨48554368793057488956063121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258956633562973274432336645 48554368793057488956063121)
              ·
                refine ⟨36415776594793116717047341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48554368793057488956063121 36415776594793116717047341)
                ·
                  refine ⟨13655916223047418768892753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36415776594793116717047341 13655916223047418768892753)
                  ·
                    refine ⟨10241937167285564076669565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13655916223047418768892753 10241937167285564076669565)
                    ·
                      refine ⟨3840726437732086528751087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10241937167285564076669565 3840726437732086528751087)
                      ·
                        rfl

theorem cell23_7479788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_7479788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479788 prefixEnd_7479788 := by exact prefixLift 7479788
  have htrace : WordTrace (prefixWord ++ tailWord_7479788) baseStart_7479788 baseEnd_7479788 := by
    simpa [prefixWord, tailWord_7479788, baseEnd_7479788] using wordTrace_append hprefix tailTrace_7479788
  have hstable : (prefixWord ++ tailWord_7479788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479788).length < 2 ^ (prefixWord ++ tailWord_7479788).sum := by decide
  have hdescent : baseEnd_7479788 < baseStart_7479788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479798 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7479798 : Nat := 118140960795 + 7479798 * 2 ^ 59
def prefixEnd_7479798 : Nat := 4983230072969 + 3 ^ 40 * 7479798 * 2
def baseEnd_7479798 : Nat := 3840731572538631489626041

theorem tailTrace_7479798 : CollatzResearch.WordTrace tailWord_7479798 prefixEnd_7479798 3840731572538631489626041 := by
  unfold tailWord_7479798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050665334748548040043503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181873763570651179093797365 17050665334748548040043503)
  ·
    refine ⟨25575998002122822060065255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17050665334748548040043503 25575998002122822060065255)
    ·
      refine ⟨38363997003184233090097883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575998002122822060065255 38363997003184233090097883)
      ·
        refine ⟨57545995504776349635146825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363997003184233090097883 57545995504776349635146825)
        ·
          refine ⟨43159496628582262226360119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57545995504776349635146825 43159496628582262226360119)
          ·
            refine ⟨64739244942873393339540179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43159496628582262226360119 64739244942873393339540179)
            ·
              refine ⟨97108867414310090009310269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64739244942873393339540179 97108867414310090009310269)
              ·
                refine ⟨36415825280366283753491351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97108867414310090009310269 36415825280366283753491351)
                ·
                  refine ⟨54623737920549425630237027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36415825280366283753491351 54623737920549425630237027)
                  ·
                    refine ⟨81935606880824138445355541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54623737920549425630237027 81935606880824138445355541)
                    ·
                      refine ⟨3840731572538631489626041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81935606880824138445355541 3840731572538631489626041)
                      ·
                        rfl

theorem cell23_7479798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7479798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479798 prefixEnd_7479798 := by exact prefixLift 7479798
  have htrace : WordTrace (prefixWord ++ tailWord_7479798) baseStart_7479798 baseEnd_7479798 := by
    simpa [prefixWord, tailWord_7479798, baseEnd_7479798] using wordTrace_append hprefix tailTrace_7479798
  have hstable : (prefixWord ++ tailWord_7479798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479798).length < 2 ^ (prefixWord ++ tailWord_7479798).sum := by decide
  have hdescent : baseEnd_7479798 < baseStart_7479798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479815 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7479815 : Nat := 118140960795 + 7479815 * 2 ^ 59
def prefixEnd_7479815 : Nat := 4983230072969 + 3 ^ 40 * 7479815 * 2
def baseEnd_7479815 : Nat := 3840740301709757923113463

theorem tailTrace_7479815 : CollatzResearch.WordTrace tailWord_7479815 prefixEnd_7479815 3840740301709757923113463 := by
  unfold tailWord_7479815
  simp only [CollatzResearch.WordTrace]
  refine ⟨272811265396915180544064899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181874176931276787029376599 272811265396915180544064899)
  ·
    refine ⟨409216898095372770816097349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272811265396915180544064899 409216898095372770816097349)
    ·
      refine ⟨76728168392882394528018253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409216898095372770816097349 76728168392882394528018253)
      ·
        refine ⟨28773063147330897948006845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76728168392882394528018253 28773063147330897948006845)
        ·
          refine ⟨10789898680249086730502567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28773063147330897948006845 10789898680249086730502567)
          ·
            refine ⟨16184848020373630095753851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10789898680249086730502567 16184848020373630095753851)
            ·
              refine ⟨24277272030560445143630777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16184848020373630095753851 24277272030560445143630777)
              ·
                refine ⟨18207954022920333857723083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24277272030560445143630777 18207954022920333857723083)
                ·
                  refine ⟨27311931034380500786584625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18207954022920333857723083 27311931034380500786584625)
                  ·
                    refine ⟨20483948275785375589938469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27311931034380500786584625 20483948275785375589938469)
                    ·
                      refine ⟨3840740301709757923113463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20483948275785375589938469 3840740301709757923113463)
                      ·
                        rfl

theorem cell23_7479815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7479815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479815 prefixEnd_7479815 := by exact prefixLift 7479815
  have htrace : WordTrace (prefixWord ++ tailWord_7479815) baseStart_7479815 baseEnd_7479815 := by
    simpa [prefixWord, tailWord_7479815, baseEnd_7479815] using wordTrace_append hprefix tailTrace_7479815
  have hstable : (prefixWord ++ tailWord_7479815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479815).length < 2 ^ (prefixWord ++ tailWord_7479815).sum := by decide
  have hdescent : baseEnd_7479815 < baseStart_7479815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479836 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_7479836 : Nat := 118140960795 + 7479836 * 2 ^ 59
def prefixEnd_7479836 : Nat := 4983230072969 + 3 ^ 40 * 7479836 * 2
def baseEnd_7479836 : Nat := 3840751084803502340950867

theorem tailTrace_7479836 : CollatzResearch.WordTrace tailWord_7479836 prefixEnd_7479836 3840751084803502340950867 := by
  unfold tailWord_7479836
  simp only [CollatzResearch.WordTrace]
  refine ⟨136406015664919550565289681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181874687553226067420386241 136406015664919550565289681)
  ·
    refine ⟨102304511748689662923967261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136406015664919550565289681 102304511748689662923967261)
    ·
      refine ⟨38364191905758623596487723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102304511748689662923967261 38364191905758623596487723)
      ·
        refine ⟨57546287858637935394731585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38364191905758623596487723 57546287858637935394731585)
        ·
          refine ⟨43159715893978451546048689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57546287858637935394731585 43159715893978451546048689)
          ·
            refine ⟨32369786920483838659536517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43159715893978451546048689 32369786920483838659536517)
            ·
              refine ⟨6069335047590719748663097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32369786920483838659536517 6069335047590719748663097)
              ·
                refine ⟨4552001285693039811497323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6069335047590719748663097 4552001285693039811497323)
                ·
                  refine ⟨6828001928539559717245985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552001285693039811497323 6828001928539559717245985)
                  ·
                    refine ⟨5121001446404669787934489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6828001928539559717245985 5121001446404669787934489)
                    ·
                      refine ⟨3840751084803502340950867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121001446404669787934489 3840751084803502340950867)
                      ·
                        rfl

theorem cell23_7479836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_7479836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479836 prefixEnd_7479836 := by exact prefixLift 7479836
  have htrace : WordTrace (prefixWord ++ tailWord_7479836) baseStart_7479836 baseEnd_7479836 := by
    simpa [prefixWord, tailWord_7479836, baseEnd_7479836] using wordTrace_append hprefix tailTrace_7479836
  have hstable : (prefixWord ++ tailWord_7479836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479836).length < 2 ^ (prefixWord ++ tailWord_7479836).sum := by decide
  have hdescent : baseEnd_7479836 < baseStart_7479836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479845 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_7479845 : Nat := 118140960795 + 7479845 * 2 ^ 59
def prefixEnd_7479845 : Nat := 4983230072969 + 3 ^ 40 * 7479845 * 2
def baseEnd_7479845 : Nat := 3840755706129392805738325

theorem tailTrace_7479845 : CollatzResearch.WordTrace tailWord_7479845 prefixEnd_7479845 3840755706129392805738325 := by
  unfold tailWord_7479845
  simp only [CollatzResearch.WordTrace]
  refine ⟨272812359586806495667656989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181874906391204330445104659 272812359586806495667656989)
  ·
    refine ⟨102304634845052435875371371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272812359586806495667656989 102304634845052435875371371)
    ·
      refine ⟨153456952267578653813057057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102304634845052435875371371 153456952267578653813057057)
      ·
        refine ⟨115092714200683990359792793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153456952267578653813057057 115092714200683990359792793)
        ·
          refine ⟨86319535650512992769844595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115092714200683990359792793 86319535650512992769844595)
          ·
            refine ⟨129479303475769489154766893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86319535650512992769844595 129479303475769489154766893)
            ·
              refine ⟨48554738803413558433037585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129479303475769489154766893 48554738803413558433037585)
              ·
                refine ⟨36416054102560168824778189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48554738803413558433037585 36416054102560168824778189)
                ·
                  refine ⟨13656020288460063309291821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36416054102560168824778189 13656020288460063309291821)
                  ·
                    refine ⟨5121007608172523740984433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13656020288460063309291821 5121007608172523740984433)
                    ·
                      refine ⟨3840755706129392805738325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121007608172523740984433 3840755706129392805738325)
                      ·
                        rfl

theorem cell23_7479845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_7479845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479845 prefixEnd_7479845 := by exact prefixLift 7479845
  have htrace : WordTrace (prefixWord ++ tailWord_7479845) baseStart_7479845 baseEnd_7479845 := by
    simpa [prefixWord, tailWord_7479845, baseEnd_7479845] using wordTrace_append hprefix tailTrace_7479845
  have hstable : (prefixWord ++ tailWord_7479845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479845).length < 2 ^ (prefixWord ++ tailWord_7479845).sum := by decide
  have hdescent : baseEnd_7479845 < baseStart_7479845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479853 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7479853 : Nat := 118140960795 + 7479853 * 2 ^ 59
def prefixEnd_7479853 : Nat := 4983230072969 + 3 ^ 40 * 7479853 * 2
def baseEnd_7479853 : Nat := 3840759813974628774438289

theorem tailTrace_7479853 : CollatzResearch.WordTrace tailWord_7479853 prefixEnd_7479853 3840759813974628774438289 := by
  unfold tailWord_7479853
  simp only [CollatzResearch.WordTrace]
  refine ⟨272812651370777513033948213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181875100913851675355965475 272812651370777513033948213)
  ·
    refine ⟨25576186066010391846932645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272812651370777513033948213 25576186066010391846932645)
    ·
      refine ⟨4795534887376948471299871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25576186066010391846932645 4795534887376948471299871)
      ·
        refine ⟨7193302331065422706949807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795534887376948471299871 7193302331065422706949807)
        ·
          refine ⟨10789953496598134060424711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193302331065422706949807 10789953496598134060424711)
          ·
            refine ⟨16184930244897201090637067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10789953496598134060424711 16184930244897201090637067)
            ·
              refine ⟨24277395367345801635955601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16184930244897201090637067 24277395367345801635955601)
              ·
                refine ⟨18208046525509351226966701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24277395367345801635955601 18208046525509351226966701)
                ·
                  refine ⟨6828017447066006710112513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18208046525509351226966701 6828017447066006710112513)
                  ·
                    refine ⟨5121013085299505032584385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6828017447066006710112513 5121013085299505032584385)
                    ·
                      refine ⟨3840759813974628774438289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121013085299505032584385 3840759813974628774438289)
                      ·
                        rfl

theorem cell23_7479853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7479853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479853 prefixEnd_7479853 := by exact prefixLift 7479853
  have htrace : WordTrace (prefixWord ++ tailWord_7479853) baseStart_7479853 baseEnd_7479853 := by
    simpa [prefixWord, tailWord_7479853, baseEnd_7479853] using wordTrace_append hprefix tailTrace_7479853
  have hstable : (prefixWord ++ tailWord_7479853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479853).length < 2 ^ (prefixWord ++ tailWord_7479853).sum := by decide
  have hdescent : baseEnd_7479853 < baseStart_7479853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479879 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_7479879 : Nat := 118140960795 + 7479879 * 2 ^ 59
def prefixEnd_7479879 : Nat := 4983230072969 + 3 ^ 40 * 7479879 * 2
def baseEnd_7479879 : Nat := 3840773164471645672713169

theorem tailTrace_7479879 : CollatzResearch.WordTrace tailWord_7479879 prefixEnd_7479879 3840773164471645672713169 := by
  unfold tailWord_7479879
  simp only [CollatzResearch.WordTrace]
  refine ⟨272813599668683319474394691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181875733112455546316263127 272813599668683319474394691)
  ·
    refine ⟨409220399503024979211592037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272813599668683319474394691 409220399503024979211592037)
    ·
      refine ⟨76728824906817183602173507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409220399503024979211592037 76728824906817183602173507)
      ·
        refine ⟨115093237360225775403260261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76728824906817183602173507 115093237360225775403260261)
        ·
          refine ⟨21579982005042332888111299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115093237360225775403260261 21579982005042332888111299)
          ·
            refine ⟨32369973007563499332166949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579982005042332888111299 32369973007563499332166949)
            ·
              refine ⟨6069369938918156124781303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32369973007563499332166949 6069369938918156124781303)
              ·
                refine ⟨9104054908377234187171955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069369938918156124781303 9104054908377234187171955)
                ·
                  refine ⟨13656082362565851280757933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9104054908377234187171955 13656082362565851280757933)
                  ·
                    refine ⟨5121030885962194230284225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13656082362565851280757933 5121030885962194230284225)
                    ·
                      refine ⟨3840773164471645672713169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121030885962194230284225 3840773164471645672713169)
                      ·
                        rfl

theorem cell23_7479879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_7479879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479879 prefixEnd_7479879 := by exact prefixLift 7479879
  have htrace : WordTrace (prefixWord ++ tailWord_7479879) baseStart_7479879 baseEnd_7479879 := by
    simpa [prefixWord, tailWord_7479879, baseEnd_7479879] using wordTrace_append hprefix tailTrace_7479879
  have hstable : (prefixWord ++ tailWord_7479879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479879).length < 2 ^ (prefixWord ++ tailWord_7479879).sum := by decide
  have hdescent : baseEnd_7479879 < baseStart_7479879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479885 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7479885 : Nat := 118140960795 + 7479885 * 2 ^ 59
def prefixEnd_7479885 : Nat := 4983230072969 + 3 ^ 40 * 7479885 * 2
def baseEnd_7479885 : Nat := 1280258748451857549746047

theorem tailTrace_7479885 : CollatzResearch.WordTrace tailWord_7479885 prefixEnd_7479885 1280258748451857549746047 := by
  unfold tailWord_7479885
  simp only [CollatzResearch.WordTrace]
  refine ⟨272813818506661582499113109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181875879004441054999408739 272813818506661582499113109)
  ·
    refine ⟨12788147742499761679645927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272813818506661582499113109 12788147742499761679645927)
    ·
      refine ⟨19182221613749642519468891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788147742499761679645927 19182221613749642519468891)
      ·
        refine ⟨28773332420624463779203337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19182221613749642519468891 28773332420624463779203337)
        ·
          refine ⟨21579999315468347834402503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28773332420624463779203337 21579999315468347834402503)
          ·
            refine ⟨32369998973202521751603755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21579999315468347834402503 32369998973202521751603755)
            ·
              refine ⟨48554998459803782627405633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32369998973202521751603755 48554998459803782627405633)
              ·
                refine ⟨36416248844852836970554225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48554998459803782627405633 36416248844852836970554225)
                ·
                  refine ⟨27312186633639627727915669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36416248844852836970554225 27312186633639627727915669)
                  ·
                    refine ⟨1280258748451857549746047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27312186633639627727915669 1280258748451857549746047)
                    ·
                      rfl

theorem cell23_7479885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7479885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479885 prefixEnd_7479885 := by exact prefixLift 7479885
  have htrace : WordTrace (prefixWord ++ tailWord_7479885) baseStart_7479885 baseEnd_7479885 := by
    simpa [prefixWord, tailWord_7479885, baseEnd_7479885] using wordTrace_append hprefix tailTrace_7479885
  have hstable : (prefixWord ++ tailWord_7479885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479885).length < 2 ^ (prefixWord ++ tailWord_7479885).sum := by decide
  have hdescent : baseEnd_7479885 < baseStart_7479885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479909 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_7479909 : Nat := 118140960795 + 7479909 * 2 ^ 59
def prefixEnd_7479909 : Nat := 4983230072969 + 3 ^ 40 * 7479909 * 2
def baseEnd_7479909 : Nat := 3840788568891280555338031

theorem tailTrace_7479909 : CollatzResearch.WordTrace tailWord_7479909 prefixEnd_7479909 3840788568891280555338031 := by
  unfold tailWord_7479909
  simp only [CollatzResearch.WordTrace]
  refine ⟨272814693858574634597986781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181876462572383089731991187 272814693858574634597986781)
  ·
    refine ⟨102305510196965487974245043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272814693858574634597986781 102305510196965487974245043)
    ·
      refine ⟨153458265295448231961367565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102305510196965487974245043 153458265295448231961367565)
      ·
        refine ⟨57546849485793086985512837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153458265295448231961367565 57546849485793086985512837)
        ·
          refine ⟨10790034278586203809783657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57546849485793086985512837 10790034278586203809783657)
          ·
            refine ⟨8092525708939652857337743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10790034278586203809783657 8092525708939652857337743)
            ·
              refine ⟨12138788563409479286006615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092525708939652857337743 12138788563409479286006615)
              ·
                refine ⟨18208182845114218929009923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138788563409479286006615 18208182845114218929009923)
                ·
                  refine ⟨27312274267671328393514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18208182845114218929009923 27312274267671328393514885)
                  ·
                    refine ⟨5121051425188374073784041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27312274267671328393514885 5121051425188374073784041)
                    ·
                      refine ⟨3840788568891280555338031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121051425188374073784041 3840788568891280555338031)
                      ·
                        rfl

theorem cell23_7479909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_7479909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479909 prefixEnd_7479909 := by exact prefixLift 7479909
  have htrace : WordTrace (prefixWord ++ tailWord_7479909) baseStart_7479909 baseEnd_7479909 := by
    simpa [prefixWord, tailWord_7479909, baseEnd_7479909] using wordTrace_append hprefix tailTrace_7479909
  have hstable : (prefixWord ++ tailWord_7479909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479909).length < 2 ^ (prefixWord ++ tailWord_7479909).sum := by decide
  have hdescent : baseEnd_7479909 < baseStart_7479909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7479948 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7479948 : Nat := 118140960795 + 7479948 * 2 ^ 59
def prefixEnd_7479948 : Nat := 4983230072969 + 3 ^ 40 * 7479948 * 2
def baseEnd_7479948 : Nat := 3840808594636805902750351

theorem tailTrace_7479948 : CollatzResearch.WordTrace tailWord_7479948 prefixEnd_7479948 3840808594636805902750351 := by
  unfold tailWord_7479948
  simp only [CollatzResearch.WordTrace]
  refine ⟨136408058152716672129328249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181877410870288896172437665 136408058152716672129328249)
  ·
    refine ⟨102306043614537504096996187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136408058152716672129328249 102306043614537504096996187)
    ·
      refine ⟨153459065421806256145494281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102306043614537504096996187 153459065421806256145494281)
      ·
        refine ⟨115094299066354692109120711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153459065421806256145494281 115094299066354692109120711)
        ·
          refine ⟨172641448599532038163681067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115094299066354692109120711 172641448599532038163681067)
          ·
            refine ⟨258962172899298057245521601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172641448599532038163681067 258962172899298057245521601)
            ·
              refine ⟨194221629674473542934141201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258962172899298057245521601 194221629674473542934141201)
              ·
                refine ⟨145666222255855157200605901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194221629674473542934141201 145666222255855157200605901)
                ·
                  refine ⟨54624833345945683950227213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145666222255855157200605901 54624833345945683950227213)
                  ·
                    refine ⟨20484312504729631481335205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54624833345945683950227213 20484312504729631481335205)
                    ·
                      refine ⟨3840808594636805902750351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20484312504729631481335205 3840808594636805902750351)
                      ·
                        rfl

theorem cell23_7479948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7479948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7479948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7479948 prefixEnd_7479948 := by exact prefixLift 7479948
  have htrace : WordTrace (prefixWord ++ tailWord_7479948) baseStart_7479948 baseEnd_7479948 := by
    simpa [prefixWord, tailWord_7479948, baseEnd_7479948] using wordTrace_append hprefix tailTrace_7479948
  have hstable : (prefixWord ++ tailWord_7479948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7479948).length < 2 ^ (prefixWord ++ tailWord_7479948).sum := by decide
  have hdescent : baseEnd_7479948 < baseStart_7479948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7479948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480066 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_7480066 : Nat := 118140960795 + 7480066 * 2 ^ 59
def prefixEnd_7480066 : Nat := 4983230072969 + 3 ^ 40 * 7480066 * 2
def baseEnd_7480066 : Nat := 3840869185354036441074809

theorem tailTrace_7480066 : CollatzResearch.WordTrace tailWord_7480066 prefixEnd_7480066 3840869185354036441074809 := by
  unfold tailWord_7480066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68205105029751462602863013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181880280079337233607634701 68205105029751462602863013)
  ·
    refine ⟨12788457193078399238036815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68205105029751462602863013 12788457193078399238036815)
    ·
      refine ⟨19182685789617598857055223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788457193078399238036815 19182685789617598857055223)
      ·
        refine ⟨28774028684426398285582835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19182685789617598857055223 28774028684426398285582835)
        ·
          refine ⟨43161043026639597428374253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28774028684426398285582835 43161043026639597428374253)
          ·
            refine ⟨16185391134989849035640345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43161043026639597428374253 16185391134989849035640345)
            ·
              refine ⟨12139043351242386776730259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16185391134989849035640345 12139043351242386776730259)
              ·
                refine ⟨18208565026863580165095389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12139043351242386776730259 18208565026863580165095389)
                ·
                  refine ⟨6828211885073842561910771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18208565026863580165095389 6828211885073842561910771)
                  ·
                    refine ⟨10242317827610763842866157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6828211885073842561910771 10242317827610763842866157)
                    ·
                      refine ⟨3840869185354036441074809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10242317827610763842866157 3840869185354036441074809)
                      ·
                        rfl

theorem cell23_7480066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_7480066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480066 prefixEnd_7480066 := by exact prefixLift 7480066
  have htrace : WordTrace (prefixWord ++ tailWord_7480066) baseStart_7480066 baseEnd_7480066 := by
    simpa [prefixWord, tailWord_7480066, baseEnd_7480066] using wordTrace_append hprefix tailTrace_7480066
  have hstable : (prefixWord ++ tailWord_7480066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480066).length < 2 ^ (prefixWord ++ tailWord_7480066).sum := by decide
  have hdescent : baseEnd_7480066 < baseStart_7480066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480085 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_7480085 : Nat := 118140960795 + 7480085 * 2 ^ 59
def prefixEnd_7480085 : Nat := 4983230072969 + 3 ^ 40 * 7480085 * 2
def baseEnd_7480085 : Nat := 3840878941486471866737221

theorem tailTrace_7480085 : CollatzResearch.WordTrace tailWord_7480085 prefixEnd_7480085 3840878941486471866737221 := by
  unfold tailWord_7480085
  simp only [CollatzResearch.WordTrace]
  refine ⟨272821113105937016656393709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181880742070624677770929139 272821113105937016656393709)
  ·
    refine ⟨102307917414726381246147641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272821113105937016656393709 102307917414726381246147641)
    ·
      refine ⟨76730938061044785934610731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102307917414726381246147641 76730938061044785934610731)
      ·
        refine ⟨115096407091567178901916097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76730938061044785934610731 115096407091567178901916097)
        ·
          refine ⟨86322305318675384176437073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115096407091567178901916097 86322305318675384176437073)
          ·
            refine ⟨64741728989006538132327805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86322305318675384176437073 64741728989006538132327805)
            ·
              refine ⟨24278148370877451799622927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64741728989006538132327805 24278148370877451799622927)
              ·
                refine ⟨36417222556316177699434391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24278148370877451799622927 36417222556316177699434391)
                ·
                  refine ⟨54625833834474266549151587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36417222556316177699434391 54625833834474266549151587)
                  ·
                    refine ⟨81938750751711399823727381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54625833834474266549151587 81938750751711399823727381)
                    ·
                      refine ⟨3840878941486471866737221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81938750751711399823727381 3840878941486471866737221)
                      ·
                        rfl

theorem cell23_7480085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_7480085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480085 prefixEnd_7480085 := by exact prefixLift 7480085
  have htrace : WordTrace (prefixWord ++ tailWord_7480085) baseStart_7480085 baseEnd_7480085 := by
    simpa [prefixWord, tailWord_7480085, baseEnd_7480085] using wordTrace_append hprefix tailTrace_7480085
  have hstable : (prefixWord ++ tailWord_7480085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480085).length < 2 ^ (prefixWord ++ tailWord_7480085).sum := by decide
  have hdescent : baseEnd_7480085 < baseStart_7480085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480095 : List Nat := [1, 1, 2, 4, 2, 3, 1, 9]
def baseStart_7480095 : Nat := 118140960795 + 7480095 * 2 ^ 59
def prefixEnd_7480095 : Nat := 4983230072969 + 3 ^ 40 * 7480095 * 2
def baseEnd_7480095 : Nat := 142254965788630252874525

theorem tailTrace_7480095 : CollatzResearch.WordTrace tailWord_7480095 prefixEnd_7480095 142254965788630252874525 := by
  unfold tailWord_7480095
  simp only [CollatzResearch.WordTrace]
  refine ⟨272821477835900788364257739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181880985223933858909505159 272821477835900788364257739)
  ·
    refine ⟨409232216753851182546386609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272821477835900788364257739 409232216753851182546386609)
    ·
      refine ⟨306924162565388386909789957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409232216753851182546386609 306924162565388386909789957)
      ·
        refine ⟨57548280481010322545585617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306924162565388386909789957 57548280481010322545585617)
        ·
          refine ⟨43161210360757741909189213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57548280481010322545585617 43161210360757741909189213)
          ·
            refine ⟨16185453885284153215945955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43161210360757741909189213 16185453885284153215945955)
            ·
              refine ⟨24278180827926229823918933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16185453885284153215945955 24278180827926229823918933)
              ·
                refine ⟨142254965788630252874525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24278180827926229823918933 142254965788630252874525)
                ·
                  rfl

theorem cell23_7480095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 9].length) (baseStart_7480095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480095 prefixEnd_7480095 := by exact prefixLift 7480095
  have htrace : WordTrace (prefixWord ++ tailWord_7480095) baseStart_7480095 baseEnd_7480095 := by
    simpa [prefixWord, tailWord_7480095, baseEnd_7480095] using wordTrace_append hprefix tailTrace_7480095
  have hstable : (prefixWord ++ tailWord_7480095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480095).length < 2 ^ (prefixWord ++ tailWord_7480095).sum := by decide
  have hdescent : baseEnd_7480095 < baseStart_7480095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480100 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_7480100 : Nat := 118140960795 + 7480100 * 2 ^ 59
def prefixEnd_7480100 : Nat := 4983230072969 + 3 ^ 40 * 7480100 * 2
def baseEnd_7480100 : Nat := 3840886643696289308049653

theorem tailTrace_7480100 : CollatzResearch.WordTrace tailWord_7480100 prefixEnd_7480100 3840886643696289308049653 := by
  unfold tailWord_7480100
  simp only [CollatzResearch.WordTrace]
  refine ⟨136410830100441337109094877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181881106800588449478793169 136410830100441337109094877)
  ·
    refine ⟨51154061287665501415910579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136410830100441337109094877 51154061287665501415910579)
    ·
      refine ⟨76731091931498252123865869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51154061287665501415910579 76731091931498252123865869)
      ·
        refine ⟨28774159474311844546449701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76731091931498252123865869 28774159474311844546449701)
        ·
          refine ⟨5395154901433470852459319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28774159474311844546449701 5395154901433470852459319)
          ·
            refine ⟨8092732352150206278688979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395154901433470852459319 8092732352150206278688979)
            ·
              refine ⟨12139098528225309418033469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092732352150206278688979 12139098528225309418033469)
              ·
                refine ⟨4552161948084491031762551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12139098528225309418033469 4552161948084491031762551)
                ·
                  refine ⟨6828242922126736547643827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552161948084491031762551 6828242922126736547643827)
                  ·
                    refine ⟨10242364383190104821465741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6828242922126736547643827 10242364383190104821465741)
                    ·
                      refine ⟨3840886643696289308049653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10242364383190104821465741 3840886643696289308049653)
                      ·
                        rfl

theorem cell23_7480100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_7480100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480100 prefixEnd_7480100 := by exact prefixLift 7480100
  have htrace : WordTrace (prefixWord ++ tailWord_7480100) baseStart_7480100 baseEnd_7480100 := by
    simpa [prefixWord, tailWord_7480100, baseEnd_7480100] using wordTrace_append hprefix tailTrace_7480100
  have hstable : (prefixWord ++ tailWord_7480100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480100).length < 2 ^ (prefixWord ++ tailWord_7480100).sum := by decide
  have hdescent : baseEnd_7480100 < baseStart_7480100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480129 : List Nat := [1, 2, 5, 3, 1, 1, 2, 8]
def baseStart_7480129 : Nat := 118140960795 + 7480129 * 2 ^ 59
def prefixEnd_7480129 : Nat := 4983230072969 + 3 ^ 40 * 7480129 * 2
def baseEnd_7480129 : Nat := 142255612393898877577297

theorem tailTrace_7480129 : CollatzResearch.WordTrace tailWord_7480129 prefixEnd_7480129 142255612393898877577297 := by
  unfold tailWord_7480129
  simp only [CollatzResearch.WordTrace]
  refine ⟨272822717917777612170995441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181881811945185074780663627 272822717917777612170995441)
  ·
    refine ⟨204617038438333209128246581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272822717917777612170995441 204617038438333209128246581)
    ·
      refine ⟨19182847353593738355773117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204617038438333209128246581 19182847353593738355773117)
      ·
        refine ⟨7193567757597651883414919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19182847353593738355773117 7193567757597651883414919)
        ·
          refine ⟨10790351636396477825122379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193567757597651883414919 10790351636396477825122379)
          ·
            refine ⟨16185527454594716737683569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790351636396477825122379 16185527454594716737683569)
            ·
              refine ⟨12139145590946037553262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16185527454594716737683569 12139145590946037553262677)
              ·
                refine ⟨142255612393898877577297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12139145590946037553262677 142255612393898877577297)
                ·
                  rfl

theorem cell23_7480129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 8].length) (baseStart_7480129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480129 prefixEnd_7480129 := by exact prefixLift 7480129
  have htrace : WordTrace (prefixWord ++ tailWord_7480129) baseStart_7480129 baseEnd_7480129 := by
    simpa [prefixWord, tailWord_7480129, baseEnd_7480129] using wordTrace_append hprefix tailTrace_7480129
  have hstable : (prefixWord ++ tailWord_7480129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480129).length < 2 ^ (prefixWord ++ tailWord_7480129).sum := by decide
  have hdescent : baseEnd_7480129 < baseStart_7480129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480149 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_7480149 : Nat := 118140960795 + 7480149 * 2 ^ 59
def prefixEnd_7480149 : Nat := 4983230072969 + 3 ^ 40 * 7480149 * 2
def baseEnd_7480149 : Nat := 3840911804248359616336927

theorem tailTrace_7480149 : CollatzResearch.WordTrace tailWord_7480149 prefixEnd_7480149 3840911804248359616336927 := by
  unfold tailWord_7480149
  simp only [CollatzResearch.WordTrace]
  refine ⟨272823447377705155586723501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181882298251803437057815667 272823447377705155586723501)
  ·
    refine ⟨102308792766639433345021313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272823447377705155586723501 102308792766639433345021313)
    ·
      refine ⟨76731594574979575008765985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102308792766639433345021313 76731594574979575008765985)
      ·
        refine ⟨57548695931234681256574489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76731594574979575008765985 57548695931234681256574489)
        ·
          refine ⟨43161521948426010942430867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57548695931234681256574489 43161521948426010942430867)
          ·
            refine ⟨64742282922639016413646301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43161521948426010942430867 64742282922639016413646301)
            ·
              refine ⟨24278356095989631155117363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64742282922639016413646301 24278356095989631155117363)
              ·
                refine ⟨36417534143984446732676045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24278356095989631155117363 36417534143984446732676045)
                ·
                  refine ⟨13656575303994167524753517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36417534143984446732676045 13656575303994167524753517)
                  ·
                    refine ⟨5121215738997812821782569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13656575303994167524753517 5121215738997812821782569)
                    ·
                      refine ⟨3840911804248359616336927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121215738997812821782569 3840911804248359616336927)
                      ·
                        rfl

theorem cell23_7480149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_7480149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480149 prefixEnd_7480149 := by exact prefixLift 7480149
  have htrace : WordTrace (prefixWord ++ tailWord_7480149) baseStart_7480149 baseEnd_7480149 := by
    simpa [prefixWord, tailWord_7480149, baseEnd_7480149] using wordTrace_append hprefix tailTrace_7480149
  have hstable : (prefixWord ++ tailWord_7480149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480149).length < 2 ^ (prefixWord ++ tailWord_7480149).sum := by decide
  have hdescent : baseEnd_7480149 < baseStart_7480149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480174 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_7480174 : Nat := 118140960795 + 7480174 * 2 ^ 59
def prefixEnd_7480174 : Nat := 4983230072969 + 3 ^ 40 * 7480174 * 2
def baseEnd_7480174 : Nat := 3840924641264722018524313

theorem tailTrace_7480174 : CollatzResearch.WordTrace tailWord_7480174 prefixEnd_7480174 3840924641264722018524313 := by
  unfold tailWord_7480174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103044900326823107047947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181882906135076389904255717 34103044900326823107047947)
  ·
    refine ⟨51154567350490234660571921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34103044900326823107047947 51154567350490234660571921)
    ·
      refine ⟨38365925512867675995428941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51154567350490234660571921 38365925512867675995428941)
      ·
        refine ⟨14387222067325378498285853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38365925512867675995428941 14387222067325378498285853)
        ·
          refine ⟨5395208275247016936857195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14387222067325378498285853 5395208275247016936857195)
          ·
            refine ⟨8092812412870525405285793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395208275247016936857195 8092812412870525405285793)
            ·
              refine ⟨6069609309652894053964345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092812412870525405285793 6069609309652894053964345)
              ·
                refine ⟨4552206982239670540473259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6069609309652894053964345 4552206982239670540473259)
                ·
                  refine ⟨6828310473359505810709889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552206982239670540473259 6828310473359505810709889)
                  ·
                    refine ⟨5121232855019629358032417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6828310473359505810709889 5121232855019629358032417)
                    ·
                      refine ⟨3840924641264722018524313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121232855019629358032417 3840924641264722018524313)
                      ·
                        rfl

theorem cell23_7480174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_7480174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480174 prefixEnd_7480174 := by exact prefixLift 7480174
  have htrace : WordTrace (prefixWord ++ tailWord_7480174) baseStart_7480174 baseEnd_7480174 := by
    simpa [prefixWord, tailWord_7480174, baseEnd_7480174] using wordTrace_append hprefix tailTrace_7480174
  have hstable : (prefixWord ++ tailWord_7480174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480174).length < 2 ^ (prefixWord ++ tailWord_7480174).sum := by decide
  have hdescent : baseEnd_7480174 < baseStart_7480174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480175 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_7480175 : Nat := 118140960795 + 7480175 * 2 ^ 59
def prefixEnd_7480175 : Nat := 4983230072969 + 3 ^ 40 * 7480175 * 2
def baseEnd_7480175 : Nat := 3840925154745376514611807

theorem tailTrace_7480175 : CollatzResearch.WordTrace tailWord_7480175 prefixEnd_7480175 3840925154745376514611807 := by
  unfold tailWord_7480175
  simp only [CollatzResearch.WordTrace]
  refine ⟨272824395675610962027169979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181882930450407308018113319 272824395675610962027169979)
  ·
    refine ⟨409236593513416443040754969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272824395675610962027169979 409236593513416443040754969)
    ·
      refine ⟨306927445135062332280566227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409236593513416443040754969 306927445135062332280566227)
      ·
        refine ⟨460391167702593498420849341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306927445135062332280566227 460391167702593498420849341)
        ·
          refine ⟨172646687888472561907818503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460391167702593498420849341 172646687888472561907818503)
          ·
            refine ⟨258970031832708842861727755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172646687888472561907818503 258970031832708842861727755)
            ·
              refine ⟨388455047749063264292591633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258970031832708842861727755 388455047749063264292591633)
              ·
                refine ⟨291341285811797448219443725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388455047749063264292591633 291341285811797448219443725)
                ·
                  refine ⟨109252982179424043082291397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291341285811797448219443725 109252982179424043082291397)
                  ·
                    refine ⟨20484934158642008077929637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109252982179424043082291397 20484934158642008077929637)
                    ·
                      refine ⟨3840925154745376514611807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20484934158642008077929637 3840925154745376514611807)
                      ·
                        rfl

theorem cell23_7480175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_7480175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480175 prefixEnd_7480175 := by exact prefixLift 7480175
  have htrace : WordTrace (prefixWord ++ tailWord_7480175) baseStart_7480175 baseEnd_7480175 := by
    simpa [prefixWord, tailWord_7480175, baseEnd_7480175] using wordTrace_append hprefix tailTrace_7480175
  have hstable : (prefixWord ++ tailWord_7480175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480175).length < 2 ^ (prefixWord ++ tailWord_7480175).sum := by decide
  have hdescent : baseEnd_7480175 < baseStart_7480175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480179 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 4, 2, 2]
def baseStart_7480179 : Nat := 118140960795 + 7480179 * 2 ^ 59
def prefixEnd_7480179 : Nat := 4983230072969 + 3 ^ 40 * 7480179 * 2
def baseEnd_7480179 : Nat := 3840927208667994498961789

theorem tailTrace_7480179 : CollatzResearch.WordTrace tailWord_7480179 prefixEnd_7480179 3840927208667994498961789 := by
  unfold tailWord_7480179
  simp only [CollatzResearch.WordTrace]
  refine ⟨272824541567596470710315591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181883027711730980473543727 272824541567596470710315591)
  ·
    refine ⟨409236812351394706065473387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272824541567596470710315591 409236812351394706065473387)
    ·
      refine ⟨613855218527092059098210081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409236812351394706065473387 613855218527092059098210081)
      ·
        refine ⟨460391413895319044323657561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613855218527092059098210081 460391413895319044323657561)
        ·
          refine ⟨345293560421489283242743171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460391413895319044323657561 345293560421489283242743171)
          ·
            refine ⟨517940340632233924864114757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345293560421489283242743171 517940340632233924864114757)
            ·
              refine ⟨97113813868543860912021517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517940340632233924864114757 97113813868543860912021517)
              ·
                refine ⟨36417680200703947842008069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97113813868543860912021517 36417680200703947842008069)
                ·
                  refine ⟨6828315037631990220376513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36417680200703947842008069 6828315037631990220376513)
                  ·
                    refine ⟨5121236278223992665282385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6828315037631990220376513 5121236278223992665282385)
                    ·
                      refine ⟨3840927208667994498961789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121236278223992665282385 3840927208667994498961789)
                      ·
                        rfl

theorem cell23_7480179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2, 2].length) (baseStart_7480179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480179 prefixEnd_7480179 := by exact prefixLift 7480179
  have htrace : WordTrace (prefixWord ++ tailWord_7480179) baseStart_7480179 baseEnd_7480179 := by
    simpa [prefixWord, tailWord_7480179, baseEnd_7480179] using wordTrace_append hprefix tailTrace_7480179
  have hstable : (prefixWord ++ tailWord_7480179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480179).length < 2 ^ (prefixWord ++ tailWord_7480179).sum := by decide
  have hdescent : baseEnd_7480179 < baseStart_7480179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480202 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_7480202 : Nat := 118140960795 + 7480202 * 2 ^ 59
def prefixEnd_7480202 : Nat := 4983230072969 + 3 ^ 40 * 7480202 * 2
def baseEnd_7480202 : Nat := 426771002080338656552687

theorem tailTrace_7480202 : CollatzResearch.WordTrace tailWord_7480202 prefixEnd_7480202 426771002080338656552687 := by
  unfold tailWord_7480202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68206345111628286409600715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181883586964342097092268573 68206345111628286409600715)
  ·
    refine ⟨102309517667442429614401073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68206345111628286409600715 102309517667442429614401073)
    ·
      refine ⟨76732138250581822210800805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102309517667442429614401073 76732138250581822210800805)
      ·
        refine ⟨14387275921984091664525151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76732138250581822210800805 14387275921984091664525151)
        ·
          refine ⟨21580913882976137496787727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14387275921984091664525151 21580913882976137496787727)
          ·
            refine ⟨32371370824464206245181591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21580913882976137496787727 32371370824464206245181591)
            ·
              refine ⟨48557056236696309367772387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32371370824464206245181591 48557056236696309367772387)
              ·
                refine ⟨72835584355044464051658581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48557056236696309367772387 72835584355044464051658581)
                ·
                  refine ⟨426771002080338656552687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72835584355044464051658581 426771002080338656552687)
                  ·
                    rfl

theorem cell23_7480202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_7480202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480202 prefixEnd_7480202 := by exact prefixLift 7480202
  have htrace : WordTrace (prefixWord ++ tailWord_7480202) baseStart_7480202 baseEnd_7480202 := by
    simpa [prefixWord, tailWord_7480202, baseEnd_7480202] using wordTrace_append hprefix tailTrace_7480202
  have hstable : (prefixWord ++ tailWord_7480202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480202).length < 2 ^ (prefixWord ++ tailWord_7480202).sum := by decide
  have hdescent : baseEnd_7480202 < baseStart_7480202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480296 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 1, 4]
def baseStart_7480296 : Nat := 118140960795 + 7480296 * 2 ^ 59
def prefixEnd_7480296 : Nat := 4983230072969 + 3 ^ 40 * 7480296 * 2
def baseEnd_7480296 : Nat := 1280329095301523513732917

theorem tailTrace_7480296 : CollatzResearch.WordTrace tailWord_7480296 prefixEnd_7480296 1280329095301523513732917 := by
  unfold tailWord_7480296
  simp only [CollatzResearch.WordTrace]
  refine ⟨136414404454086299846162371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181885872605448399794883161 136414404454086299846162371)
  ·
    refine ⟨204621606681129449769243557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136414404454086299846162371 204621606681129449769243557)
    ·
      refine ⟨38366551252711771831733167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204621606681129449769243557 38366551252711771831733167)
      ·
        refine ⟨57549826879067657747599751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38366551252711771831733167 57549826879067657747599751)
        ·
          refine ⟨86324740318601486621399627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57549826879067657747599751 86324740318601486621399627)
          ·
            refine ⟨129487110477902229932099441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86324740318601486621399627 129487110477902229932099441)
            ·
              refine ⟨97115332858426672449074581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129487110477902229932099441 97115332858426672449074581)
              ·
                refine ⟨4552281227738750271050371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97115332858426672449074581 4552281227738750271050371)
                ·
                  refine ⟨6828421841608125406575557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552281227738750271050371 6828421841608125406575557)
                  ·
                    refine ⟨1280329095301523513732917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6828421841608125406575557 1280329095301523513732917)
                    ·
                      rfl

theorem cell23_7480296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_7480296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480296 prefixEnd_7480296 := by exact prefixLift 7480296
  have htrace : WordTrace (prefixWord ++ tailWord_7480296) baseStart_7480296 baseEnd_7480296 := by
    simpa [prefixWord, tailWord_7480296, baseEnd_7480296] using wordTrace_append hprefix tailTrace_7480296
  have hstable : (prefixWord ++ tailWord_7480296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480296).length < 2 ^ (prefixWord ++ tailWord_7480296).sum := by decide
  have hdescent : baseEnd_7480296 < baseStart_7480296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480329 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 5, 2]
def baseStart_7480329 : Nat := 118140960795 + 7480329 * 2 ^ 59
def prefixEnd_7480329 : Nat := 4983230072969 + 3 ^ 40 * 7480329 * 2
def baseEnd_7480329 : Nat := 3841004230766168912086099

theorem tailTrace_7480329 : CollatzResearch.WordTrace tailWord_7480329 prefixEnd_7480329 3841004230766168912086099 := by
  unfold tailWord_7480329
  simp only [CollatzResearch.WordTrace]
  refine ⟨272830012517053046328276041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181886675011368697552184027 272830012517053046328276041)
  ·
    refine ⟨204622509387789784746207031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272830012517053046328276041 204622509387789784746207031)
    ·
      refine ⟨306933764081684677119310547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204622509387789784746207031 306933764081684677119310547)
      ·
        refine ⟨460400646122527015678965821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306933764081684677119310547 460400646122527015678965821)
        ·
          refine ⟨172650242295947630879612183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460400646122527015678965821 172650242295947630879612183)
          ·
            refine ⟨258975363443921446319418275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172650242295947630879612183 258975363443921446319418275)
            ·
              refine ⟨388463045165882169479127413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258975363443921446319418275 388463045165882169479127413)
              ·
                refine ⟨36418410484301453388668195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388463045165882169479127413 36418410484301453388668195)
                ·
                  refine ⟨54627615726452180083002293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36418410484301453388668195 54627615726452180083002293)
                  ·
                    refine ⟨5121338974354891882781465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54627615726452180083002293 5121338974354891882781465)
                    ·
                      refine ⟨3841004230766168912086099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121338974354891882781465 3841004230766168912086099)
                      ·
                        rfl

theorem cell23_7480329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5, 2].length) (baseStart_7480329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480329 prefixEnd_7480329 := by exact prefixLift 7480329
  have htrace : WordTrace (prefixWord ++ tailWord_7480329) baseStart_7480329 baseEnd_7480329 := by
    simpa [prefixWord, tailWord_7480329, baseEnd_7480329] using wordTrace_append hprefix tailTrace_7480329
  have hstable : (prefixWord ++ tailWord_7480329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480329).length < 2 ^ (prefixWord ++ tailWord_7480329).sum := by decide
  have hdescent : baseEnd_7480329 < baseStart_7480329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480346 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_7480346 : Nat := 118140960795 + 7480346 * 2 ^ 59
def prefixEnd_7480346 : Nat := 4983230072969 + 3 ^ 40 * 7480346 * 2
def baseEnd_7480346 : Nat := 3841012959937295345573521

theorem tailTrace_7480346 : CollatzResearch.WordTrace tailWord_7480346 prefixEnd_7480346 3841012959937295345573521 := by
  unfold tailWord_7480346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68207658139497864557911223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181887088371994305487763261 68207658139497864557911223)
  ·
    refine ⟨102311487209246796836866835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68207658139497864557911223 102311487209246796836866835)
    ·
      refine ⟨153467230813870195255300253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102311487209246796836866835 153467230813870195255300253)
      ·
        refine ⟨57550211555201323220737595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153467230813870195255300253 57550211555201323220737595)
        ·
          refine ⟨86325317332801984831106393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57550211555201323220737595 86325317332801984831106393)
          ·
            refine ⟨64743987999601488623329795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86325317332801984831106393 64743987999601488623329795)
            ·
              refine ⟨97115981999402232934994693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64743987999601488623329795 97115981999402232934994693)
              ·
                refine ⟨18209246624887918675311505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97115981999402232934994693 18209246624887918675311505)
                ·
                  refine ⟨13656934968665939006483629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18209246624887918675311505 13656934968665939006483629)
                  ·
                    refine ⟨5121350613249727127431361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13656934968665939006483629 5121350613249727127431361)
                    ·
                      refine ⟨3841012959937295345573521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121350613249727127431361 3841012959937295345573521)
                      ·
                        rfl

theorem cell23_7480346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_7480346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480346 prefixEnd_7480346 := by exact prefixLift 7480346
  have htrace : WordTrace (prefixWord ++ tailWord_7480346) baseStart_7480346 baseEnd_7480346 := by
    simpa [prefixWord, tailWord_7480346, baseEnd_7480346] using wordTrace_append hprefix tailTrace_7480346
  have hstable : (prefixWord ++ tailWord_7480346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480346).length < 2 ^ (prefixWord ++ tailWord_7480346).sum := by decide
  have hdescent : baseEnd_7480346 < baseStart_7480346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480369 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_7480369 : Nat := 118140960795 + 7480369 * 2 ^ 59
def prefixEnd_7480369 : Nat := 4983230072969 + 3 ^ 40 * 7480369 * 2
def baseEnd_7480369 : Nat := 1280341589997449585195305

theorem tailTrace_7480369 : CollatzResearch.WordTrace tailWord_7480369 prefixEnd_7480369 1280341589997449585195305 := by
  unfold tailWord_7480369
  simp only [CollatzResearch.WordTrace]
  refine ⟨272831471436908133159732161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181887647624605422106488107 272831471436908133159732161)
  ·
    refine ⟨204623603577681099869799121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272831471436908133159732161 204623603577681099869799121)
    ·
      refine ⟨153467702683260824902349341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204623603577681099869799121 153467702683260824902349341)
      ·
        refine ⟨57550388506222809338381003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153467702683260824902349341 57550388506222809338381003)
        ·
          refine ⟨86325582759334214007571505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57550388506222809338381003 86325582759334214007571505)
          ·
            refine ⟨64744187069500660505678629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86325582759334214007571505 64744187069500660505678629)
            ·
              refine ⟨12139535075531373844814743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64744187069500660505678629 12139535075531373844814743)
              ·
                refine ⟨18209302613297060767222115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12139535075531373844814743 18209302613297060767222115)
                ·
                  refine ⟨27313953919945591150833173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18209302613297060767222115 27313953919945591150833173)
                  ·
                    refine ⟨1280341589997449585195305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27313953919945591150833173 1280341589997449585195305)
                    ·
                      rfl

theorem cell23_7480369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_7480369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480369 prefixEnd_7480369 := by exact prefixLift 7480369
  have htrace : WordTrace (prefixWord ++ tailWord_7480369) baseStart_7480369 baseEnd_7480369 := by
    simpa [prefixWord, tailWord_7480369, baseEnd_7480369] using wordTrace_append hprefix tailTrace_7480369
  have hstable : (prefixWord ++ tailWord_7480369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480369).length < 2 ^ (prefixWord ++ tailWord_7480369).sum := by decide
  have hdescent : baseEnd_7480369 < baseStart_7480369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480389 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_7480389 : Nat := 118140960795 + 7480389 * 2 ^ 59
def prefixEnd_7480389 : Nat := 4983230072969 + 3 ^ 40 * 7480389 * 2
def baseEnd_7480389 : Nat := 3841035039605438677335823

theorem tailTrace_7480389 : CollatzResearch.WordTrace tailWord_7480389 prefixEnd_7480389 3841035039605438677335823 := by
  unfold tailWord_7480389
  simp only [CollatzResearch.WordTrace]
  refine ⟨272832200896835676575460221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181888133931223784383640147 272832200896835676575460221)
  ·
    refine ⟨102312075336313378715797583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272832200896835676575460221 102312075336313378715797583)
    ·
      refine ⟨153468113004470068073696375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102312075336313378715797583 153468113004470068073696375)
      ·
        refine ⟨230202169506705102110544563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153468113004470068073696375 230202169506705102110544563)
        ·
          refine ⟨345303254260057653165816845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230202169506705102110544563 345303254260057653165816845)
          ·
            refine ⟨129488720347521619937181317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345303254260057653165816845 129488720347521619937181317)
            ·
              refine ⟨24279135065160303738221497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129488720347521619937181317 24279135065160303738221497)
              ·
                refine ⟨18209351298870227803666123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24279135065160303738221497 18209351298870227803666123)
                ·
                  refine ⟨27314026948305341705499185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18209351298870227803666123 27314026948305341705499185)
                  ·
                    refine ⟨20485520211229006279124389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27314026948305341705499185 20485520211229006279124389)
                    ·
                      refine ⟨3841035039605438677335823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20485520211229006279124389 3841035039605438677335823)
                      ·
                        rfl

theorem cell23_7480389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_7480389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480389 prefixEnd_7480389 := by exact prefixLift 7480389
  have htrace : WordTrace (prefixWord ++ tailWord_7480389) baseStart_7480389 baseEnd_7480389 := by
    simpa [prefixWord, tailWord_7480389, baseEnd_7480389] using wordTrace_append hprefix tailTrace_7480389
  have hstable : (prefixWord ++ tailWord_7480389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480389).length < 2 ^ (prefixWord ++ tailWord_7480389).sum := by decide
  have hdescent : baseEnd_7480389 < baseStart_7480389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480390 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_7480390 : Nat := 118140960795 + 7480390 * 2 ^ 59
def prefixEnd_7480390 : Nat := 4983230072969 + 3 ^ 40 * 7480390 * 2
def baseEnd_7480390 : Nat := 1280345184362031057807773

theorem tailTrace_7480390 : CollatzResearch.WordTrace tailWord_7480390 prefixEnd_7480390 1280345184362031057807773 := by
  unfold tailWord_7480390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526007417807251679570207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181888158246554702497497749 8526007417807251679570207)
  ·
    refine ⟨12789011126710877519355311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8526007417807251679570207 12789011126710877519355311)
    ·
      refine ⟨19183516690066316279032967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12789011126710877519355311 19183516690066316279032967)
      ·
        refine ⟨28775275035099474418549451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19183516690066316279032967 28775275035099474418549451)
        ·
          refine ⟨43162912552649211627824177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28775275035099474418549451 43162912552649211627824177)
          ·
            refine ⟨32372184414486908720868133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43162912552649211627824177 32372184414486908720868133)
            ·
              refine ⟨6069784577716295385162775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32372184414486908720868133 6069784577716295385162775)
              ·
                refine ⟨9104676866574443077744163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069784577716295385162775 9104676866574443077744163)
                ·
                  refine ⟨13657015299861664616616245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9104676866574443077744163 13657015299861664616616245)
                  ·
                    refine ⟨1280345184362031057807773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13657015299861664616616245 1280345184362031057807773)
                    ·
                      rfl

theorem cell23_7480390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_7480390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480390 prefixEnd_7480390 := by exact prefixLift 7480390
  have htrace : WordTrace (prefixWord ++ tailWord_7480390) baseStart_7480390 baseEnd_7480390 := by
    simpa [prefixWord, tailWord_7480390, baseEnd_7480390] using wordTrace_append hprefix tailTrace_7480390
  have hstable : (prefixWord ++ tailWord_7480390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480390).length < 2 ^ (prefixWord ++ tailWord_7480390).sum := by decide
  have hdescent : baseEnd_7480390 < baseStart_7480390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480413 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7480413 : Nat := 118140960795 + 7480413 * 2 ^ 59
def prefixEnd_7480413 : Nat := 4983230072969 + 3 ^ 40 * 7480413 * 2
def baseEnd_7480413 : Nat := 3841047363141146583435713

theorem tailTrace_7480413 : CollatzResearch.WordTrace tailWord_7480413 prefixEnd_7480413 3841047363141146583435713 := by
  unfold tailWord_7480413
  simp only [CollatzResearch.WordTrace]
  refine ⟨272833076248748728674333893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181888717499165819116222595 272833076248748728674333893)
  ·
    refine ⟨51156201796640386626437605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272833076248748728674333893 51156201796640386626437605)
    ·
      refine ⟨9591787836870072492457051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51156201796640386626437605 9591787836870072492457051)
      ·
        refine ⟨14387681755305108738685577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9591787836870072492457051 14387681755305108738685577)
        ·
          refine ⟨10790761316478831554014183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14387681755305108738685577 10790761316478831554014183)
          ·
            refine ⟨16186141974718247331021275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790761316478831554014183 16186141974718247331021275)
            ·
              refine ⟨24279212962077370996531913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186141974718247331021275 24279212962077370996531913)
              ·
                refine ⟨18209409721558028247398935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24279212962077370996531913 18209409721558028247398935)
                ·
                  refine ⟨27314114582337042371098403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18209409721558028247398935 27314114582337042371098403)
                  ·
                    refine ⟨40971171873505563556647605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27314114582337042371098403 40971171873505563556647605)
                    ·
                      refine ⟨3841047363141146583435713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40971171873505563556647605 3841047363141146583435713)
                      ·
                        rfl

theorem cell23_7480413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7480413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480413 prefixEnd_7480413 := by exact prefixLift 7480413
  have htrace : WordTrace (prefixWord ++ tailWord_7480413) baseStart_7480413 baseEnd_7480413 := by
    simpa [prefixWord, tailWord_7480413, baseEnd_7480413] using wordTrace_append hprefix tailTrace_7480413
  have hstable : (prefixWord ++ tailWord_7480413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480413).length < 2 ^ (prefixWord ++ tailWord_7480413).sum := by decide
  have hdescent : baseEnd_7480413 < baseStart_7480413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480487 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7480487 : Nat := 118140960795 + 7480487 * 2 ^ 59
def prefixEnd_7480487 : Nat := 4983230072969 + 3 ^ 40 * 7480487 * 2
def baseEnd_7480487 : Nat := 3841085360709579293910373

theorem tailTrace_7480487 : CollatzResearch.WordTrace tailWord_7480487 prefixEnd_7480487 3841085360709579293910373 := by
  unfold tailWord_7480487
  simp only [CollatzResearch.WordTrace]
  refine ⟨272835775250480639312527715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181890516833653759541685143 272835775250480639312527715)
  ·
    refine ⟨409253662875720958968791573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272835775250480639312527715 409253662875720958968791573)
    ·
      refine ⟨19183765447299419951662105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 409253662875720958968791573 19183765447299419951662105)
      ·
        refine ⟨14387824085474564963746579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19183765447299419951662105 14387824085474564963746579)
        ·
          refine ⟨21581736128211847445619869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14387824085474564963746579 21581736128211847445619869)
          ·
            refine ⟨8093151048079442792107451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21581736128211847445619869 8093151048079442792107451)
            ·
              refine ⟨12139726572119164188161177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093151048079442792107451 12139726572119164188161177)
              ·
                refine ⟨9104794929089373141120883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12139726572119164188161177 9104794929089373141120883)
                ·
                  refine ⟨13657192393634059711681325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9104794929089373141120883 13657192393634059711681325)
                  ·
                    refine ⟨5121447147612772391880497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13657192393634059711681325 5121447147612772391880497)
                    ·
                      refine ⟨3841085360709579293910373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121447147612772391880497 3841085360709579293910373)
                      ·
                        rfl

theorem cell23_7480487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7480487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480487 prefixEnd_7480487 := by exact prefixLift 7480487
  have htrace : WordTrace (prefixWord ++ tailWord_7480487) baseStart_7480487 baseEnd_7480487 := by
    simpa [prefixWord, tailWord_7480487, baseEnd_7480487] using wordTrace_append hprefix tailTrace_7480487
  have hstable : (prefixWord ++ tailWord_7480487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480487).length < 2 ^ (prefixWord ++ tailWord_7480487).sum := by decide
  have hdescent : baseEnd_7480487 < baseStart_7480487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480506 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_7480506 : Nat := 118140960795 + 7480506 * 2 ^ 59
def prefixEnd_7480506 : Nat := 4983230072969 + 3 ^ 40 * 7480506 * 2
def baseEnd_7480506 : Nat := 426788346315779413285865

theorem tailTrace_7480506 : CollatzResearch.WordTrace tailWord_7480506 prefixEnd_7480506 426788346315779413285865 := by
  unfold tailWord_7480506
  simp only [CollatzResearch.WordTrace]
  refine ⟨68209117059352951389367343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181890978824941203704979581 68209117059352951389367343)
  ·
    refine ⟨102313675589029427084051015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68209117059352951389367343 102313675589029427084051015)
    ·
      refine ⟨153470513383544140626076523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102313675589029427084051015 153470513383544140626076523)
      ·
        refine ⟨230205770075316210939114785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153470513383544140626076523 230205770075316210939114785)
        ·
          refine ⟨172654327556487158204336089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230205770075316210939114785 172654327556487158204336089)
          ·
            refine ⟨129490745667365368653252067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172654327556487158204336089 129490745667365368653252067)
            ·
              refine ⟨194236118501048052979878101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129490745667365368653252067 194236118501048052979878101)
              ·
                refine ⟨4552409027368313741715893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194236118501048052979878101 4552409027368313741715893)
                ·
                  refine ⟨426788346315779413285865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4552409027368313741715893 426788346315779413285865)
                  ·
                    rfl

theorem cell23_7480506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_7480506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480506 prefixEnd_7480506 := by exact prefixLift 7480506
  have htrace : WordTrace (prefixWord ++ tailWord_7480506) baseStart_7480506 baseEnd_7480506 := by
    simpa [prefixWord, tailWord_7480506, baseEnd_7480506] using wordTrace_append hprefix tailTrace_7480506
  have hstable : (prefixWord ++ tailWord_7480506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480506).length < 2 ^ (prefixWord ++ tailWord_7480506).sum := by decide
  have hdescent : baseEnd_7480506 < baseStart_7480506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480533 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7480533 : Nat := 118140960795 + 7480533 * 2 ^ 59
def prefixEnd_7480533 : Nat := 4983230072969 + 3 ^ 40 * 7480533 * 2
def baseEnd_7480533 : Nat := 3841108980819686113935161

theorem tailTrace_7480533 : CollatzResearch.WordTrace tailWord_7480533 prefixEnd_7480533 3841108980819686113935161 := by
  unfold tailWord_7480533
  simp only [CollatzResearch.WordTrace]
  refine ⟨272837453008313989168702253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181891635338875992779134835 272837453008313989168702253)
  ·
    refine ⟨102314044878117745938263345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272837453008313989168702253 102314044878117745938263345)
    ·
      refine ⟨76735533658588309453697509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102314044878117745938263345 76735533658588309453697509)
      ·
        refine ⟨14387912560985308022568283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76735533658588309453697509 14387912560985308022568283)
        ·
          refine ⟨21581868841477962033852425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14387912560985308022568283 21581868841477962033852425)
          ·
            refine ⟨16186401631108471525389319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21581868841477962033852425 16186401631108471525389319)
            ·
              refine ⟨24279602446662707288083979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186401631108471525389319 24279602446662707288083979)
              ·
                refine ⟨36419403669994060932125969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24279602446662707288083979 36419403669994060932125969)
                ·
                  refine ⟨27314552752495545699094477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36419403669994060932125969 27314552752495545699094477)
                  ·
                    refine ⟨10242957282185829637160429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27314552752495545699094477 10242957282185829637160429)
                    ·
                      refine ⟨3841108980819686113935161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10242957282185829637160429 3841108980819686113935161)
                      ·
                        rfl

theorem cell23_7480533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7480533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480533 prefixEnd_7480533 := by exact prefixLift 7480533
  have htrace : WordTrace (prefixWord ++ tailWord_7480533) baseStart_7480533 baseEnd_7480533 := by
    simpa [prefixWord, tailWord_7480533, baseEnd_7480533] using wordTrace_append hprefix tailTrace_7480533
  have hstable : (prefixWord ++ tailWord_7480533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480533).length < 2 ^ (prefixWord ++ tailWord_7480533).sum := by decide
  have hdescent : baseEnd_7480533 < baseStart_7480533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480556 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_7480556 : Nat := 118140960795 + 7480556 * 2 ^ 59
def prefixEnd_7480556 : Nat := 4983230072969 + 3 ^ 40 * 7480556 * 2
def baseEnd_7480556 : Nat := 3841120790874739523947555

theorem tailTrace_7480556 : CollatzResearch.WordTrace tailWord_7480556 prefixEnd_7480556 3841120790874739523947555 := by
  unfold tailWord_7480556
  simp only [CollatzResearch.WordTrace]
  refine ⟨136419145943615332048394761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181892194591487109397859681 136419145943615332048394761)
  ·
    refine ⟨102314359457711499036296071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136419145943615332048394761 102314359457711499036296071)
    ·
      refine ⟨153471539186567248554444107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102314359457711499036296071 153471539186567248554444107)
      ·
        refine ⟨230207308779850872831666161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153471539186567248554444107 230207308779850872831666161)
        ·
          refine ⟨172655481584888154623749621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230207308779850872831666161 172655481584888154623749621)
          ·
            refine ⟨16186451398583264495976527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172655481584888154623749621 16186451398583264495976527)
            ·
              refine ⟨24279677097874896743964791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186451398583264495976527 24279677097874896743964791)
              ·
                refine ⟨36419515646812345115947187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24279677097874896743964791 36419515646812345115947187)
                ·
                  refine ⟨54629273470218517673920781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36419515646812345115947187 54629273470218517673920781)
                  ·
                    refine ⟨20485977551331944127720293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54629273470218517673920781 20485977551331944127720293)
                    ·
                      refine ⟨3841120790874739523947555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20485977551331944127720293 3841120790874739523947555)
                      ·
                        rfl

theorem cell23_7480556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_7480556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480556 prefixEnd_7480556 := by exact prefixLift 7480556
  have htrace : WordTrace (prefixWord ++ tailWord_7480556) baseStart_7480556 baseEnd_7480556 := by
    simpa [prefixWord, tailWord_7480556, baseEnd_7480556] using wordTrace_append hprefix tailTrace_7480556
  have hstable : (prefixWord ++ tailWord_7480556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480556).length < 2 ^ (prefixWord ++ tailWord_7480556).sum := by decide
  have hdescent : baseEnd_7480556 < baseStart_7480556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480569 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7480569 : Nat := 118140960795 + 7480569 * 2 ^ 59
def prefixEnd_7480569 : Nat := 4983230072969 + 3 ^ 40 * 7480569 * 2
def baseEnd_7480569 : Nat := 3841127466123247973084995

theorem tailTrace_7480569 : CollatzResearch.WordTrace tailWord_7480569 prefixEnd_7480569 3841127466123247973084995 := by
  unfold tailWord_7480569
  simp only [CollatzResearch.WordTrace]
  refine ⟨272838766036183567317012761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181892510690789044878008507 272838766036183567317012761)
  ·
    refine ⟨204629074527137675487759571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272838766036183567317012761 204629074527137675487759571)
    ·
      refine ⟨306943611790706513231639357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204629074527137675487759571 306943611790706513231639357)
      ·
        refine ⟨115103854421514942461864759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306943611790706513231639357 115103854421514942461864759)
        ·
          refine ⟨172655781632272413692797139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115103854421514942461864759 172655781632272413692797139)
          ·
            refine ⟨258983672448408620539195709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172655781632272413692797139 258983672448408620539195709)
            ·
              refine ⟨97118877168153232702198391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258983672448408620539195709 97118877168153232702198391)
              ·
                refine ⟨145678315752229849053297587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97118877168153232702198391 145678315752229849053297587)
                ·
                  refine ⟨218517473628344773579946381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145678315752229849053297587 218517473628344773579946381)
                  ·
                    refine ⟨81944052610629290092479893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218517473628344773579946381 81944052610629290092479893)
                    ·
                      refine ⟨3841127466123247973084995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81944052610629290092479893 3841127466123247973084995)
                      ·
                        rfl

theorem cell23_7480569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7480569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480569 prefixEnd_7480569 := by exact prefixLift 7480569
  have htrace : WordTrace (prefixWord ++ tailWord_7480569) baseStart_7480569 baseEnd_7480569 := by
    simpa [prefixWord, tailWord_7480569, baseEnd_7480569] using wordTrace_append hprefix tailTrace_7480569
  have hstable : (prefixWord ++ tailWord_7480569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480569).length < 2 ^ (prefixWord ++ tailWord_7480569).sum := by decide
  have hdescent : baseEnd_7480569 < baseStart_7480569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480576 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_7480576 : Nat := 118140960795 + 7480576 * 2 ^ 59
def prefixEnd_7480576 : Nat := 4983230072969 + 3 ^ 40 * 7480576 * 2
def baseEnd_7480576 : Nat := 3841131060487829445697463

theorem tailTrace_7480576 : CollatzResearch.WordTrace tailWord_7480576 prefixEnd_7480576 3841131060487829445697463 := by
  unfold tailWord_7480576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136419510673579103756258791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181892680898105471675011721 136419510673579103756258791)
  ·
    refine ⟨204629266010368655634388187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136419510673579103756258791 204629266010368655634388187)
    ·
      refine ⟨306943899015552983451582281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204629266010368655634388187 306943899015552983451582281)
      ·
        refine ⟨230207924261664737588686711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306943899015552983451582281 230207924261664737588686711)
        ·
          refine ⟨345311886392497106383030067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230207924261664737588686711 345311886392497106383030067)
          ·
            refine ⟨517967829588745659574545101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345311886392497106383030067 517967829588745659574545101)
            ·
              refine ⟨194237936095779622340454413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517967829588745659574545101 194237936095779622340454413)
              ·
                refine ⟨72839226035917358377670405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194237936095779622340454413 72839226035917358377670405)
                ·
                  refine ⟨13657354881734504695813201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72839226035917358377670405 13657354881734504695813201)
                  ·
                    refine ⟨10243016161300878521859901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13657354881734504695813201 10243016161300878521859901)
                    ·
                      refine ⟨3841131060487829445697463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243016161300878521859901 3841131060487829445697463)
                      ·
                        rfl

theorem cell23_7480576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_7480576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480576 prefixEnd_7480576 := by exact prefixLift 7480576
  have htrace : WordTrace (prefixWord ++ tailWord_7480576) baseStart_7480576 baseEnd_7480576 := by
    simpa [prefixWord, tailWord_7480576, baseEnd_7480576] using wordTrace_append hprefix tailTrace_7480576
  have hstable : (prefixWord ++ tailWord_7480576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480576).length < 2 ^ (prefixWord ++ tailWord_7480576).sum := by decide
  have hdescent : baseEnd_7480576 < baseStart_7480576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480619 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_7480619 : Nat := 118140960795 + 7480619 * 2 ^ 59
def prefixEnd_7480619 : Nat := 4983230072969 + 3 ^ 40 * 7480619 * 2
def baseEnd_7480619 : Nat := 3841153140155972777459765

theorem tailTrace_7480619 : CollatzResearch.WordTrace tailWord_7480619 prefixEnd_7480619 3841153140155972777459765 := by
  unfold tailWord_7480619
  simp only [CollatzResearch.WordTrace]
  refine ⟨272840589686002425856332911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181893726457334950570888607 272840589686002425856332911)
  ·
    refine ⟨409260884529003638784499367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272840589686002425856332911 409260884529003638784499367)
    ·
      refine ⟨613891326793505458176749051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409260884529003638784499367 613891326793505458176749051)
      ·
        refine ⟨920836990190258187265123577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613891326793505458176749051 920836990190258187265123577)
        ·
          refine ⟨690627742642693640448842683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920836990190258187265123577 690627742642693640448842683)
          ·
            refine ⟨1035941613964040460673264025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690627742642693640448842683 1035941613964040460673264025)
            ·
              refine ⟨776956210473030345504948019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035941613964040460673264025 776956210473030345504948019)
              ·
                refine ⟨1165434315709545518257422029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776956210473030345504948019 1165434315709545518257422029)
                ·
                  refine ⟨437037868391079569346533261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165434315709545518257422029 437037868391079569346533261)
                  ·
                    refine ⟨163889200646654838504949973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437037868391079569346533261 163889200646654838504949973)
                    ·
                      refine ⟨3841153140155972777459765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163889200646654838504949973 3841153140155972777459765)
                      ·
                        rfl

theorem cell23_7480619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_7480619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480619 prefixEnd_7480619 := by exact prefixLift 7480619
  have htrace : WordTrace (prefixWord ++ tailWord_7480619) baseStart_7480619 baseEnd_7480619 := by
    simpa [prefixWord, tailWord_7480619, baseEnd_7480619] using wordTrace_append hprefix tailTrace_7480619
  have hstable : (prefixWord ++ tailWord_7480619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480619).length < 2 ^ (prefixWord ++ tailWord_7480619).sum := by decide
  have hdescent : baseEnd_7480619 < baseStart_7480619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480656 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_7480656 : Nat := 118140960795 + 7480656 * 2 ^ 59
def prefixEnd_7480656 : Nat := 4983230072969 + 3 ^ 40 * 7480656 * 2
def baseEnd_7480656 : Nat := 1280390712980063044232365

theorem tailTrace_7480656 : CollatzResearch.WordTrace tailWord_7480656 prefixEnd_7480656 1280390712980063044232365 := by
  unfold tailWord_7480656
  simp only [CollatzResearch.WordTrace]
  refine ⟨136420969593434190587714911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181894626124578920783619881 136420969593434190587714911)
  ·
    refine ⟨204631454390151285881572367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136420969593434190587714911 204631454390151285881572367)
    ·
      refine ⟨306947181585226928822358551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204631454390151285881572367 306947181585226928822358551)
      ·
        refine ⟨460420772377840393233537827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306947181585226928822358551 460420772377840393233537827)
        ·
          refine ⟨690631158566760589850306741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460420772377840393233537827 690631158566760589850306741)
          ·
            refine ⟨64746671115633805298466257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 690631158566760589850306741 64746671115633805298466257)
            ·
              refine ⟨48560003336725353973849693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64746671115633805298466257 48560003336725353973849693)
              ·
                refine ⟨18210001251272007740193635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48560003336725353973849693 18210001251272007740193635)
                ·
                  refine ⟨27315001876908011610290453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18210001251272007740193635 27315001876908011610290453)
                  ·
                    refine ⟨1280390712980063044232365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27315001876908011610290453 1280390712980063044232365)
                    ·
                      rfl

theorem cell23_7480656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_7480656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480656 prefixEnd_7480656 := by exact prefixLift 7480656
  have htrace : WordTrace (prefixWord ++ tailWord_7480656) baseStart_7480656 baseEnd_7480656 := by
    simpa [prefixWord, tailWord_7480656, baseEnd_7480656] using wordTrace_append hprefix tailTrace_7480656
  have hstable : (prefixWord ++ tailWord_7480656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480656).length < 2 ^ (prefixWord ++ tailWord_7480656).sum := by decide
  have hdescent : baseEnd_7480656 < baseStart_7480656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480663 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_7480663 : Nat := 118140960795 + 7480663 * 2 ^ 59
def prefixEnd_7480663 : Nat := 4983230072969 + 3 ^ 40 * 7480663 * 2
def baseEnd_7480663 : Nat := 3841175733304770605309563

theorem tailTrace_7480663 : CollatzResearch.WordTrace tailWord_7480663 prefixEnd_7480663 3841175733304770605309563 := by
  unfold tailWord_7480663
  simp only [CollatzResearch.WordTrace]
  refine ⟨272842194497843021370934643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181894796331895347580623095 272842194497843021370934643)
  ·
    refine ⟨409263291746764532056401965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272842194497843021370934643 409263291746764532056401965)
    ·
      refine ⟨153473734405036699521150737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409263291746764532056401965 153473734405036699521150737)
      ·
        refine ⟨115105300803777524640863053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153473734405036699521150737 115105300803777524640863053)
        ·
          refine ⟨43164487801416571740323645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115105300803777524640863053 43164487801416571740323645)
          ·
            refine ⟨16186682925531214402621367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43164487801416571740323645 16186682925531214402621367)
            ·
              refine ⟨24280024388296821603932051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186682925531214402621367 24280024388296821603932051)
              ·
                refine ⟨36420036582445232405898077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24280024388296821603932051 36420036582445232405898077)
                ·
                  refine ⟨13657513718416962152211779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36420036582445232405898077 13657513718416962152211779)
                  ·
                    refine ⟨20486270577625443228317669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13657513718416962152211779 20486270577625443228317669)
                    ·
                      refine ⟨3841175733304770605309563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20486270577625443228317669 3841175733304770605309563)
                      ·
                        rfl

theorem cell23_7480663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_7480663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480663 prefixEnd_7480663 := by exact prefixLift 7480663
  have htrace : WordTrace (prefixWord ++ tailWord_7480663) baseStart_7480663 baseEnd_7480663 := by
    simpa [prefixWord, tailWord_7480663, baseEnd_7480663] using wordTrace_append hprefix tailTrace_7480663
  have hstable : (prefixWord ++ tailWord_7480663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480663).length < 2 ^ (prefixWord ++ tailWord_7480663).sum := by decide
  have hdescent : baseEnd_7480663 < baseStart_7480663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480666 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_7480666 : Nat := 118140960795 + 7480666 * 2 ^ 59
def prefixEnd_7480666 : Nat := 4983230072969 + 3 ^ 40 * 7480666 * 2
def baseEnd_7480666 : Nat := 3841177273746734093572049

theorem tailTrace_7480666 : CollatzResearch.WordTrace tailWord_7480666 prefixEnd_7480666 3841177273746734093572049 := by
  unfold tailWord_7480666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68210575979208038220823463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181894869277888101922195901 68210575979208038220823463)
  ·
    refine ⟨102315863968812057331235195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68210575979208038220823463 102315863968812057331235195)
    ·
      refine ⟨153473795953218085996852793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102315863968812057331235195 153473795953218085996852793)
      ·
        refine ⟨115105346964913564497639595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153473795953218085996852793 115105346964913564497639595)
        ·
          refine ⟨172658020447370346746459393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115105346964913564497639595 172658020447370346746459393)
          ·
            refine ⟨129493515335527760059844545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172658020447370346746459393 129493515335527760059844545)
            ·
              refine ⟨97120136501645820044883409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129493515335527760059844545 97120136501645820044883409)
              ·
                refine ⟨72840102376234365033662557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97120136501645820044883409 72840102376234365033662557)
                ·
                  refine ⟨27315038391087886887623459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72840102376234365033662557 27315038391087886887623459)
                  ·
                    refine ⟨40972557586631830331435189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27315038391087886887623459 40972557586631830331435189)
                    ·
                      refine ⟨3841177273746734093572049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40972557586631830331435189 3841177273746734093572049)
                      ·
                        rfl

theorem cell23_7480666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_7480666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480666 prefixEnd_7480666 := by exact prefixLift 7480666
  have htrace : WordTrace (prefixWord ++ tailWord_7480666) baseStart_7480666 baseEnd_7480666 := by
    simpa [prefixWord, tailWord_7480666, baseEnd_7480666] using wordTrace_append hprefix tailTrace_7480666
  have hstable : (prefixWord ++ tailWord_7480666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480666).length < 2 ^ (prefixWord ++ tailWord_7480666).sum := by decide
  have hdescent : baseEnd_7480666 < baseStart_7480666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480690 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_7480690 : Nat := 118140960795 + 7480690 * 2 ^ 59
def prefixEnd_7480690 : Nat := 4983230072969 + 3 ^ 40 * 7480690 * 2
def baseEnd_7480690 : Nat := 1280396532427480666557313

theorem tailTrace_7480690 : CollatzResearch.WordTrace tailWord_7480690 prefixEnd_7480690 1280396532427480666557313 := by
  unfold tailWord_7480690
  simp only [CollatzResearch.WordTrace]
  refine ⟨68210794817186301245541881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181895452845830136654778349 68210794817186301245541881)
  ·
    refine ⟨51158096112889725934156411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68210794817186301245541881 51158096112889725934156411)
    ·
      refine ⟨76737144169334588901234617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51158096112889725934156411 76737144169334588901234617)
      ·
        refine ⟨57552858127000941675925963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76737144169334588901234617 57552858127000941675925963)
        ·
          refine ⟨86329287190501412513888945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57552858127000941675925963 86329287190501412513888945)
          ·
            refine ⟨64746965392876059385416709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86329287190501412513888945 64746965392876059385416709)
            ·
              refine ⟨12140056011164261134765633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64746965392876059385416709 12140056011164261134765633)
              ·
                refine ⟨9105042008373195851074225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12140056011164261134765633 9105042008373195851074225)
                ·
                  refine ⟨6828781506279896888305669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9105042008373195851074225 6828781506279896888305669)
                  ·
                    refine ⟨1280396532427480666557313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6828781506279896888305669 1280396532427480666557313)
                    ·
                      rfl

theorem cell23_7480690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_7480690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480690 prefixEnd_7480690 := by exact prefixLift 7480690
  have htrace : WordTrace (prefixWord ++ tailWord_7480690) baseStart_7480690 baseEnd_7480690 := by
    simpa [prefixWord, tailWord_7480690, baseEnd_7480690] using wordTrace_append hprefix tailTrace_7480690
  have hstable : (prefixWord ++ tailWord_7480690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480690).length < 2 ^ (prefixWord ++ tailWord_7480690).sum := by decide
  have hdescent : baseEnd_7480690 < baseStart_7480690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480716 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_7480716 : Nat := 118140960795 + 7480716 * 2 ^ 59
def prefixEnd_7480716 : Nat := 4983230072969 + 3 ^ 40 * 7480716 * 2
def baseEnd_7480716 : Nat := 1280400982593152965982273

theorem tailTrace_7480716 : CollatzResearch.WordTrace tailWord_7480716 prefixEnd_7480716 1280400982593152965982273 := by
  unfold tailWord_7480716
  simp only [CollatzResearch.WordTrace]
  refine ⟨136422063783325505711307001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181896085044434007615076001 136422063783325505711307001)
  ·
    refine ⟨102316547837494129283480251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136422063783325505711307001 102316547837494129283480251)
    ·
      refine ⟨153474821756241193925220377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102316547837494129283480251 153474821756241193925220377)
      ·
        refine ⟨115106116317180895443915283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153474821756241193925220377 115106116317180895443915283)
        ·
          refine ⟨172659174475771343165872925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115106116317180895443915283 172659174475771343165872925)
          ·
            refine ⟨64747190428414253687202347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172659174475771343165872925 64747190428414253687202347)
            ·
              refine ⟨97120785642621380530803521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64747190428414253687202347 97120785642621380530803521)
              ·
                refine ⟨72840589231966035398102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97120785642621380530803521 72840589231966035398102641)
                ·
                  refine ⟨54630441923974526548576981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72840589231966035398102641 54630441923974526548576981)
                  ·
                    refine ⟨1280400982593152965982273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54630441923974526548576981 1280400982593152965982273)
                    ·
                      rfl

theorem cell23_7480716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_7480716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480716 prefixEnd_7480716 := by exact prefixLift 7480716
  have htrace : WordTrace (prefixWord ++ tailWord_7480716) baseStart_7480716 baseEnd_7480716 := by
    simpa [prefixWord, tailWord_7480716, baseEnd_7480716] using wordTrace_append hprefix tailTrace_7480716
  have hstable : (prefixWord ++ tailWord_7480716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480716).length < 2 ^ (prefixWord ++ tailWord_7480716).sum := by decide
  have hdescent : baseEnd_7480716 < baseStart_7480716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480730 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7480730 : Nat := 118140960795 + 7480730 * 2 ^ 59
def prefixEnd_7480730 : Nat := 4983230072969 + 3 ^ 40 * 7480730 * 2
def baseEnd_7480730 : Nat := 3841210136508621843171755

theorem tailTrace_7480730 : CollatzResearch.WordTrace tailWord_7480730 prefixEnd_7480730 3841210136508621843171755 := by
  unfold tailWord_7480730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68211159547150072953405911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181896425459066861209082429 68211159547150072953405911)
  ·
    refine ⟨102316739320725109430108867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68211159547150072953405911 102316739320725109430108867)
    ·
      refine ⟨153475108981087664145163301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102316739320725109430108867 153475108981087664145163301)
      ·
        refine ⟨28776582933953937027218119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153475108981087664145163301 28776582933953937027218119)
        ·
          refine ⟨43164874400930905540827179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28776582933953937027218119 43164874400930905540827179)
          ·
            refine ⟨64747311601396358311240769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43164874400930905540827179 64747311601396358311240769)
            ·
              refine ⟨48560483701047268733430577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64747311601396358311240769 48560483701047268733430577)
              ·
                refine ⟨36420362775785451550072933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48560483701047268733430577 36420362775785451550072933)
                ·
                  refine ⟨6828818020459772165638675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36420362775785451550072933 6828818020459772165638675)
                  ·
                    refine ⟨10243227030689658248458013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6828818020459772165638675 10243227030689658248458013)
                    ·
                      refine ⟨3841210136508621843171755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243227030689658248458013 3841210136508621843171755)
                      ·
                        rfl

theorem cell23_7480730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7480730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480730 prefixEnd_7480730 := by exact prefixLift 7480730
  have htrace : WordTrace (prefixWord ++ tailWord_7480730) baseStart_7480730 baseEnd_7480730 := by
    simpa [prefixWord, tailWord_7480730, baseEnd_7480730] using wordTrace_append hprefix tailTrace_7480730
  have hstable : (prefixWord ++ tailWord_7480730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480730).length < 2 ^ (prefixWord ++ tailWord_7480730).sum := by decide
  have hdescent : baseEnd_7480730 < baseStart_7480730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480734 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7480734 : Nat := 118140960795 + 7480734 * 2 ^ 59
def prefixEnd_7480734 : Nat := 4983230072969 + 3 ^ 40 * 7480734 * 2
def baseEnd_7480734 : Nat := 3841212190431239827521737

theorem tailTrace_7480734 : CollatzResearch.WordTrace tailWord_7480734 prefixEnd_7480734 3841212190431239827521737 := by
  unfold tailWord_7480734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34105598010073225062096157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181896522720390533664512837 34105598010073225062096157)
  ·
    refine ⟨12789599253777459398286059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34105598010073225062096157 12789599253777459398286059)
    ·
      refine ⟨19184398880666189097429089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12789599253777459398286059 19184398880666189097429089)
      ·
        refine ⟨14388299160499641823071817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19184398880666189097429089 14388299160499641823071817)
        ·
          refine ⟨10791224370374731367303863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14388299160499641823071817 10791224370374731367303863)
          ·
            refine ⟨16186836555562097050955795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10791224370374731367303863 16186836555562097050955795)
            ·
              refine ⟨24280254833343145576433693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16186836555562097050955795 24280254833343145576433693)
              ·
                refine ⟨9105095562503679591162635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24280254833343145576433693 9105095562503679591162635)
                ·
                  refine ⟨13657643343755519386743953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9105095562503679591162635 13657643343755519386743953)
                  ·
                    refine ⟨10243232507816639540057965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13657643343755519386743953 10243232507816639540057965)
                    ·
                      refine ⟨3841212190431239827521737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243232507816639540057965 3841212190431239827521737)
                      ·
                        rfl

theorem cell23_7480734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7480734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480734 prefixEnd_7480734 := by exact prefixLift 7480734
  have htrace : WordTrace (prefixWord ++ tailWord_7480734) baseStart_7480734 baseEnd_7480734 := by
    simpa [prefixWord, tailWord_7480734, baseEnd_7480734] using wordTrace_append hprefix tailTrace_7480734
  have hstable : (prefixWord ++ tailWord_7480734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480734).length < 2 ^ (prefixWord ++ tailWord_7480734).sum := by decide
  have hdescent : baseEnd_7480734 < baseStart_7480734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480764 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7480764 : Nat := 118140960795 + 7480764 * 2 ^ 59
def prefixEnd_7480764 : Nat := 4983230072969 + 3 ^ 40 * 7480764 * 2
def baseEnd_7480764 : Nat := 3841227594850874710146599

theorem tailTrace_7480764 : CollatzResearch.WordTrace tailWord_7480764 prefixEnd_7480764 3841227594850874710146599 := by
  unfold tailWord_7480764
  simp only [CollatzResearch.WordTrace]
  refine ⟨136422939135238557810180673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181897252180318077080240897 136422939135238557810180673)
  ·
    refine ⟨102317204351428918357635505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136422939135238557810180673 102317204351428918357635505)
    ·
      refine ⟨76737903263571688768226629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102317204351428918357635505 76737903263571688768226629)
      ·
        refine ⟨14388356861919691644042493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76737903263571688768226629 14388356861919691644042493)
        ·
          refine ⟨5395633823219884366515935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14388356861919691644042493 5395633823219884366515935)
          ·
            refine ⟨8093450734829826549773903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395633823219884366515935 8093450734829826549773903)
            ·
              refine ⟨12140176102244739824660855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093450734829826549773903 12140176102244739824660855)
              ·
                refine ⟨18210264153367109736991283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12140176102244739824660855 18210264153367109736991283)
                ·
                  refine ⟨27315396230050664605486925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18210264153367109736991283 27315396230050664605486925)
                  ·
                    refine ⟨10243273586268999227057597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27315396230050664605486925 10243273586268999227057597)
                    ·
                      refine ⟨3841227594850874710146599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243273586268999227057597 3841227594850874710146599)
                      ·
                        rfl

theorem cell23_7480764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7480764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480764 prefixEnd_7480764 := by exact prefixLift 7480764
  have htrace : WordTrace (prefixWord ++ tailWord_7480764) baseStart_7480764 baseEnd_7480764 := by
    simpa [prefixWord, tailWord_7480764, baseEnd_7480764] using wordTrace_append hprefix tailTrace_7480764
  have hstable : (prefixWord ++ tailWord_7480764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480764).length < 2 ^ (prefixWord ++ tailWord_7480764).sum := by decide
  have hdescent : baseEnd_7480764 < baseStart_7480764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480790 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7480790 : Nat := 118140960795 + 7480790 * 2 ^ 59
def prefixEnd_7480790 : Nat := 4983230072969 + 3 ^ 40 * 7480790 * 2
def baseEnd_7480790 : Nat := 3841240945347891608421479

theorem tailTrace_7480790 : CollatzResearch.WordTrace tailWord_7480790 prefixEnd_7480790 3841240945347891608421479 := by
  unfold tailWord_7480790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052926660523932628800489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181897884378921948040538549 17052926660523932628800489)
  ·
    refine ⟨12789694995392949471600367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17052926660523932628800489 12789694995392949471600367)
    ·
      refine ⟨19184542493089424207400551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12789694995392949471600367 19184542493089424207400551)
      ·
        refine ⟨28776813739634136311100827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19184542493089424207400551 28776813739634136311100827)
        ·
          refine ⟨43165220609451204466651241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28776813739634136311100827 43165220609451204466651241)
          ·
            refine ⟨32373915457088403349988431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43165220609451204466651241 32373915457088403349988431)
            ·
              refine ⟨48560873185632605024982647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32373915457088403349988431 48560873185632605024982647)
              ·
                refine ⟨72841309778448907537473971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48560873185632605024982647 72841309778448907537473971)
                ·
                  refine ⟨109261964667673361306210957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72841309778448907537473971 109261964667673361306210957)
                  ·
                    refine ⟨40973236750377510489829109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109261964667673361306210957 40973236750377510489829109)
                    ·
                      refine ⟨3841240945347891608421479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40973236750377510489829109 3841240945347891608421479)
                      ·
                        rfl

theorem cell23_7480790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7480790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480790 prefixEnd_7480790 := by exact prefixLift 7480790
  have htrace : WordTrace (prefixWord ++ tailWord_7480790) baseStart_7480790 baseEnd_7480790 := by
    simpa [prefixWord, tailWord_7480790, baseEnd_7480790] using wordTrace_append hprefix tailTrace_7480790
  have hstable : (prefixWord ++ tailWord_7480790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480790).length < 2 ^ (prefixWord ++ tailWord_7480790).sum := by decide
  have hdescent : baseEnd_7480790 < baseStart_7480790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480821 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7480821 : Nat := 118140960795 + 7480821 * 2 ^ 59
def prefixEnd_7480821 : Nat := 4983230072969 + 3 ^ 40 * 7480821 * 2
def baseEnd_7480821 : Nat := 3841256863248180987133837

theorem tailTrace_7480821 : CollatzResearch.WordTrace tailWord_7480821 prefixEnd_7480821 3841256863248180987133837 := by
  unfold tailWord_7480821
  simp only [CollatzResearch.WordTrace]
  refine ⟨272847957231270614355186317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181898638154180409570124211 272847957231270614355186317)
  ·
    refine ⟨102317983961726480383194869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272847957231270614355186317 102317983961726480383194869)
    ·
      refine ⟨9592310996411857535924519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102317983961726480383194869 9592310996411857535924519)
      ·
        refine ⟨14388466494617786303886779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9592310996411857535924519 14388466494617786303886779)
        ·
          refine ⟨21582699741926679455830169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14388466494617786303886779 21582699741926679455830169)
          ·
            refine ⟨16187024806445009591872627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21582699741926679455830169 16187024806445009591872627)
            ·
              refine ⟨24280537209667514387808941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16187024806445009591872627 24280537209667514387808941)
              ·
                refine ⟨9105201453625317895428353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24280537209667514387808941 9105201453625317895428353)
                ·
                  refine ⟨6828901090218988421571265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9105201453625317895428353 6828901090218988421571265)
                  ·
                    refine ⟨5121675817664241316178449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6828901090218988421571265 5121675817664241316178449)
                    ·
                      refine ⟨3841256863248180987133837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121675817664241316178449 3841256863248180987133837)
                      ·
                        rfl

theorem cell23_7480821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7480821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480821 prefixEnd_7480821 := by exact prefixLift 7480821
  have htrace : WordTrace (prefixWord ++ tailWord_7480821) baseStart_7480821 baseEnd_7480821 := by
    simpa [prefixWord, tailWord_7480821, baseEnd_7480821] using wordTrace_append hprefix tailTrace_7480821
  have hstable : (prefixWord ++ tailWord_7480821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480821).length < 2 ^ (prefixWord ++ tailWord_7480821).sum := by decide
  have hdescent : baseEnd_7480821 < baseStart_7480821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480838 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7480838 : Nat := 118140960795 + 7480838 * 2 ^ 59
def prefixEnd_7480838 : Nat := 4983230072969 + 3 ^ 40 * 7480838 * 2
def baseEnd_7480838 : Nat := 3841265592419307420621259

theorem tailTrace_7480838 : CollatzResearch.WordTrace tailWord_7480838 prefixEnd_7480838 3841265592419307420621259 := by
  unfold tailWord_7480838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526518039756532070579849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181899051514806017505703445 8526518039756532070579849)
  ·
    refine ⟨6394888529817399052934887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8526518039756532070579849 6394888529817399052934887)
    ·
      refine ⟨9592332794726098579402331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6394888529817399052934887 9592332794726098579402331)
      ·
        refine ⟨14388499192089147869103497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9592332794726098579402331 14388499192089147869103497)
        ·
          refine ⟨10791374394066860901827623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14388499192089147869103497 10791374394066860901827623)
          ·
            refine ⟨16187061591100291352741435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10791374394066860901827623 16187061591100291352741435)
            ·
              refine ⟨24280592386650437029112153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16187061591100291352741435 24280592386650437029112153)
              ·
                refine ⟨18210444289987827771834115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24280592386650437029112153 18210444289987827771834115)
                ·
                  refine ⟨27315666434981741657751173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18210444289987827771834115 27315666434981741657751173)
                  ·
                    refine ⟨5121687456559076560828345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27315666434981741657751173 5121687456559076560828345)
                    ·
                      refine ⟨3841265592419307420621259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121687456559076560828345 3841265592419307420621259)
                      ·
                        rfl

theorem cell23_7480838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7480838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480838 prefixEnd_7480838 := by exact prefixLift 7480838
  have htrace : WordTrace (prefixWord ++ tailWord_7480838) baseStart_7480838 baseEnd_7480838 := by
    simpa [prefixWord, tailWord_7480838, baseEnd_7480838] using wordTrace_append hprefix tailTrace_7480838
  have hstable : (prefixWord ++ tailWord_7480838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480838).length < 2 ^ (prefixWord ++ tailWord_7480838).sum := by decide
  have hdescent : baseEnd_7480838 < baseStart_7480838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480860 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7480860 : Nat := 118140960795 + 7480860 * 2 ^ 59
def prefixEnd_7480860 : Nat := 4983230072969 + 3 ^ 40 * 7480860 * 2
def baseEnd_7480860 : Nat := 3841276888993706334546157

theorem tailTrace_7480860 : CollatzResearch.WordTrace tailWord_7480860 prefixEnd_7480860 3841276888993706334546157 := by
  unfold tailWord_7480860
  simp only [CollatzResearch.WordTrace]
  refine ⟨136424689839064662007928017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181899586452086216010570689 136424689839064662007928017)
  ·
    refine ⟨102318517379298496505946013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136424689839064662007928017 102318517379298496505946013)
    ·
      refine ⟨38369444017236936189729755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102318517379298496505946013 38369444017236936189729755)
      ·
        refine ⟨57554166025855404284594633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38369444017236936189729755 57554166025855404284594633)
        ·
          refine ⟨43165624519391553213445975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57554166025855404284594633 43165624519391553213445975)
          ·
            refine ⟨64748436779087329820168963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43165624519391553213445975 64748436779087329820168963)
            ·
              refine ⟨97122655168630994730253445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64748436779087329820168963 97122655168630994730253445)
              ·
                refine ⟨18210497844118311511922521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97122655168630994730253445 18210497844118311511922521)
                ·
                  refine ⟨13657873383088733633941891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18210497844118311511922521 13657873383088733633941891)
                  ·
                    refine ⟨20486810074633100450912837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13657873383088733633941891 20486810074633100450912837)
                    ·
                      refine ⟨3841276888993706334546157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20486810074633100450912837 3841276888993706334546157)
                      ·
                        rfl

theorem cell23_7480860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7480860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480860 prefixEnd_7480860 := by exact prefixLift 7480860
  have htrace : WordTrace (prefixWord ++ tailWord_7480860) baseStart_7480860 baseEnd_7480860 := by
    simpa [prefixWord, tailWord_7480860, baseEnd_7480860] using wordTrace_append hprefix tailTrace_7480860
  have hstable : (prefixWord ++ tailWord_7480860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480860).length < 2 ^ (prefixWord ++ tailWord_7480860).sum := by decide
  have hdescent : baseEnd_7480860 < baseStart_7480860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480960 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_7480960 : Nat := 118140960795 + 7480960 * 2 ^ 59
def prefixEnd_7480960 : Nat := 4983230072969 + 3 ^ 40 * 7480960 * 2
def baseEnd_7480960 : Nat := 1280442745686385314431899

theorem tailTrace_7480960 : CollatzResearch.WordTrace tailWord_7480960 prefixEnd_7480960 1280442745686385314431899 := by
  unfold tailWord_7480960
  simp only [CollatzResearch.WordTrace]
  refine ⟨136426513488883520547248167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181902017985178027396330889 136426513488883520547248167)
  ·
    refine ⟨204639770233325280820872251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136426513488883520547248167 204639770233325280820872251)
    ·
      refine ⟨306959655349987921231308377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204639770233325280820872251 306959655349987921231308377)
      ·
        refine ⟨230219741512490940923481283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306959655349987921231308377 230219741512490940923481283)
        ·
          refine ⟨345329612268736411385221925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230219741512490940923481283 345329612268736411385221925)
          ·
            refine ⟨64749302300388077134729111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345329612268736411385221925 64749302300388077134729111)
            ·
              refine ⟨97123953450582115702093667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64749302300388077134729111 97123953450582115702093667)
              ·
                refine ⟨145685930175873173553140501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97123953450582115702093667 145685930175873173553140501)
                ·
                  refine ⟨6829027976994055010303461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145685930175873173553140501 6829027976994055010303461)
                  ·
                    refine ⟨1280442745686385314431899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829027976994055010303461 1280442745686385314431899)
                    ·
                      rfl

theorem cell23_7480960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_7480960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480960 prefixEnd_7480960 := by exact prefixLift 7480960
  have htrace : WordTrace (prefixWord ++ tailWord_7480960) baseStart_7480960 baseEnd_7480960 := by
    simpa [prefixWord, tailWord_7480960, baseEnd_7480960] using wordTrace_append hprefix tailTrace_7480960
  have hstable : (prefixWord ++ tailWord_7480960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480960).length < 2 ^ (prefixWord ++ tailWord_7480960).sum := by decide
  have hdescent : baseEnd_7480960 < baseStart_7480960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480961 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_7480961 : Nat := 118140960795 + 7480961 * 2 ^ 59
def prefixEnd_7480961 : Nat := 4983230072969 + 3 ^ 40 * 7480961 * 2
def baseEnd_7480961 : Nat := 3841328750539810439383193

theorem tailTrace_7480961 : CollatzResearch.WordTrace tailWord_7480961 prefixEnd_7480961 3841328750539810439383193 := by
  unfold tailWord_7480961
  simp only [CollatzResearch.WordTrace]
  refine ⟨272853063450763418265282737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181902042300508945510188491 272853063450763418265282737)
  ·
    refine ⟨204639797588072563698962053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272853063450763418265282737 204639797588072563698962053)
    ·
      refine ⟨38369962047763605693555385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204639797588072563698962053 38369962047763605693555385)
      ·
        refine ⟨28777471535822704270166539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38369962047763605693555385 28777471535822704270166539)
        ·
          refine ⟨43166207303734056405249809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28777471535822704270166539 43166207303734056405249809)
          ·
            refine ⟨32374655477800542303937357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43166207303734056405249809 32374655477800542303937357)
            ·
              refine ⟨12140495804175203363976509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32374655477800542303937357 12140495804175203363976509)
              ·
                refine ⟨4552685926565701261491191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12140495804175203363976509 4552685926565701261491191)
                ·
                  refine ⟨6829028889848551892236787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552685926565701261491191 6829028889848551892236787)
                  ·
                    refine ⟨10243543334772827838355181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829028889848551892236787 10243543334772827838355181)
                    ·
                      refine ⟨3841328750539810439383193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243543334772827838355181 3841328750539810439383193)
                      ·
                        rfl

theorem cell23_7480961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_7480961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480961 prefixEnd_7480961 := by exact prefixLift 7480961
  have htrace : WordTrace (prefixWord ++ tailWord_7480961) baseStart_7480961 baseEnd_7480961 := by
    simpa [prefixWord, tailWord_7480961, baseEnd_7480961] using wordTrace_append hprefix tailTrace_7480961
  have hstable : (prefixWord ++ tailWord_7480961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480961).length < 2 ^ (prefixWord ++ tailWord_7480961).sum := by decide
  have hdescent : baseEnd_7480961 < baseStart_7480961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480967 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_7480967 : Nat := 118140960795 + 7480967 * 2 ^ 59
def prefixEnd_7480967 : Nat := 4983230072969 + 3 ^ 40 * 7480967 * 2
def baseEnd_7480967 : Nat := 3841331831423737415908165

theorem tailTrace_7480967 : CollatzResearch.WordTrace tailWord_7480967 prefixEnd_7480967 3841331831423737415908165 := by
  unfold tailWord_7480967
  simp only [CollatzResearch.WordTrace]
  refine ⟨272853282288741681290001155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181902188192494454193334103 272853282288741681290001155)
  ·
    refine ⟨409279923433112521935001733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272853282288741681290001155 409279923433112521935001733)
    ·
      refine ⟨76739985643708597862812825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 409279923433112521935001733 76739985643708597862812825)
      ·
        refine ⟨57554989232781448397109619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76739985643708597862812825 57554989232781448397109619)
        ·
          refine ⟨86332483849172172595664429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57554989232781448397109619 86332483849172172595664429)
          ·
            refine ⟨32374681443439564723374161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86332483849172172595664429 32374681443439564723374161)
            ·
              refine ⟨24281011082579673542530621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32374681443439564723374161 24281011082579673542530621)
              ·
                refine ⟨9105379155967377578448983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24281011082579673542530621 9105379155967377578448983)
                ·
                  refine ⟨13658068733951066367673475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9105379155967377578448983 13658068733951066367673475)
                  ·
                    refine ⟨20487103100926599551510213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13658068733951066367673475 20487103100926599551510213)
                    ·
                      refine ⟨3841331831423737415908165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20487103100926599551510213 3841331831423737415908165)
                      ·
                        rfl

theorem cell23_7480967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_7480967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480967 prefixEnd_7480967 := by exact prefixLift 7480967
  have htrace : WordTrace (prefixWord ++ tailWord_7480967) baseStart_7480967 baseEnd_7480967 := by
    simpa [prefixWord, tailWord_7480967, baseEnd_7480967] using wordTrace_append hprefix tailTrace_7480967
  have hstable : (prefixWord ++ tailWord_7480967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480967).length < 2 ^ (prefixWord ++ tailWord_7480967).sum := by decide
  have hdescent : baseEnd_7480967 < baseStart_7480967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7480978 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_7480978 : Nat := 118140960795 + 7480978 * 2 ^ 59
def prefixEnd_7480978 : Nat := 4983230072969 + 3 ^ 40 * 7480978 * 2
def baseEnd_7480978 : Nat := 3841337479710936872870615

theorem tailTrace_7480978 : CollatzResearch.WordTrace tailWord_7480978 prefixEnd_7480978 3841337479710936872870615 := by
  unfold tailWord_7480978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68213420872925457542162897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181902455661134553445767725 68213420872925457542162897)
  ·
    refine ⟨51160065654694093156622173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68213420872925457542162897 51160065654694093156622173)
    ·
      refine ⟨19185024620510284933733315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51160065654694093156622173 19185024620510284933733315)
      ·
        refine ⟨28777536930765427400599973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19185024620510284933733315 28777536930765427400599973)
        ·
          refine ⟨5395788174518517637612495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28777536930765427400599973 5395788174518517637612495)
          ·
            refine ⟨8093682261777776456418743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395788174518517637612495 8093682261777776456418743)
            ·
              refine ⟨12140523392666664684628115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093682261777776456418743 12140523392666664684628115)
              ·
                refine ⟨18210785088999997026942173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12140523392666664684628115 18210785088999997026942173)
                ·
                  refine ⟨6829044408374998885103315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18210785088999997026942173 6829044408374998885103315)
                  ·
                    refine ⟨10243566612562498327654973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829044408374998885103315 10243566612562498327654973)
                    ·
                      refine ⟨3841337479710936872870615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243566612562498327654973 3841337479710936872870615)
                      ·
                        rfl

theorem cell23_7480978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_7480978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7480978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7480978 prefixEnd_7480978 := by exact prefixLift 7480978
  have htrace : WordTrace (prefixWord ++ tailWord_7480978) baseStart_7480978 baseEnd_7480978 := by
    simpa [prefixWord, tailWord_7480978, baseEnd_7480978] using wordTrace_append hprefix tailTrace_7480978
  have hstable : (prefixWord ++ tailWord_7480978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7480978).length < 2 ^ (prefixWord ++ tailWord_7480978).sum := by decide
  have hdescent : baseEnd_7480978 < baseStart_7480978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7480978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481014 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7481014 : Nat := 118140960795 + 7481014 * 2 ^ 59
def prefixEnd_7481014 : Nat := 4983230072969 + 3 ^ 40 * 7481014 * 2
def baseEnd_7481014 : Nat := 3841355965014498732020449

theorem tailTrace_7481014 : CollatzResearch.WordTrace tailWord_7481014 prefixEnd_7481014 3841355965014498732020449 := by
  unfold tailWord_7481014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053437282473213019810131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181903331013047605544641397 17053437282473213019810131)
  ·
    refine ⟨25580155923709819529715197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17053437282473213019810131 25580155923709819529715197)
    ·
      refine ⟨9592558471391182323643199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25580155923709819529715197 9592558471391182323643199)
      ·
        refine ⟨14388837707086773485464799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9592558471391182323643199 14388837707086773485464799)
        ·
          refine ⟨21583256560630160228197199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14388837707086773485464799 21583256560630160228197199)
          ·
            refine ⟨32374884840945240342295799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21583256560630160228197199 32374884840945240342295799)
            ·
              refine ⟨48562327261417860513443699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32374884840945240342295799 48562327261417860513443699)
              ·
                refine ⟨72843490892126790770165549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48562327261417860513443699 72843490892126790770165549)
                ·
                  refine ⟨27316309084547546538812081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72843490892126790770165549 27316309084547546538812081)
                  ·
                    refine ⟨20487231813410659904109061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27316309084547546538812081 20487231813410659904109061)
                    ·
                      refine ⟨3841355965014498732020449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20487231813410659904109061 3841355965014498732020449)
                      ·
                        rfl

theorem cell23_7481014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7481014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481014 prefixEnd_7481014 := by exact prefixLift 7481014
  have htrace : WordTrace (prefixWord ++ tailWord_7481014) baseStart_7481014 baseEnd_7481014 := by
    simpa [prefixWord, tailWord_7481014, baseEnd_7481014] using wordTrace_append hprefix tailTrace_7481014
  have hstable : (prefixWord ++ tailWord_7481014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481014).length < 2 ^ (prefixWord ++ tailWord_7481014).sum := by decide
  have hdescent : baseEnd_7481014 < baseStart_7481014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481017 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7481017 : Nat := 118140960795 + 7481017 * 2 ^ 59
def prefixEnd_7481017 : Nat := 4983230072969 + 3 ^ 40 * 7481017 * 2
def baseEnd_7481017 : Nat := 3841357505456462220282935

theorem tailTrace_7481017 : CollatzResearch.WordTrace tailWord_7481017 prefixEnd_7481017 3841357505456462220282935 := by
  unfold tailWord_7481017
  simp only [CollatzResearch.WordTrace]
  refine ⟨272855105938560539829321305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181903403959040359886214203 272855105938560539829321305)
  ·
    refine ⟨204641329453920404871990979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272855105938560539829321305 204641329453920404871990979)
    ·
      refine ⟨306961994180880607307986469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204641329453920404871990979 306961994180880607307986469)
      ·
        refine ⟨57555373908915113870247463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306961994180880607307986469 57555373908915113870247463)
        ·
          refine ⟨86333060863372670805371195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57555373908915113870247463 86333060863372670805371195)
          ·
            refine ⟨129499591295059006208056793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86333060863372670805371195 129499591295059006208056793)
            ·
              refine ⟨97124693471294254656042595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129499591295059006208056793 97124693471294254656042595)
              ·
                refine ⟨145687040206941381984063893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97124693471294254656042595 145687040206941381984063893)
                ·
                  refine ⟨6829080009700377280502995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145687040206941381984063893 6829080009700377280502995)
                  ·
                    refine ⟨10243620014550565920754493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829080009700377280502995 10243620014550565920754493)
                    ·
                      refine ⟨3841357505456462220282935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243620014550565920754493 3841357505456462220282935)
                      ·
                        rfl

theorem cell23_7481017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7481017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481017 prefixEnd_7481017 := by exact prefixLift 7481017
  have htrace : WordTrace (prefixWord ++ tailWord_7481017) baseStart_7481017 baseEnd_7481017 := by
    simpa [prefixWord, tailWord_7481017, baseEnd_7481017] using wordTrace_append hprefix tailTrace_7481017
  have hstable : (prefixWord ++ tailWord_7481017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481017).length < 2 ^ (prefixWord ++ tailWord_7481017).sum := by decide
  have hdescent : baseEnd_7481017 < baseStart_7481017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481050 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_7481050 : Nat := 118140960795 + 7481050 * 2 ^ 59
def prefixEnd_7481050 : Nat := 4983230072969 + 3 ^ 40 * 7481050 * 2
def baseEnd_7481050 : Nat := 1280458150106020197056761

theorem tailTrace_7481050 : CollatzResearch.WordTrace tailWord_7481050 prefixEnd_7481050 1280458150106020197056761 := by
  unfold tailWord_7481050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68214077386860246616318151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181904206364960657643515069 68214077386860246616318151)
  ·
    refine ⟨102321116080290369924477227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68214077386860246616318151 102321116080290369924477227)
    ·
      refine ⟨153481674120435554886715841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102321116080290369924477227 153481674120435554886715841)
      ·
        refine ⟨115111255590326666165036881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153481674120435554886715841 115111255590326666165036881)
        ·
          refine ⟨86333441692744999623777661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115111255590326666165036881 86333441692744999623777661)
          ·
            refine ⟨32375040634779374858916623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86333441692744999623777661 32375040634779374858916623)
            ·
              refine ⟨48562560952169062288374935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32375040634779374858916623 48562560952169062288374935)
              ·
                refine ⟨72843841428253593432562403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48562560952169062288374935 72843841428253593432562403)
                ·
                  refine ⟨109265762142380390148843605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72843841428253593432562403 109265762142380390148843605)
                  ·
                    refine ⟨1280458150106020197056761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109265762142380390148843605 1280458150106020197056761)
                    ·
                      rfl

theorem cell23_7481050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_7481050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481050 prefixEnd_7481050 := by exact prefixLift 7481050
  have htrace : WordTrace (prefixWord ++ tailWord_7481050) baseStart_7481050 baseEnd_7481050 := by
    simpa [prefixWord, tailWord_7481050, baseEnd_7481050] using wordTrace_append hprefix tailTrace_7481050
  have hstable : (prefixWord ++ tailWord_7481050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481050).length < 2 ^ (prefixWord ++ tailWord_7481050).sum := by decide
  have hdescent : baseEnd_7481050 < baseStart_7481050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481074 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_7481074 : Nat := 118140960795 + 7481074 * 2 ^ 59
def prefixEnd_7481074 : Nat := 4983230072969 + 3 ^ 40 * 7481074 * 2
def baseEnd_7481074 : Nat := 3841386773853768497270173

theorem tailTrace_7481074 : CollatzResearch.WordTrace tailWord_7481074 prefixEnd_7481074 3841386773853768497270173 := by
  unfold tailWord_7481074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68214296224838509641036569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181904789932902692376097517 68214296224838509641036569)
  ·
    refine ⟨51160722168628882230777427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68214296224838509641036569 51160722168628882230777427)
    ·
      refine ⟨76741083252943323346166141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51160722168628882230777427 76741083252943323346166141)
      ·
        refine ⟨28777906219853746254812303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76741083252943323346166141 28777906219853746254812303)
        ·
          refine ⟨43166859329780619382218455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28777906219853746254812303 43166859329780619382218455)
          ·
            refine ⟨64750288994670929073327683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43166859329780619382218455 64750288994670929073327683)
            ·
              refine ⟨97125433492006393609991525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64750288994670929073327683 97125433492006393609991525)
              ·
                refine ⟨18211018779751198801873411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97125433492006393609991525 18211018779751198801873411)
                ·
                  refine ⟨27316528169626798202810117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18211018779751198801873411 27316528169626798202810117)
                  ·
                    refine ⟨5121849031805024663026897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27316528169626798202810117 5121849031805024663026897)
                    ·
                      refine ⟨3841386773853768497270173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121849031805024663026897 3841386773853768497270173)
                      ·
                        rfl

theorem cell23_7481074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_7481074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481074 prefixEnd_7481074 := by exact prefixLift 7481074
  have htrace : WordTrace (prefixWord ++ tailWord_7481074) baseStart_7481074 baseEnd_7481074 := by
    simpa [prefixWord, tailWord_7481074, baseEnd_7481074] using wordTrace_append hprefix tailTrace_7481074
  have hstable : (prefixWord ++ tailWord_7481074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481074).length < 2 ^ (prefixWord ++ tailWord_7481074).sum := by decide
  have hdescent : baseEnd_7481074 < baseStart_7481074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481078 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7481078 : Nat := 118140960795 + 7481078 * 2 ^ 59
def prefixEnd_7481078 : Nat := 4983230072969 + 3 ^ 40 * 7481078 * 2
def baseEnd_7481078 : Nat := 3841388827776386481620155

theorem tailTrace_7481078 : CollatzResearch.WordTrace tailWord_7481078 prefixEnd_7481078 3841388827776386481620155 := by
  unfold tailWord_7481078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053583174458721702955743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181904887194226364831527925 17053583174458721702955743)
  ·
    refine ⟨25580374761688082554433615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17053583174458721702955743 25580374761688082554433615)
    ·
      refine ⟨38370562142532123831650423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25580374761688082554433615 38370562142532123831650423)
      ·
        refine ⟨57555843213798185747475635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38370562142532123831650423 57555843213798185747475635)
        ·
          refine ⟨86333764820697278621213453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57555843213798185747475635 86333764820697278621213453)
          ·
            refine ⟨32375161807761479482955045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86333764820697278621213453 32375161807761479482955045)
            ·
              refine ⟨6070342838955277403054071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32375161807761479482955045 6070342838955277403054071)
              ·
                refine ⟨9105514258432916104581107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070342838955277403054071 9105514258432916104581107)
                ·
                  refine ⟨13658271387649374156871661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9105514258432916104581107 13658271387649374156871661)
                  ·
                    refine ⟨5121851770368515308826873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13658271387649374156871661 5121851770368515308826873)
                    ·
                      refine ⟨3841388827776386481620155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121851770368515308826873 3841388827776386481620155)
                      ·
                        rfl

theorem cell23_7481078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7481078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481078 prefixEnd_7481078 := by exact prefixLift 7481078
  have htrace : WordTrace (prefixWord ++ tailWord_7481078) baseStart_7481078 baseEnd_7481078 := by
    simpa [prefixWord, tailWord_7481078, baseEnd_7481078] using wordTrace_append hprefix tailTrace_7481078
  have hstable : (prefixWord ++ tailWord_7481078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481078).length < 2 ^ (prefixWord ++ tailWord_7481078).sum := by decide
  have hdescent : baseEnd_7481078 < baseStart_7481078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481091 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 2, 2, 2]
def baseStart_7481091 : Nat := 118140960795 + 7481091 * 2 ^ 59
def prefixEnd_7481091 : Nat := 4983230072969 + 3 ^ 40 * 7481091 * 2
def baseEnd_7481091 : Nat := 3841395503024894930757595

theorem tailTrace_7481091 : CollatzResearch.WordTrace tailWord_7481091 prefixEnd_7481091 3841395503024894930757595 := by
  unfold tailWord_7481091
  simp only [CollatzResearch.WordTrace]
  refine ⟨272857804940292450467515127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181905203293528300311676751 272857804940292450467515127)
  ·
    refine ⟨409286707410438675701272691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272857804940292450467515127 409286707410438675701272691)
    ·
      refine ⟨613930061115658013551909037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409286707410438675701272691 613930061115658013551909037)
      ·
        refine ⟨230223772918371755081965889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613930061115658013551909037 230223772918371755081965889)
        ·
          refine ⟨172667829688778816311474417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230223772918371755081965889 172667829688778816311474417)
          ·
            refine ⟨129500872266584112233605813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172667829688778816311474417 129500872266584112233605813)
            ·
              refine ⟨12140706774992260521900545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129500872266584112233605813 12140706774992260521900545)
              ·
                refine ⟨9105530081244195391425409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12140706774992260521900545 9105530081244195391425409)
                ·
                  refine ⟨6829147560933146543569057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9105530081244195391425409 6829147560933146543569057)
                  ·
                    refine ⟨5121860670699859907676793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6829147560933146543569057 5121860670699859907676793)
                    ·
                      refine ⟨3841395503024894930757595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121860670699859907676793 3841395503024894930757595)
                      ·
                        rfl

theorem cell23_7481091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_7481091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481091 prefixEnd_7481091 := by exact prefixLift 7481091
  have htrace : WordTrace (prefixWord ++ tailWord_7481091) baseStart_7481091 baseEnd_7481091 := by
    simpa [prefixWord, tailWord_7481091, baseEnd_7481091] using wordTrace_append hprefix tailTrace_7481091
  have hstable : (prefixWord ++ tailWord_7481091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481091).length < 2 ^ (prefixWord ++ tailWord_7481091).sum := by decide
  have hdescent : baseEnd_7481091 < baseStart_7481091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481184 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_7481184 : Nat := 118140960795 + 7481184 * 2 ^ 59
def prefixEnd_7481184 : Nat := 4983230072969 + 3 ^ 40 * 7481184 * 2
def baseEnd_7481184 : Nat := 3841443256725763066894667

theorem tailTrace_7481184 : CollatzResearch.WordTrace tailWord_7481184 prefixEnd_7481184 3841443256725763066894667 := by
  unfold tailWord_7481184
  simp only [CollatzResearch.WordTrace]
  refine ⟨136430598464477763675325303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181907464619303684900433737 136430598464477763675325303)
  ·
    refine ⟨204645897696716645512987955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136430598464477763675325303 204645897696716645512987955)
    ·
      refine ⟨306968846545074968269481933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204645897696716645512987955 306968846545074968269481933)
      ·
        refine ⟨115113317454403113101055725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306968846545074968269481933 115113317454403113101055725)
        ·
          refine ⟨43167494045401167412895897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115113317454403113101055725 43167494045401167412895897)
          ·
            refine ⟨32375620534050875559671923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43167494045401167412895897 32375620534050875559671923)
            ·
              refine ⟨48563430801076313339507885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32375620534050875559671923 48563430801076313339507885)
              ·
                refine ⟨18211286550403617502315457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48563430801076313339507885 18211286550403617502315457)
                ·
                  refine ⟨13658464912802713126736593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18211286550403617502315457 13658464912802713126736593)
                  ·
                    refine ⟨10243848684602034845052445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13658464912802713126736593 10243848684602034845052445)
                    ·
                      refine ⟨3841443256725763066894667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243848684602034845052445 3841443256725763066894667)
                      ·
                        rfl

theorem cell23_7481184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_7481184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481184 prefixEnd_7481184 := by exact prefixLift 7481184
  have htrace : WordTrace (prefixWord ++ tailWord_7481184) baseStart_7481184 baseEnd_7481184 := by
    simpa [prefixWord, tailWord_7481184, baseEnd_7481184] using wordTrace_append hprefix tailTrace_7481184
  have hstable : (prefixWord ++ tailWord_7481184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481184).length < 2 ^ (prefixWord ++ tailWord_7481184).sum := by decide
  have hdescent : baseEnd_7481184 < baseStart_7481184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481191 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 1, 4]
def baseStart_7481191 : Nat := 118140960795 + 7481191 * 2 ^ 59
def prefixEnd_7481191 : Nat := 4983230072969 + 3 ^ 40 * 7481191 * 2
def baseEnd_7481191 : Nat := 1280482283696781513169045

theorem tailTrace_7481191 : CollatzResearch.WordTrace tailWord_7481191 prefixEnd_7481191 1280482283696781513169045 := by
  unfold tailWord_7481191
  simp only [CollatzResearch.WordTrace]
  refine ⟨272861452239930167546155427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181907634826620111697436951 272861452239930167546155427)
  ·
    refine ⟨409292178359895251319233141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272861452239930167546155427 409292178359895251319233141)
    ·
      refine ⟨38371141721240179811178107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409292178359895251319233141 38371141721240179811178107)
      ·
        refine ⟨57556712581860269716767161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38371141721240179811178107 57556712581860269716767161)
        ·
          refine ⟨43167534436395202287575371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57556712581860269716767161 43167534436395202287575371)
          ·
            refine ⟨64751301654592803431363057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43167534436395202287575371 64751301654592803431363057)
            ·
              refine ⟨48563476240944602573522293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64751301654592803431363057 48563476240944602573522293)
              ·
                refine ⟨4552825897588556491267715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48563476240944602573522293 4552825897588556491267715)
                ·
                  refine ⟨6829238846382834736901573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552825897588556491267715 6829238846382834736901573)
                  ·
                    refine ⟨1280482283696781513169045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829238846382834736901573 1280482283696781513169045)
                    ·
                      rfl

theorem cell23_7481191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_7481191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481191 prefixEnd_7481191 := by exact prefixLift 7481191
  have htrace : WordTrace (prefixWord ++ tailWord_7481191) baseStart_7481191 baseEnd_7481191 := by
    simpa [prefixWord, tailWord_7481191, baseEnd_7481191] using wordTrace_append hprefix tailTrace_7481191
  have hstable : (prefixWord ++ tailWord_7481191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481191).length < 2 ^ (prefixWord ++ tailWord_7481191).sum := by decide
  have hdescent : baseEnd_7481191 < baseStart_7481191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481241 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 2, 3, 2]
def baseStart_7481241 : Nat := 118140960795 + 7481241 * 2 ^ 59
def prefixEnd_7481241 : Nat := 4983230072969 + 3 ^ 40 * 7481241 * 2
def baseEnd_7481241 : Nat := 3841472525123069343881905

theorem tailTrace_7481241 : CollatzResearch.WordTrace tailWord_7481241 prefixEnd_7481241 3841472525123069343881905 := by
  unfold tailWord_7481241
  simp only [CollatzResearch.WordTrace]
  refine ⟨272863275889749026085475577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181908850593166017390317051 272863275889749026085475577)
  ·
    refine ⟨204647456917311769564106683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272863275889749026085475577 204647456917311769564106683)
    ·
      refine ⟨306971185375967654346160025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204647456917311769564106683 306971185375967654346160025)
      ·
        refine ⟨230228389031975740759620019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306971185375967654346160025 230228389031975740759620019)
        ·
          refine ⟨345342583547963611139430029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230228389031975740759620019 345342583547963611139430029)
          ·
            refine ⟨129503468830486354177286261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345342583547963611139430029 129503468830486354177286261)
            ·
              refine ⟨12140950202858095704120587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129503468830486354177286261 12140950202858095704120587)
              ·
                refine ⟨18211425304287143556180881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12140950202858095704120587 18211425304287143556180881)
                ·
                  refine ⟨13658568978215357667135661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18211425304287143556180881 13658568978215357667135661)
                  ·
                    refine ⟨5121963366830759125175873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13658568978215357667135661 5121963366830759125175873)
                    ·
                      refine ⟨3841472525123069343881905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121963366830759125175873 3841472525123069343881905)
                      ·
                        rfl

theorem cell23_7481241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_7481241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481241 prefixEnd_7481241 := by exact prefixLift 7481241
  have htrace : WordTrace (prefixWord ++ tailWord_7481241) baseStart_7481241 baseEnd_7481241 := by
    simpa [prefixWord, tailWord_7481241, baseEnd_7481241] using wordTrace_append hprefix tailTrace_7481241
  have hstable : (prefixWord ++ tailWord_7481241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481241).length < 2 ^ (prefixWord ++ tailWord_7481241).sum := by decide
  have hdescent : baseEnd_7481241 < baseStart_7481241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481267 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_7481267 : Nat := 118140960795 + 7481267 * 2 ^ 59
def prefixEnd_7481267 : Nat := 4983230072969 + 3 ^ 40 * 7481267 * 2
def baseEnd_7481267 : Nat := 3841485875620086242156785

theorem tailTrace_7481267 : CollatzResearch.WordTrace tailWord_7481267 prefixEnd_7481267 3841485875620086242156785 := by
  unfold tailWord_7481267
  simp only [CollatzResearch.WordTrace]
  refine ⟨272864224187654832525922055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181909482791769888350614703 272864224187654832525922055)
  ·
    refine ⟨409296336281482248788883083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272864224187654832525922055 409296336281482248788883083)
    ·
      refine ⟨613944504422223373183324625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409296336281482248788883083 613944504422223373183324625)
      ·
        refine ⟨460458378316667529887493469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613944504422223373183324625 460458378316667529887493469)
        ·
          refine ⟨172671891868750323707810051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460458378316667529887493469 172671891868750323707810051)
          ·
            refine ⟨259007837803125485561715077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172671891868750323707810051 259007837803125485561715077)
            ·
              refine ⟨48563969588086028542821577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259007837803125485561715077 48563969588086028542821577)
              ·
                refine ⟨36422977191064521407116183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48563969588086028542821577 36422977191064521407116183)
                ·
                  refine ⟨54634465786596782110674275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36422977191064521407116183 54634465786596782110674275)
                  ·
                    refine ⟨81951698679895173166011413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54634465786596782110674275 81951698679895173166011413)
                    ·
                      refine ⟨3841485875620086242156785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81951698679895173166011413 3841485875620086242156785)
                      ·
                        rfl

theorem cell23_7481267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_7481267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481267 prefixEnd_7481267 := by exact prefixLift 7481267
  have htrace : WordTrace (prefixWord ++ tailWord_7481267) baseStart_7481267 baseEnd_7481267 := by
    simpa [prefixWord, tailWord_7481267, baseEnd_7481267] using wordTrace_append hprefix tailTrace_7481267
  have hstable : (prefixWord ++ tailWord_7481267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481267).length < 2 ^ (prefixWord ++ tailWord_7481267).sum := by decide
  have hdescent : baseEnd_7481267 < baseStart_7481267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481274 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_7481274 : Nat := 118140960795 + 7481274 * 2 ^ 59
def prefixEnd_7481274 : Nat := 4983230072969 + 3 ^ 40 * 7481274 * 2
def baseEnd_7481274 : Nat := 3841489469984667714769253

theorem tailTrace_7481274 : CollatzResearch.WordTrace tailWord_7481274 prefixEnd_7481274 3841489469984667714769253 := by
  unfold tailWord_7481274
  simp only [CollatzResearch.WordTrace]
  refine ⟨68216119874657368180356719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181909652999086315147617917 68216119874657368180356719)
  ·
    refine ⟨102324179811986052270535079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68216119874657368180356719 102324179811986052270535079)
    ·
      refine ⟨153486269717979078405802619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102324179811986052270535079 153486269717979078405802619)
      ·
        refine ⟨230229404576968617608703929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153486269717979078405802619 230229404576968617608703929)
        ·
          refine ⟨172672053432726463206527947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230229404576968617608703929 172672053432726463206527947)
          ·
            refine ⟨259008080149089694809791921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172672053432726463206527947 259008080149089694809791921)
            ·
              refine ⟨194256060111817271107343941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259008080149089694809791921 194256060111817271107343941)
              ·
                refine ⟨36423011270965738332626989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194256060111817271107343941 36423011270965738332626989)
                ·
                  refine ⟨13658629226612151874735121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36423011270965738332626989 13658629226612151874735121)
                  ·
                    refine ⟨10243971919959113906051341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13658629226612151874735121 10243971919959113906051341)
                    ·
                      refine ⟨3841489469984667714769253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243971919959113906051341 3841489469984667714769253)
                      ·
                        rfl

theorem cell23_7481274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_7481274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481274 prefixEnd_7481274 := by exact prefixLift 7481274
  have htrace : WordTrace (prefixWord ++ tailWord_7481274) baseStart_7481274 baseEnd_7481274 := by
    simpa [prefixWord, tailWord_7481274, baseEnd_7481274] using wordTrace_append hprefix tailTrace_7481274
  have hstable : (prefixWord ++ tailWord_7481274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481274).length < 2 ^ (prefixWord ++ tailWord_7481274).sum := by decide
  have hdescent : baseEnd_7481274 < baseStart_7481274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481288 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_7481288 : Nat := 118140960795 + 7481288 * 2 ^ 59
def prefixEnd_7481288 : Nat := 4983230072969 + 3 ^ 40 * 7481288 * 2
def baseEnd_7481288 : Nat := 3841496658713830659994189

theorem tailTrace_7481288 : CollatzResearch.WordTrace tailWord_7481288 prefixEnd_7481288 3841496658713830659994189 := by
  unfold tailWord_7481288
  simp only [CollatzResearch.WordTrace]
  refine ⟨136432495060289376556218259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181909993413719168741624345 136432495060289376556218259)
  ·
    refine ⟨204648742590434064834327389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136432495060289376556218259 204648742590434064834327389)
    ·
      refine ⟨76743278471412774312872771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204648742590434064834327389 76743278471412774312872771)
      ·
        refine ⟨115114917707119161469309157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76743278471412774312872771 115114917707119161469309157)
        ·
          refine ⟨21584047070084842775495467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115114917707119161469309157 21584047070084842775495467)
          ·
            refine ⟨32376070605127264163243201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21584047070084842775495467 32376070605127264163243201)
            ·
              refine ⟨24282052953845448122432401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32376070605127264163243201 24282052953845448122432401)
              ·
                refine ⟨18211539715384086091824301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24282052953845448122432401 18211539715384086091824301)
                ·
                  refine ⟨6829327393269032284434113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18211539715384086091824301 6829327393269032284434113)
                  ·
                    refine ⟨5121995544951774213325585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6829327393269032284434113 5121995544951774213325585)
                    ·
                      refine ⟨3841496658713830659994189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5121995544951774213325585 3841496658713830659994189)
                      ·
                        rfl

theorem cell23_7481288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_7481288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481288 prefixEnd_7481288 := by exact prefixLift 7481288
  have htrace : WordTrace (prefixWord ++ tailWord_7481288) baseStart_7481288 baseEnd_7481288 := by
    simpa [prefixWord, tailWord_7481288, baseEnd_7481288] using wordTrace_append hprefix tailTrace_7481288
  have hstable : (prefixWord ++ tailWord_7481288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481288).length < 2 ^ (prefixWord ++ tailWord_7481288).sum := by decide
  have hdescent : baseEnd_7481288 < baseStart_7481288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481291 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 3]
def baseStart_7481291 : Nat := 118140960795 + 7481291 * 2 ^ 59
def prefixEnd_7481291 : Nat := 4983230072969 + 3 ^ 40 * 7481291 * 2
def baseEnd_7481291 : Nat := 3841498199155794148256675

theorem tailTrace_7481291 : CollatzResearch.WordTrace tailWord_7481291 prefixEnd_7481291 3841498199155794148256675 := by
  unfold tailWord_7481291
  simp only [CollatzResearch.WordTrace]
  refine ⟨272865099539567884624795727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181910066359711923083197151 272865099539567884624795727)
  ·
    refine ⟨409297649309351826937193591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272865099539567884624795727 409297649309351826937193591)
    ·
      refine ⟨613946473964027740405790387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409297649309351826937193591 613946473964027740405790387)
      ·
        refine ⟨920919710946041610608685581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613946473964027740405790387 920919710946041610608685581)
        ·
          refine ⟨345344891604765603978257093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920919710946041610608685581 345344891604765603978257093)
          ·
            refine ⟨64752167175893550745923205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345344891604765603978257093 64752167175893550745923205)
            ·
              refine ⟨12141031345480040764860601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64752167175893550745923205 12141031345480040764860601)
              ·
                refine ⟨9105773509110030573645451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12141031345480040764860601 9105773509110030573645451)
                ·
                  refine ⟨13658660263665045860468177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9105773509110030573645451 13658660263665045860468177)
                  ·
                    refine ⟨10243995197748784395351133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13658660263665045860468177 10243995197748784395351133)
                    ·
                      refine ⟨3841498199155794148256675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10243995197748784395351133 3841498199155794148256675)
                      ·
                        rfl

theorem cell23_7481291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 3].length) (baseStart_7481291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481291 prefixEnd_7481291 := by exact prefixLift 7481291
  have htrace : WordTrace (prefixWord ++ tailWord_7481291) baseStart_7481291 baseEnd_7481291 := by
    simpa [prefixWord, tailWord_7481291, baseEnd_7481291] using wordTrace_append hprefix tailTrace_7481291
  have hstable : (prefixWord ++ tailWord_7481291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481291).length < 2 ^ (prefixWord ++ tailWord_7481291).sum := by decide
  have hdescent : baseEnd_7481291 < baseStart_7481291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481304 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_7481304 : Nat := 118140960795 + 7481304 * 2 ^ 59
def prefixEnd_7481304 : Nat := 4983230072969 + 3 ^ 40 * 7481304 * 2
def baseEnd_7481304 : Nat := 3841504874404302597394115

theorem tailTrace_7481304 : CollatzResearch.WordTrace tailWord_7481304 prefixEnd_7481304 3841504874404302597394115 := by
  unfold tailWord_7481304
  simp only [CollatzResearch.WordTrace]
  refine ⟨136432786844260393922509483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181910382459013858563345977 136432786844260393922509483)
  ·
    refine ⟨204649180266390590883764225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136432786844260393922509483 204649180266390590883764225)
    ·
      refine ⟨153486885199792943162823169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204649180266390590883764225 153486885199792943162823169)
      ·
        refine ⟨115115163899844707372117377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153486885199792943162823169 115115163899844707372117377)
        ·
          refine ⟨86336372924883530529088033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115115163899844707372117377 86336372924883530529088033)
          ·
            refine ⟨64752279693662647896816025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86336372924883530529088033 64752279693662647896816025)
            ·
              refine ⟨48564209770246985922612019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64752279693662647896816025 48564209770246985922612019)
              ·
                refine ⟨72846314655370478883918029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48564209770246985922612019 72846314655370478883918029)
                ·
                  refine ⟨27317367995763929581469261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72846314655370478883918029 27317367995763929581469261)
                  ·
                    refine ⟨10244012998411473593050973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27317367995763929581469261 10244012998411473593050973)
                    ·
                      refine ⟨3841504874404302597394115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244012998411473593050973 3841504874404302597394115)
                      ·
                        rfl

theorem cell23_7481304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_7481304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481304 prefixEnd_7481304 := by exact prefixLift 7481304
  have htrace : WordTrace (prefixWord ++ tailWord_7481304) baseStart_7481304 baseEnd_7481304 := by
    simpa [prefixWord, tailWord_7481304, baseEnd_7481304] using wordTrace_append hprefix tailTrace_7481304
  have hstable : (prefixWord ++ tailWord_7481304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481304).length < 2 ^ (prefixWord ++ tailWord_7481304).sum := by decide
  have hdescent : baseEnd_7481304 < baseStart_7481304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481322 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_7481322 : Nat := 118140960795 + 7481322 * 2 ^ 59
def prefixEnd_7481322 : Nat := 4983230072969 + 3 ^ 40 * 7481322 * 2
def baseEnd_7481322 : Nat := 3841514117056083526969033

theorem tailTrace_7481322 : CollatzResearch.WordTrace tailWord_7481322 prefixEnd_7481322 3841514117056083526969033 := by
  unfold tailWord_7481322
  simp only [CollatzResearch.WordTrace]
  refine ⟨68216557550613894229793555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181910820134970384612782813 68216557550613894229793555)
  ·
    refine ⟨102324836325920841344690333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68216557550613894229793555 102324836325920841344690333)
    ·
      refine ⟨38371813622220315504258875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102324836325920841344690333 38371813622220315504258875)
      ·
        refine ⟨57557720433330473256388313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38371813622220315504258875 57557720433330473256388313)
        ·
          refine ⟨43168290324997854942291235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57557720433330473256388313 43168290324997854942291235)
          ·
            refine ⟨64752435487496782413436853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43168290324997854942291235 64752435487496782413436853)
            ·
              refine ⟨6070540826952823351259705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64752435487496782413436853 6070540826952823351259705)
              ·
                refine ⟨4552905620214617513444779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6070540826952823351259705 4552905620214617513444779)
                ·
                  refine ⟨6829358430321926270167169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552905620214617513444779 6829358430321926270167169)
                  ·
                    refine ⟨5122018822741444702625377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6829358430321926270167169 5122018822741444702625377)
                    ·
                      refine ⟨3841514117056083526969033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5122018822741444702625377 3841514117056083526969033)
                      ·
                        rfl

theorem cell23_7481322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_7481322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481322 prefixEnd_7481322 := by exact prefixLift 7481322
  have htrace : WordTrace (prefixWord ++ tailWord_7481322) baseStart_7481322 baseEnd_7481322 := by
    simpa [prefixWord, tailWord_7481322, baseEnd_7481322] using wordTrace_append hprefix tailTrace_7481322
  have hstable : (prefixWord ++ tailWord_7481322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481322).length < 2 ^ (prefixWord ++ tailWord_7481322).sum := by decide
  have hdescent : baseEnd_7481322 < baseStart_7481322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481401 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 7]
def baseStart_7481401 : Nat := 118140960795 + 7481401 * 2 ^ 59
def prefixEnd_7481401 : Nat := 4983230072969 + 3 ^ 40 * 7481401 * 2
def baseEnd_7481401 : Nat := 426839409114198746431241

theorem tailTrace_7481401 : CollatzResearch.WordTrace tailWord_7481401 prefixEnd_7481401 426839409114198746431241 := by
  unfold tailWord_7481401
  simp only [CollatzResearch.WordTrace]
  refine ⟨272869111569169373411300057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181912741046112915607533371 272869111569169373411300057)
  ·
    refine ⟨204651833676877030058475043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272869111569169373411300057 204651833676877030058475043)
    ·
      refine ⟨306977750515315545087712565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204651833676877030058475043 306977750515315545087712565)
      ·
        refine ⟨28779164110810832351973053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306977750515315545087712565 28779164110810832351973053)
        ·
          refine ⟨10792186541554062131989895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28779164110810832351973053 10792186541554062131989895)
          ·
            refine ⟨16188279812331093197984843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10792186541554062131989895 16188279812331093197984843)
            ·
              refine ⟨24282419718496639796977265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16188279812331093197984843 24282419718496639796977265)
              ·
                refine ⟨18211814788872479847732949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24282419718496639796977265 18211814788872479847732949)
                ·
                  refine ⟨426839409114198746431241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18211814788872479847732949 426839409114198746431241)
                  ·
                    rfl

theorem cell23_7481401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_7481401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481401 prefixEnd_7481401 := by exact prefixLift 7481401
  have htrace : WordTrace (prefixWord ++ tailWord_7481401) baseStart_7481401 baseEnd_7481401 := by
    simpa [prefixWord, tailWord_7481401, baseEnd_7481401] using wordTrace_append hprefix tailTrace_7481401
  have hstable : (prefixWord ++ tailWord_7481401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481401).length < 2 ^ (prefixWord ++ tailWord_7481401).sum := by decide
  have hdescent : baseEnd_7481401 < baseStart_7481401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481464 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_7481464 : Nat := 118140960795 + 7481464 * 2 ^ 59
def prefixEnd_7481464 : Nat := 4983230072969 + 3 ^ 40 * 7481464 * 2
def baseEnd_7481464 : Nat := 3841587031309021971393379

theorem tailTrace_7481464 : CollatzResearch.WordTrace tailWord_7481464 prefixEnd_7481464 3841587031309021971393379 := by
  unfold tailWord_7481464
  simp only [CollatzResearch.WordTrace]
  refine ⟨136435704683970567585421723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181914272911960756780562297 136435704683970567585421723)
  ·
    refine ⟨204653557025955851378132585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136435704683970567585421723 204653557025955851378132585)
    ·
      refine ⟨153490167769466888533599439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204653557025955851378132585 153490167769466888533599439)
      ·
        refine ⟨230235251654200332800399159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153490167769466888533599439 230235251654200332800399159)
        ·
          refine ⟨345352877481300499200598739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230235251654200332800399159 345352877481300499200598739)
          ·
            refine ⟨518029316221950748800898109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345352877481300499200598739 518029316221950748800898109)
            ·
              refine ⟨194260993583231530800336791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518029316221950748800898109 194260993583231530800336791)
              ·
                refine ⟨291391490374847296200505187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194260993583231530800336791 291391490374847296200505187)
                ·
                  refine ⟨437087235562270944300757781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291391490374847296200505187 437087235562270944300757781)
                  ·
                    refine ⟨20488464166981450514098021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 437087235562270944300757781 20488464166981450514098021)
                    ·
                      refine ⟨3841587031309021971393379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20488464166981450514098021 3841587031309021971393379)
                      ·
                        rfl

theorem cell23_7481464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_7481464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481464 prefixEnd_7481464 := by exact prefixLift 7481464
  have htrace : WordTrace (prefixWord ++ tailWord_7481464) baseStart_7481464 baseEnd_7481464 := by
    simpa [prefixWord, tailWord_7481464, baseEnd_7481464] using wordTrace_append hprefix tailTrace_7481464
  have hstable : (prefixWord ++ tailWord_7481464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481464).length < 2 ^ (prefixWord ++ tailWord_7481464).sum := by decide
  have hdescent : baseEnd_7481464 < baseStart_7481464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481495 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 3, 4]
def baseStart_7481495 : Nat := 118140960795 + 7481495 * 2 ^ 59
def prefixEnd_7481495 : Nat := 4983230072969 + 3 ^ 40 * 7481495 * 2
def baseEnd_7481495 : Nat := 1280534316403103783368579

theorem tailTrace_7481495 : CollatzResearch.WordTrace tailWord_7481495 prefixEnd_7481495 1280534316403103783368579 := by
  unfold tailWord_7481495
  simp only [CollatzResearch.WordTrace]
  refine ⟨272872540030828827465221939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181915026687219218310147959 272872540030828827465221939)
  ·
    refine ⟨409308810046243241197832909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272872540030828827465221939 409308810046243241197832909)
    ·
      refine ⟨153490803767341215449187341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409308810046243241197832909 153490803767341215449187341)
      ·
        refine ⟨57559051412752955793445253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153490803767341215449187341 57559051412752955793445253)
        ·
          refine ⟨10792322139891179211270985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57559051412752955793445253 10792322139891179211270985)
          ·
            refine ⟨8094241604918384408453239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10792322139891179211270985 8094241604918384408453239)
            ·
              refine ⟨12141362407377576612679859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094241604918384408453239 12141362407377576612679859)
              ·
                refine ⟨18212043611066364919019789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12141362407377576612679859 18212043611066364919019789)
                ·
                  refine ⟨6829516354149886844632421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18212043611066364919019789 6829516354149886844632421)
                  ·
                    refine ⟨1280534316403103783368579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829516354149886844632421 1280534316403103783368579)
                    ·
                      rfl

theorem cell23_7481495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_7481495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481495 prefixEnd_7481495 := by exact prefixLift 7481495
  have htrace : WordTrace (prefixWord ++ tailWord_7481495) baseStart_7481495 baseEnd_7481495 := by
    simpa [prefixWord, tailWord_7481495, baseEnd_7481495] using wordTrace_append hprefix tailTrace_7481495
  have hstable : (prefixWord ++ tailWord_7481495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481495).length < 2 ^ (prefixWord ++ tailWord_7481495).sum := by decide
  have hdescent : baseEnd_7481495 < baseStart_7481495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481508 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 6]
def baseStart_7481508 : Nat := 118140960795 + 7481508 * 2 ^ 59
def prefixEnd_7481508 : Nat := 4983230072969 + 3 ^ 40 * 7481508 * 2
def baseEnd_7481508 : Nat := 426845513828646644360353

theorem tailTrace_7481508 : CollatzResearch.WordTrace tailWord_7481508 prefixEnd_7481508 426845513828646644360353 := by
  unfold tailWord_7481508
  simp only [CollatzResearch.WordTrace]
  refine ⟨136436507089890865342722589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181915342786521153790296785 136436507089890865342722589)
  ·
    refine ⟨51163690158709074503520971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136436507089890865342722589 51163690158709074503520971)
    ·
      refine ⟨76745535238063611755281457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51163690158709074503520971 76745535238063611755281457)
      ·
        refine ⟨57559151428547708816461093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76745535238063611755281457 57559151428547708816461093)
        ·
          refine ⟨10792340892852695403086455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57559151428547708816461093 10792340892852695403086455)
          ·
            refine ⟨16188511339279043104629683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10792340892852695403086455 16188511339279043104629683)
            ·
              refine ⟨24282767008918564656944525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16188511339279043104629683 24282767008918564656944525)
              ·
                refine ⟨9106037628344461746354197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24282767008918564656944525 9106037628344461746354197)
                ·
                  refine ⟨426845513828646644360353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9106037628344461746354197 426845513828646644360353)
                  ·
                    rfl

theorem cell23_7481508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_7481508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481508 prefixEnd_7481508 := by exact prefixLift 7481508
  have htrace : WordTrace (prefixWord ++ tailWord_7481508) baseStart_7481508 baseEnd_7481508 := by
    simpa [prefixWord, tailWord_7481508, baseEnd_7481508] using wordTrace_append hprefix tailTrace_7481508
  have hstable : (prefixWord ++ tailWord_7481508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481508).length < 2 ^ (prefixWord ++ tailWord_7481508).sum := by decide
  have hdescent : baseEnd_7481508 < baseStart_7481508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481535 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 1, 1, 3]
def baseStart_7481535 : Nat := 118140960795 + 7481535 * 2 ^ 59
def prefixEnd_7481535 : Nat := 4983230072969 + 3 ^ 40 * 7481535 * 2
def baseEnd_7481535 : Nat := 3841623488435491193605553

theorem tailTrace_7481535 : CollatzResearch.WordTrace tailWord_7481535 prefixEnd_7481535 3841623488435491193605553 := by
  unfold tailWord_7481535
  simp only [CollatzResearch.WordTrace]
  refine ⟨272873998950683914296678059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181915999300455942864452039 272873998950683914296678059)
  ·
    refine ⟨409310998426025871445017089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272873998950683914296678059 409310998426025871445017089)
    ·
      refine ⟨306983248819519403583762817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409310998426025871445017089 306983248819519403583762817)
      ·
        refine ⟨230237436614639552687822113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306983248819519403583762817 230237436614639552687822113)
        ·
          refine ⟨172678077460979664515866585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230237436614639552687822113 172678077460979664515866585)
          ·
            refine ⟨129508558095734748386899939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172678077460979664515866585 129508558095734748386899939)
            ·
              refine ⟨194262837143602122580349909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129508558095734748386899939 194262837143602122580349909)
              ·
                refine ⟨4553035245553174747976951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194262837143602122580349909 4553035245553174747976951)
                ·
                  refine ⟨6829552868329762121965427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553035245553174747976951 6829552868329762121965427)
                  ·
                    refine ⟨10244329302494643182948141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829552868329762121965427 10244329302494643182948141)
                    ·
                      refine ⟨3841623488435491193605553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244329302494643182948141 3841623488435491193605553)
                      ·
                        rfl

theorem cell23_7481535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_7481535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481535 prefixEnd_7481535 := by exact prefixLift 7481535
  have htrace : WordTrace (prefixWord ++ tailWord_7481535) baseStart_7481535 baseEnd_7481535 := by
    simpa [prefixWord, tailWord_7481535, baseEnd_7481535] using wordTrace_append hprefix tailTrace_7481535
  have hstable : (prefixWord ++ tailWord_7481535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481535).length < 2 ^ (prefixWord ++ tailWord_7481535).sum := by decide
  have hdescent : baseEnd_7481535 < baseStart_7481535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481561 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_7481561 : Nat := 118140960795 + 7481561 * 2 ^ 59
def prefixEnd_7481561 : Nat := 4983230072969 + 3 ^ 40 * 7481561 * 2
def baseEnd_7481561 : Nat := 3841636838932508091880433

theorem tailTrace_7481561 : CollatzResearch.WordTrace tailWord_7481561 prefixEnd_7481561 3841636838932508091880433 := by
  unfold tailWord_7481561
  simp only [CollatzResearch.WordTrace]
  refine ⟨272874947248589720737124537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181916631499059813824749691 272874947248589720737124537)
  ·
    refine ⟨204656210436442290552843403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272874947248589720737124537 204656210436442290552843403)
    ·
      refine ⟨306984315654663435829265105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204656210436442290552843403 306984315654663435829265105)
      ·
        refine ⟨230238236740997576871948829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306984315654663435829265105 230238236740997576871948829)
        ·
          refine ⟨86339338777874091326980811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230238236740997576871948829 86339338777874091326980811)
          ·
            refine ⟨129509008166811136990471217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86339338777874091326980811 129509008166811136990471217)
            ·
              refine ⟨97131756125108352742853413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129509008166811136990471217 97131756125108352742853413)
              ·
                refine ⟨18212204273457816139285015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97131756125108352742853413 18212204273457816139285015)
                ·
                  refine ⟨27318306410186724208927523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18212204273457816139285015 27318306410186724208927523)
                  ·
                    refine ⟨40977459615280086313391285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27318306410186724208927523 40977459615280086313391285)
                    ·
                      refine ⟨3841636838932508091880433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40977459615280086313391285 3841636838932508091880433)
                      ·
                        rfl

theorem cell23_7481561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_7481561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481561 prefixEnd_7481561 := by exact prefixLift 7481561
  have htrace : WordTrace (prefixWord ++ tailWord_7481561) baseStart_7481561 baseEnd_7481561 := by
    simpa [prefixWord, tailWord_7481561, baseEnd_7481561] using wordTrace_append hprefix tailTrace_7481561
  have hstable : (prefixWord ++ tailWord_7481561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481561).length < 2 ^ (prefixWord ++ tailWord_7481561).sum := by decide
  have hdescent : baseEnd_7481561 < baseStart_7481561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481568 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_7481568 : Nat := 118140960795 + 7481568 * 2 ^ 59
def prefixEnd_7481568 : Nat := 4983230072969 + 3 ^ 40 * 7481568 * 2
def baseEnd_7481568 : Nat := 1280546811099029854830967

theorem tailTrace_7481568 : CollatzResearch.WordTrace tailWord_7481568 prefixEnd_7481568 1280546811099029854830967 := by
  unfold tailWord_7481568
  simp only [CollatzResearch.WordTrace]
  refine ⟨136437601279782180466314679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181916801706376240621752905 136437601279782180466314679)
  ·
    refine ⟨204656401919673270699472019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136437601279782180466314679 204656401919673270699472019)
    ·
      refine ⟨306984602879509906049208029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204656401919673270699472019 306984602879509906049208029)
      ·
        refine ⟨115119226079816214768453011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306984602879509906049208029 115119226079816214768453011)
        ·
          refine ⟨172678839119724322152679517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115119226079816214768453011 172678839119724322152679517)
          ·
            refine ⟨64754564669896620807254819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172678839119724322152679517 64754564669896620807254819)
            ·
              refine ⟨97131847004844931210882229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64754564669896620807254819 97131847004844931210882229)
              ·
                refine ⟨9106110656704212301020209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97131847004844931210882229 9106110656704212301020209)
                ·
                  refine ⟨6829582992528159225765157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9106110656704212301020209 6829582992528159225765157)
                  ·
                    refine ⟨1280546811099029854830967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829582992528159225765157 1280546811099029854830967)
                    ·
                      rfl

theorem cell23_7481568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_7481568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481568 prefixEnd_7481568 := by exact prefixLift 7481568
  have htrace : WordTrace (prefixWord ++ tailWord_7481568) baseStart_7481568 baseEnd_7481568 := by
    simpa [prefixWord, tailWord_7481568, baseEnd_7481568] using wordTrace_append hprefix tailTrace_7481568
  have hstable : (prefixWord ++ tailWord_7481568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481568).length < 2 ^ (prefixWord ++ tailWord_7481568).sum := by decide
  have hdescent : baseEnd_7481568 < baseStart_7481568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481578 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_7481578 : Nat := 118140960795 + 7481578 * 2 ^ 59
def prefixEnd_7481578 : Nat := 4983230072969 + 3 ^ 40 * 7481578 * 2
def baseEnd_7481578 : Nat := 3841645568103634525367855

theorem tailTrace_7481578 : CollatzResearch.WordTrace tailWord_7481578 prefixEnd_7481578 3841645568103634525367855 := by
  unfold tailWord_7481578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68218891822382033160123347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181917044859685421760328925 68218891822382033160123347)
  ·
    refine ⟨102328337733573049740185021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68218891822382033160123347 102328337733573049740185021)
    ·
      refine ⟨38373126650089893652569383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102328337733573049740185021 38373126650089893652569383)
      ·
        refine ⟨57559689975134840478854075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38373126650089893652569383 57559689975134840478854075)
        ·
          refine ⟨86339534962702260718281113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57559689975134840478854075 86339534962702260718281113)
          ·
            refine ⟨64754651222026695538710835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86339534962702260718281113 64754651222026695538710835)
            ·
              refine ⟨97131976833040043308066253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64754651222026695538710835 97131976833040043308066253)
              ·
                refine ⟨36424491312390016240524845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97131976833040043308066253 36424491312390016240524845)
                ·
                  refine ⟨13659184242146256090196817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36424491312390016240524845 13659184242146256090196817)
                  ·
                    refine ⟨10244388181609692067647613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13659184242146256090196817 10244388181609692067647613)
                    ·
                      refine ⟨3841645568103634525367855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10244388181609692067647613 3841645568103634525367855)
                      ·
                        rfl

theorem cell23_7481578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_7481578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481578 prefixEnd_7481578 := by exact prefixLift 7481578
  have htrace : WordTrace (prefixWord ++ tailWord_7481578) baseStart_7481578 baseEnd_7481578 := by
    simpa [prefixWord, tailWord_7481578, baseEnd_7481578] using wordTrace_append hprefix tailTrace_7481578
  have hstable : (prefixWord ++ tailWord_7481578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481578).length < 2 ^ (prefixWord ++ tailWord_7481578).sum := by decide
  have hdescent : baseEnd_7481578 < baseStart_7481578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7481602 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7481602 : Nat := 118140960795 + 7481602 * 2 ^ 59
def prefixEnd_7481602 : Nat := 4983230072969 + 3 ^ 40 * 7481602 * 2
def baseEnd_7481602 : Nat := 1280552630546447477155915

theorem tailTrace_7481602 : CollatzResearch.WordTrace tailWord_7481602 prefixEnd_7481602 1280552630546447477155915 := by
  unfold tailWord_7481602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68219110660360296184841765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181917628427627456492911373 68219110660360296184841765)
  ·
    refine ⟨12791083248817555534657831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68219110660360296184841765 12791083248817555534657831)
    ·
      refine ⟨19186624873226333301986747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12791083248817555534657831 19186624873226333301986747)
      ·
        refine ⟨28779937309839499952980121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19186624873226333301986747 28779937309839499952980121)
        ·
          refine ⟨21584952982379624964735091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28779937309839499952980121 21584952982379624964735091)
          ·
            refine ⟨32377429473569437447102637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21584952982379624964735091 32377429473569437447102637)
            ·
              refine ⟨12141536052588539042663489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32377429473569437447102637 12141536052588539042663489)
              ·
                refine ⟨9106152039441404281997617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12141536052588539042663489 9106152039441404281997617)
                ·
                  refine ⟨6829614029581053211498213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9106152039441404281997617 6829614029581053211498213)
                  ·
                    refine ⟨1280552630546447477155915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829614029581053211498213 1280552630546447477155915)
                    ·
                      rfl

theorem cell23_7481602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7481602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7481602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7481602 prefixEnd_7481602 := by exact prefixLift 7481602
  have htrace : WordTrace (prefixWord ++ tailWord_7481602) baseStart_7481602 baseEnd_7481602 := by
    simpa [prefixWord, tailWord_7481602, baseEnd_7481602] using wordTrace_append hprefix tailTrace_7481602
  have hstable : (prefixWord ++ tailWord_7481602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7481602).length < 2 ^ (prefixWord ++ tailWord_7481602).sum := by decide
  have hdescent : baseEnd_7481602 < baseStart_7481602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7481602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
