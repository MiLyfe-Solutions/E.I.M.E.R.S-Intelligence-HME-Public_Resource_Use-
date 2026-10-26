import V185TrunkScan23Chunk1214

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7198400 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3]
def baseStart_7198400 : Nat := 118140960795 + 7198400 * 2 ^ 59
def prefixEnd_7198400 : Nat := 4983230072969 + 3 ^ 40 * 7198400 * 2
def baseEnd_7198400 : Nat := 3696239143324741460595167

theorem tailTrace_7198400 : CollatzResearch.WordTrace tailWord_7198400 prefixEnd_7198400 3696239143324741460595167 := by
  unfold tailWord_7198400
  simp only [CollatzResearch.WordTrace]
  refine ⟨131273608560716831844232327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175031478080955775792309769 131273608560716831844232327)
  ·
    refine ⟨196910412841075247766348491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131273608560716831844232327 196910412841075247766348491)
    ·
      refine ⟨295365619261612871649522737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196910412841075247766348491 295365619261612871649522737)
      ·
        refine ⟨221524214446209653737142053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295365619261612871649522737 221524214446209653737142053)
        ·
          refine ⟨41535790208664310075714135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221524214446209653737142053 41535790208664310075714135)
          ·
            refine ⟨62303685312996465113571203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41535790208664310075714135 62303685312996465113571203)
            ·
              refine ⟨93455527969494697670356805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62303685312996465113571203 93455527969494697670356805)
              ·
                refine ⟨17522911494280255813191901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93455527969494697670356805 17522911494280255813191901)
                ·
                  refine ⟨6571091810355095929946963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17522911494280255813191901 6571091810355095929946963)
                  ·
                    refine ⟨9856637715532643894920445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6571091810355095929946963 9856637715532643894920445)
                    ·
                      refine ⟨3696239143324741460595167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856637715532643894920445 3696239143324741460595167)
                      ·
                        rfl

theorem cell23_7198400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_7198400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198400 prefixEnd_7198400 := by exact prefixLift 7198400
  have htrace : WordTrace (prefixWord ++ tailWord_7198400) baseStart_7198400 baseEnd_7198400 := by
    simpa [prefixWord, tailWord_7198400, baseEnd_7198400] using wordTrace_append hprefix tailTrace_7198400
  have hstable : (prefixWord ++ tailWord_7198400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198400).length < 2 ^ (prefixWord ++ tailWord_7198400).sum := by decide
  have hdescent : baseEnd_7198400 < baseStart_7198400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198443 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5]
def baseStart_7198443 : Nat := 118140960795 + 7198443 * 2 ^ 59
def prefixEnd_7198443 : Nat := 4983230072969 + 3 ^ 40 * 7198443 * 2
def baseEnd_7198443 : Nat := 3696261222992884792357469

theorem tailTrace_7198443 : CollatzResearch.WordTrace tailWord_7198443 prefixEnd_7198443 3696261222992884792357469 := by
  unfold tailWord_7198443
  simp only [CollatzResearch.WordTrace]
  refine ⟨262548785460277882032279983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175032523640185254688186655 262548785460277882032279983)
  ·
    refine ⟨393823178190416823048419975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262548785460277882032279983 393823178190416823048419975)
    ·
      refine ⟨590734767285625234572629963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393823178190416823048419975 590734767285625234572629963)
      ·
        refine ⟨886102150928437851858944945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590734767285625234572629963 886102150928437851858944945)
        ·
          refine ⟨664576613196328388894208709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886102150928437851858944945 664576613196328388894208709)
          ·
            refine ⟨124608114974311572917664133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 664576613196328388894208709 124608114974311572917664133)
            ·
              refine ⟨23364021557683419922062025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124608114974311572917664133 23364021557683419922062025)
              ·
                refine ⟨17523016168262564941546519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23364021557683419922062025 17523016168262564941546519)
                ·
                  refine ⟨26284524252393847412319779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17523016168262564941546519 26284524252393847412319779)
                  ·
                    refine ⟨39426786378590771118479669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26284524252393847412319779 39426786378590771118479669)
                    ·
                      refine ⟨3696261222992884792357469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39426786378590771118479669 3696261222992884792357469)
                      ·
                        rfl

theorem cell23_7198443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_7198443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198443 prefixEnd_7198443 := by exact prefixLift 7198443
  have htrace : WordTrace (prefixWord ++ tailWord_7198443) baseStart_7198443 baseEnd_7198443 := by
    simpa [prefixWord, tailWord_7198443, baseEnd_7198443] using wordTrace_append hprefix tailTrace_7198443
  have hstable : (prefixWord ++ tailWord_7198443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198443).length < 2 ^ (prefixWord ++ tailWord_7198443).sum := by decide
  have hdescent : baseEnd_7198443 < baseStart_7198443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198460 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_7198460 : Nat := 118140960795 + 7198460 * 2 ^ 59
def prefixEnd_7198460 : Nat := 4983230072969 + 3 ^ 40 * 7198460 * 2
def baseEnd_7198460 : Nat := 3696269952164011225844891

theorem tailTrace_7198460 : CollatzResearch.WordTrace tailWord_7198460 prefixEnd_7198460 3696269952164011225844891 := by
  unfold tailWord_7198460
  simp only [CollatzResearch.WordTrace]
  refine ⟨131274702750608146967824417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175032937000810862623765889 131274702750608146967824417)
  ·
    refine ⟨98456027062956110225868313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131274702750608146967824417 98456027062956110225868313)
    ·
      refine ⟨73842020297217082669401235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98456027062956110225868313 73842020297217082669401235)
      ·
        refine ⟨110763030445825624004101853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73842020297217082669401235 110763030445825624004101853)
        ·
          refine ⟨41536136417184609001538195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110763030445825624004101853 41536136417184609001538195)
          ·
            refine ⟨62304204625776913502307293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41536136417184609001538195 62304204625776913502307293)
            ·
              refine ⟨23364076734666342563365235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62304204625776913502307293 23364076734666342563365235)
              ·
                refine ⟨35046115101999513845047853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23364076734666342563365235 35046115101999513845047853)
                ·
                  refine ⟨13142293163249817691892945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35046115101999513845047853 13142293163249817691892945)
                  ·
                    refine ⟨9856719872437363268919709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13142293163249817691892945 9856719872437363268919709)
                    ·
                      refine ⟨3696269952164011225844891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856719872437363268919709 3696269952164011225844891)
                      ·
                        rfl

theorem cell23_7198460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_7198460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198460 prefixEnd_7198460 := by exact prefixLift 7198460
  have htrace : WordTrace (prefixWord ++ tailWord_7198460) baseStart_7198460 baseEnd_7198460 := by
    simpa [prefixWord, tailWord_7198460, baseEnd_7198460] using wordTrace_append hprefix tailTrace_7198460
  have hstable : (prefixWord ++ tailWord_7198460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198460).length < 2 ^ (prefixWord ++ tailWord_7198460).sum := by decide
  have hdescent : baseEnd_7198460 < baseStart_7198460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198533 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_7198533 : Nat := 118140960795 + 7198533 * 2 ^ 59
def prefixEnd_7198533 : Nat := 4983230072969 + 3 ^ 40 * 7198533 * 2
def baseEnd_7198533 : Nat := 3696307436251789440232055

theorem tailTrace_7198533 : CollatzResearch.WordTrace tailWord_7198533 prefixEnd_7198533 3696307436251789440232055 := by
  unfold tailWord_7198533
  simp only [CollatzResearch.WordTrace]
  refine ⟨262552068029951827403056253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175034712019967884935370835 262552068029951827403056253)
  ·
    refine ⟨98457025511231935276146095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262552068029951827403056253 98457025511231935276146095)
    ·
      refine ⟨147685538266847902914219143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98457025511231935276146095 147685538266847902914219143)
      ·
        refine ⟨221528307400271854371328715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147685538266847902914219143 221528307400271854371328715)
        ·
          refine ⟨332292461100407781556993073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221528307400271854371328715 332292461100407781556993073)
          ·
            refine ⟨249219345825305836167744805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332292461100407781556993073 249219345825305836167744805)
            ·
              refine ⟨46728627342244844281452151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249219345825305836167744805 46728627342244844281452151)
              ·
                refine ⟨70092941013367266422178227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46728627342244844281452151 70092941013367266422178227)
                ·
                  refine ⟨105139411520050899633267341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70092941013367266422178227 105139411520050899633267341)
                  ·
                    refine ⟨39427279320019087362475253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105139411520050899633267341 39427279320019087362475253)
                    ·
                      refine ⟨3696307436251789440232055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39427279320019087362475253 3696307436251789440232055)
                      ·
                        rfl

theorem cell23_7198533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_7198533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198533 prefixEnd_7198533 := by exact prefixLift 7198533
  have htrace : WordTrace (prefixWord ++ tailWord_7198533) baseStart_7198533 baseEnd_7198533 := by
    simpa [prefixWord, tailWord_7198533, baseEnd_7198533] using wordTrace_append hprefix tailTrace_7198533
  have hstable : (prefixWord ++ tailWord_7198533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198533).length < 2 ^ (prefixWord ++ tailWord_7198533).sum := by decide
  have hdescent : baseEnd_7198533 < baseStart_7198533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198541 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7198541 : Nat := 118140960795 + 7198541 * 2 ^ 59
def prefixEnd_7198541 : Nat := 4983230072969 + 3 ^ 40 * 7198541 * 2
def baseEnd_7198541 : Nat := 3696311544097025408932019

theorem tailTrace_7198541 : CollatzResearch.WordTrace tailWord_7198541 prefixEnd_7198541 3696311544097025408932019 := by
  unfold tailWord_7198541
  simp only [CollatzResearch.WordTrace]
  refine ⟨262552359813922844769347477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175034906542615229846231651 262552359813922844769347477)
  ·
    refine ⟨12307141866277633348563163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 262552359813922844769347477 12307141866277633348563163)
    ·
      refine ⟨18460712799416450022844745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307141866277633348563163 18460712799416450022844745)
      ·
        refine ⟨13845534599562337517133559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18460712799416450022844745 13845534599562337517133559)
        ·
          refine ⟨20768301899343506275700339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13845534599562337517133559 20768301899343506275700339)
          ·
            refine ⟨31152452849015259413550509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20768301899343506275700339 31152452849015259413550509)
            ·
              refine ⟨11682169818380722280081441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31152452849015259413550509 11682169818380722280081441)
              ·
                refine ⟨8761627363785541710061081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11682169818380722280081441 8761627363785541710061081)
                ·
                  refine ⟨6571220522839156282545811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8761627363785541710061081 6571220522839156282545811)
                  ·
                    refine ⟨9856830784258734423818717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6571220522839156282545811 9856830784258734423818717)
                    ·
                      refine ⟨3696311544097025408932019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9856830784258734423818717 3696311544097025408932019)
                      ·
                        rfl

theorem cell23_7198541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7198541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198541 prefixEnd_7198541 := by exact prefixLift 7198541
  have htrace : WordTrace (prefixWord ++ tailWord_7198541) baseStart_7198541 baseEnd_7198541 := by
    simpa [prefixWord, tailWord_7198541, baseEnd_7198541] using wordTrace_append hprefix tailTrace_7198541
  have hstable : (prefixWord ++ tailWord_7198541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198541).length < 2 ^ (prefixWord ++ tailWord_7198541).sum := by decide
  have hdescent : baseEnd_7198541 < baseStart_7198541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198560 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_7198560 : Nat := 118140960795 + 7198560 * 2 ^ 59
def prefixEnd_7198560 : Nat := 4983230072969 + 3 ^ 40 * 7198560 * 2
def baseEnd_7198560 : Nat := 3696321300229460834594431

theorem tailTrace_7198560 : CollatzResearch.WordTrace tailWord_7198560 prefixEnd_7198560 3696321300229460834594431 := by
  unfold tailWord_7198560
  simp only [CollatzResearch.WordTrace]
  refine ⟨131276526400427005507144567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175035368533902674009526089 131276526400427005507144567)
  ·
    refine ⟨196914789600640508260716851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131276526400427005507144567 196914789600640508260716851)
    ·
      refine ⟨295372184400960762391075277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196914789600640508260716851 295372184400960762391075277)
      ·
        refine ⟨110764569150360285896653229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295372184400960762391075277 110764569150360285896653229)
        ·
          refine ⟨41536713431385107211244961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110764569150360285896653229 41536713431385107211244961)
          ·
            refine ⟨31152535073538830408433721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41536713431385107211244961 31152535073538830408433721)
            ·
              refine ⟨23364401305154122806325291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31152535073538830408433721 23364401305154122806325291)
              ·
                refine ⟨35046601957731184209487937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23364401305154122806325291 35046601957731184209487937)
                ·
                  refine ⟨26284951468298388157115953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35046601957731184209487937 26284951468298388157115953)
                  ·
                    refine ⟨19713713601223791117836965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26284951468298388157115953 19713713601223791117836965)
                    ·
                      refine ⟨3696321300229460834594431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19713713601223791117836965 3696321300229460834594431)
                      ·
                        rfl

theorem cell23_7198560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_7198560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198560 prefixEnd_7198560 := by exact prefixLift 7198560
  have htrace : WordTrace (prefixWord ++ tailWord_7198560) baseStart_7198560 baseEnd_7198560 := by
    simpa [prefixWord, tailWord_7198560, baseEnd_7198560] using wordTrace_append hprefix tailTrace_7198560
  have hstable : (prefixWord ++ tailWord_7198560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198560).length < 2 ^ (prefixWord ++ tailWord_7198560).sum := by decide
  have hdescent : baseEnd_7198560 < baseStart_7198560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198677 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 6]
def baseStart_7198677 : Nat := 118140960795 + 7198677 * 2 ^ 59
def prefixEnd_7198677 : Nat := 4983230072969 + 3 ^ 40 * 7198677 * 2
def baseEnd_7198677 : Nat := 410709041940670764092377

theorem tailTrace_7198677 : CollatzResearch.WordTrace tailWord_7198677 prefixEnd_7198677 410709041940670764092377 := by
  unfold tailWord_7198677
  simp only [CollatzResearch.WordTrace]
  refine ⟨262557320141430139996298285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175038213427620093330865523 262557320141430139996298285)
  ·
    refine ⟨98458995053036302498611857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262557320141430139996298285 98458995053036302498611857)
    ·
      refine ⟨73844246289777226873958893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98458995053036302498611857 73844246289777226873958893)
      ·
        refine ⟨27691592358666460077734585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73844246289777226873958893 27691592358666460077734585)
        ·
          refine ⟨20768694268999845058300939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27691592358666460077734585 20768694268999845058300939)
          ·
            refine ⟨31153041403499767587451409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20768694268999845058300939 31153041403499767587451409)
            ·
              refine ⟨23364781052624825690588557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31153041403499767587451409 23364781052624825690588557)
              ·
                refine ⟨8761792894734309633970709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23364781052624825690588557 8761792894734309633970709)
                ·
                  refine ⟨410709041940670764092377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8761792894734309633970709 410709041940670764092377)
                  ·
                    rfl

theorem cell23_7198677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_7198677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198677 prefixEnd_7198677 := by exact prefixLift 7198677
  have htrace : WordTrace (prefixWord ++ tailWord_7198677) baseStart_7198677 baseEnd_7198677 := by
    simpa [prefixWord, tailWord_7198677, baseEnd_7198677] using wordTrace_append hprefix tailTrace_7198677
  have hstable : (prefixWord ++ tailWord_7198677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198677).length < 2 ^ (prefixWord ++ tailWord_7198677).sum := by decide
  have hdescent : baseEnd_7198677 < baseStart_7198677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198721 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_7198721 : Nat := 118140960795 + 7198721 * 2 ^ 59
def prefixEnd_7198721 : Nat := 4983230072969 + 3 ^ 40 * 7198721 * 2
def baseEnd_7198721 : Nat := 3696403970614834704681191

theorem tailTrace_7198721 : CollatzResearch.WordTrace tailWord_7198721 prefixEnd_7198721 3696403970614834704681191 := by
  unfold tailWord_7198721
  simp only [CollatzResearch.WordTrace]
  refine ⟨262558924953270735510900017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175039283302180490340600011 262558924953270735510900017)
  ·
    refine ⟨196919193714953051633175013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262558924953270735510900017 196919193714953051633175013)
    ·
      refine ⟨36922348821553697181220315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196919193714953051633175013 36922348821553697181220315)
      ·
        refine ⟨55383523232330545771830473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36922348821553697181220315 55383523232330545771830473)
        ·
          refine ⟨41537642424247909328872855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55383523232330545771830473 41537642424247909328872855)
          ·
            refine ⟨62306463636371863993309283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41537642424247909328872855 62306463636371863993309283)
            ·
              refine ⟨93459695454557795989963925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62306463636371863993309283 93459695454557795989963925)
              ·
                refine ⟨4380923224432396687029559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93459695454557795989963925 4380923224432396687029559)
                ·
                  refine ⟨6571384836648595030544339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380923224432396687029559 6571384836648595030544339)
                  ·
                    refine ⟨9857077254972892545816509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6571384836648595030544339 9857077254972892545816509)
                    ·
                      refine ⟨3696403970614834704681191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857077254972892545816509 3696403970614834704681191)
                      ·
                        rfl

theorem cell23_7198721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_7198721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198721 prefixEnd_7198721 := by exact prefixLift 7198721
  have htrace : WordTrace (prefixWord ++ tailWord_7198721) baseStart_7198721 baseEnd_7198721 := by
    simpa [prefixWord, tailWord_7198721, baseEnd_7198721] using wordTrace_append hprefix tailTrace_7198721
  have hstable : (prefixWord ++ tailWord_7198721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198721).length < 2 ^ (prefixWord ++ tailWord_7198721).sum := by decide
  have hdescent : baseEnd_7198721 < baseStart_7198721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198744 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7198744 : Nat := 118140960795 + 7198744 * 2 ^ 59
def prefixEnd_7198744 : Nat := 4983230072969 + 3 ^ 40 * 7198744 * 2
def baseEnd_7198744 : Nat := 3696415780669888114693585

theorem tailTrace_7198744 : CollatzResearch.WordTrace tailWord_7198744 prefixEnd_7198744 3696415780669888114693585 := by
  unfold tailWord_7198744
  simp only [CollatzResearch.WordTrace]
  refine ⟨131279881916093705219493643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175039842554791606959324857 131279881916093705219493643)
  ·
    refine ⟨196919822874140557829240465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131279881916093705219493643 196919822874140557829240465)
    ·
      refine ⟨147689867155605418371930349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196919822874140557829240465 147689867155605418371930349)
      ·
        refine ⟨55383700183352031889473881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147689867155605418371930349 55383700183352031889473881)
        ·
          refine ⟨41537775137514023917105411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55383700183352031889473881 41537775137514023917105411)
          ·
            refine ⟨62306662706271035875658117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41537775137514023917105411 62306662706271035875658117)
            ·
              refine ⟨11682499257425819226685897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62306662706271035875658117 11682499257425819226685897)
              ·
                refine ⟨8761874443069364420014423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11682499257425819226685897 8761874443069364420014423)
                ·
                  refine ⟨13142811664604046630021635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8761874443069364420014423 13142811664604046630021635)
                  ·
                    refine ⟨19714217496906069945032453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13142811664604046630021635 19714217496906069945032453)
                    ·
                      refine ⟨3696415780669888114693585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19714217496906069945032453 3696415780669888114693585)
                      ·
                        rfl

theorem cell23_7198744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7198744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198744 prefixEnd_7198744 := by exact prefixLift 7198744
  have htrace : WordTrace (prefixWord ++ tailWord_7198744) baseStart_7198744 baseEnd_7198744 := by
    simpa [prefixWord, tailWord_7198744, baseEnd_7198744] using wordTrace_append hprefix tailTrace_7198744
  have hstable : (prefixWord ++ tailWord_7198744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198744).length < 2 ^ (prefixWord ++ tailWord_7198744).sum := by decide
  have hdescent : baseEnd_7198744 < baseStart_7198744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198772 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7198772 : Nat := 118140960795 + 7198772 * 2 ^ 59
def prefixEnd_7198772 : Nat := 4983230072969 + 3 ^ 40 * 7198772 * 2
def baseEnd_7198772 : Nat := 3696430158128214005143457

theorem tailTrace_7198772 : CollatzResearch.WordTrace tailWord_7198772 prefixEnd_7198772 3696430158128214005143457 := by
  unfold tailWord_7198772
  simp only [CollatzResearch.WordTrace]
  refine ⟨131280392538042985610503285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175040523384057314147337713 131280392538042985610503285)
  ·
    refine ⟨12307536800441529900984683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131280392538042985610503285 12307536800441529900984683)
    ·
      refine ⟨18461305200662294851477025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307536800441529900984683 18461305200662294851477025)
      ·
        refine ⟨13845978900496721138607769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18461305200662294851477025 13845978900496721138607769)
        ·
          refine ⟨10384484175372540853955827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13845978900496721138607769 10384484175372540853955827)
          ·
            refine ⟨15576726263058811280933741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10384484175372540853955827 15576726263058811280933741)
            ·
              refine ⟨5841272348647054230350153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15576726263058811280933741 5841272348647054230350153)
              ·
                refine ⟨4380954261485290672762615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841272348647054230350153 4380954261485290672762615)
                ·
                  refine ⟨6571431392227936009143923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380954261485290672762615 6571431392227936009143923)
                  ·
                    refine ⟨9857147088341904013715885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6571431392227936009143923 9857147088341904013715885)
                    ·
                      refine ⟨3696430158128214005143457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857147088341904013715885 3696430158128214005143457)
                      ·
                        rfl

theorem cell23_7198772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7198772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198772 prefixEnd_7198772 := by exact prefixLift 7198772
  have htrace : WordTrace (prefixWord ++ tailWord_7198772) baseStart_7198772 baseEnd_7198772 := by
    simpa [prefixWord, tailWord_7198772, baseEnd_7198772] using wordTrace_append hprefix tailTrace_7198772
  have hstable : (prefixWord ++ tailWord_7198772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198772).length < 2 ^ (prefixWord ++ tailWord_7198772).sum := by decide
  have hdescent : baseEnd_7198772 < baseStart_7198772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198800 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_7198800 : Nat := 118140960795 + 7198800 * 2 ^ 59
def prefixEnd_7198800 : Nat := 4983230072969 + 3 ^ 40 * 7198800 * 2
def baseEnd_7198800 : Nat := 3696444535586539895593327

theorem tailTrace_7198800 : CollatzResearch.WordTrace tailWord_7198800 prefixEnd_7198800 3696444535586539895593327 := by
  unfold tailWord_7198800
  simp only [CollatzResearch.WordTrace]
  refine ⟨131280903159992266001512927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175041204213323021335350569 131280903159992266001512927)
  ·
    refine ⟨196921354739988399002269391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131280903159992266001512927 196921354739988399002269391)
    ·
      refine ⟨295382032109982598503404087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196921354739988399002269391 295382032109982598503404087)
      ·
        refine ⟨443073048164973897755106131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295382032109982598503404087 443073048164973897755106131)
        ·
          refine ⟨664609572247460846632659197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443073048164973897755106131 664609572247460846632659197)
          ·
            refine ⟨249228589592797817487247199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664609572247460846632659197 249228589592797817487247199)
            ·
              refine ⟨373842884389196726230870799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249228589592797817487247199 373842884389196726230870799)
              ·
                refine ⟨560764326583795089346306199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373842884389196726230870799 560764326583795089346306199)
                ·
                  refine ⟨841146489875692634019459299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560764326583795089346306199 841146489875692634019459299)
                  ·
                    refine ⟨1261719734813538951029188949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841146489875692634019459299 1261719734813538951029188949)
                    ·
                      refine ⟨3696444535586539895593327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1261719734813538951029188949 3696444535586539895593327)
                      ·
                        rfl

theorem cell23_7198800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_7198800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198800 prefixEnd_7198800 := by exact prefixLift 7198800
  have htrace : WordTrace (prefixWord ++ tailWord_7198800) baseStart_7198800 baseEnd_7198800 := by
    simpa [prefixWord, tailWord_7198800, baseEnd_7198800] using wordTrace_append hprefix tailTrace_7198800
  have hstable : (prefixWord ++ tailWord_7198800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198800).length < 2 ^ (prefixWord ++ tailWord_7198800).sum := by decide
  have hdescent : baseEnd_7198800 < baseStart_7198800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198851 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 1, 4, 2]
def baseStart_7198851 : Nat := 118140960795 + 7198851 * 2 ^ 59
def prefixEnd_7198851 : Nat := 4983230072969 + 3 ^ 40 * 7198851 * 2
def baseEnd_7198851 : Nat := 3696470723099919196055593

theorem tailTrace_7198851 : CollatzResearch.WordTrace tailWord_7198851 prefixEnd_7198851 3696470723099919196055593 := by
  unfold tailWord_7198851
  simp only [CollatzResearch.WordTrace]
  refine ⟨262563666442799767713132407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175042444295199845142088271 262563666442799767713132407)
  ·
    refine ⟨393845499664199651569698611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262563666442799767713132407 393845499664199651569698611)
    ·
      refine ⟨590768249496299477354547917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393845499664199651569698611 590768249496299477354547917)
      ·
        refine ⟨221538093561112304007955469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590768249496299477354547917 221538093561112304007955469)
        ·
          refine ⟨83076785085417114002983301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221538093561112304007955469 83076785085417114002983301)
          ·
            refine ⟨15576897203515708875559369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83076785085417114002983301 15576897203515708875559369)
            ·
              refine ⟨11682672902636781656669527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15576897203515708875559369 11682672902636781656669527)
              ·
                refine ⟨17524009353955172485004291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11682672902636781656669527 17524009353955172485004291)
                ·
                  refine ⟨26286014030932758727506437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17524009353955172485004291 26286014030932758727506437)
                  ·
                    refine ⟨4928627630799892261407457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26286014030932758727506437 4928627630799892261407457)
                    ·
                      refine ⟨3696470723099919196055593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928627630799892261407457 3696470723099919196055593)
                      ·
                        rfl

theorem cell23_7198851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_7198851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198851 prefixEnd_7198851 := by exact prefixLift 7198851
  have htrace : WordTrace (prefixWord ++ tailWord_7198851) baseStart_7198851 baseEnd_7198851 := by
    simpa [prefixWord, tailWord_7198851, baseEnd_7198851] using wordTrace_append hprefix tailTrace_7198851
  have hstable : (prefixWord ++ tailWord_7198851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198851).length < 2 ^ (prefixWord ++ tailWord_7198851).sum := by decide
  have hdescent : baseEnd_7198851 < baseStart_7198851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198857 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 7]
def baseStart_7198857 : Nat := 118140960795 + 7198857 * 2 ^ 59
def prefixEnd_7198857 : Nat := 4983230072969 + 3 ^ 40 * 7198857 * 2
def baseEnd_7198857 : Nat := 410719311553760685842285

theorem tailTrace_7198857 : CollatzResearch.WordTrace tailWord_7198857 prefixEnd_7198857 410719311553760685842285 := by
  unfold tailWord_7198857
  simp only [CollatzResearch.WordTrace]
  refine ⟨262563885280778030737850825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175042590187185353825233883 262563885280778030737850825)
  ·
    refine ⟨196922913960583523053388119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262563885280778030737850825 196922913960583523053388119)
    ·
      refine ⟨295384370940875284580082179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196922913960583523053388119 295384370940875284580082179)
      ·
        refine ⟨443076556411312926870123269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295384370940875284580082179 443076556411312926870123269)
        ·
          refine ⟨83076854327121173788148113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443076556411312926870123269 83076854327121173788148113)
          ·
            refine ⟨62307640745340880341111085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83076854327121173788148113 62307640745340880341111085)
            ·
              refine ⟨23365365279502830127916657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62307640745340880341111085 23365365279502830127916657)
              ·
                refine ⟨17524023959627122595937493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23365365279502830127916657 17524023959627122595937493)
                ·
                  refine ⟨410719311553760685842285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17524023959627122595937493 410719311553760685842285)
                  ·
                    rfl

theorem cell23_7198857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_7198857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198857 prefixEnd_7198857 := by exact prefixLift 7198857
  have htrace : WordTrace (prefixWord ++ tailWord_7198857) baseStart_7198857 baseEnd_7198857 := by
    simpa [prefixWord, tailWord_7198857, baseEnd_7198857] using wordTrace_append hprefix tailTrace_7198857
  have hstable : (prefixWord ++ tailWord_7198857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198857).length < 2 ^ (prefixWord ++ tailWord_7198857).sum := by decide
  have hdescent : baseEnd_7198857 < baseStart_7198857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198867 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3]
def baseStart_7198867 : Nat := 118140960795 + 7198867 * 2 ^ 59
def prefixEnd_7198867 : Nat := 4983230072969 + 3 ^ 40 * 7198867 * 2
def baseEnd_7198867 : Nat := 3696478938790391133455519

theorem tailTrace_7198867 : CollatzResearch.WordTrace tailWord_7198867 prefixEnd_7198867 3696478938790391133455519 := by
  unfold tailWord_7198867
  simp only [CollatzResearch.WordTrace]
  refine ⟨262564250010741802445714855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175042833340494534963809903 262564250010741802445714855)
  ·
    refine ⟨393846375016112703668572283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262564250010741802445714855 393846375016112703668572283)
    ·
      refine ⟨590769562524169055502858425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393846375016112703668572283 590769562524169055502858425)
      ·
        refine ⟨443077171893126791627143819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590769562524169055502858425 443077171893126791627143819)
        ·
          refine ⟨664615757839690187440715729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443077171893126791627143819 664615757839690187440715729)
          ·
            refine ⟨498461818379767640580536797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664615757839690187440715729 498461818379767640580536797)
            ·
              refine ⟨186923181892412865217701299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498461818379767640580536797 186923181892412865217701299)
              ·
                refine ⟨280384772838619297826551949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186923181892412865217701299 280384772838619297826551949)
                ·
                  refine ⟨105144289814482236684956981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280384772838619297826551949 105144289814482236684956981)
                  ·
                    refine ⟨9857277170107709689214717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105144289814482236684956981 9857277170107709689214717)
                    ·
                      refine ⟨3696478938790391133455519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857277170107709689214717 3696478938790391133455519)
                      ·
                        rfl

theorem cell23_7198867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_7198867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198867 prefixEnd_7198867 := by exact prefixLift 7198867
  have htrace : WordTrace (prefixWord ++ tailWord_7198867) baseStart_7198867 baseEnd_7198867 := by
    simpa [prefixWord, tailWord_7198867, baseEnd_7198867] using wordTrace_append hprefix tailTrace_7198867
  have hstable : (prefixWord ++ tailWord_7198867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198867).length < 2 ^ (prefixWord ++ tailWord_7198867).sum := by decide
  have hdescent : baseEnd_7198867 < baseStart_7198867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198872 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7198872 : Nat := 118140960795 + 7198872 * 2 ^ 59
def prefixEnd_7198872 : Nat := 4983230072969 + 3 ^ 40 * 7198872 * 2
def baseEnd_7198872 : Nat := 3696481506193663613892997

theorem tailTrace_7198872 : CollatzResearch.WordTrace tailWord_7198872 prefixEnd_7198872 3696481506193663613892997 := by
  unfold tailWord_7198872
  simp only [CollatzResearch.WordTrace]
  refine ⟨131282216187861844149823435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175042954917149125533097913 131282216187861844149823435)
  ·
    refine ⟨196923324281792766224735153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131282216187861844149823435 196923324281792766224735153)
    ·
      refine ⟨147692493211344574668551365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196923324281792766224735153 147692493211344574668551365)
      ·
        refine ⟨27692342477127107750353381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147692493211344574668551365 27692342477127107750353381)
        ·
          refine ⟨5192314214461332703191259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27692342477127107750353381 5192314214461332703191259)
          ·
            refine ⟨7788471321691999054786889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192314214461332703191259 7788471321691999054786889)
            ·
              refine ⟨5841353491268999291090167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7788471321691999054786889 5841353491268999291090167)
              ·
                refine ⟨8762030236903498936635251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841353491268999291090167 8762030236903498936635251)
                ·
                  refine ⟨13143045355355248404952877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8762030236903498936635251 13143045355355248404952877)
                  ·
                    refine ⟨4928642008258218151857329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13143045355355248404952877 4928642008258218151857329)
                    ·
                      refine ⟨3696481506193663613892997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928642008258218151857329 3696481506193663613892997)
                      ·
                        rfl

theorem cell23_7198872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7198872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198872 prefixEnd_7198872 := by exact prefixLift 7198872
  have htrace : WordTrace (prefixWord ++ tailWord_7198872) baseStart_7198872 baseEnd_7198872 := by
    simpa [prefixWord, tailWord_7198872, baseEnd_7198872] using wordTrace_append hprefix tailTrace_7198872
  have hstable : (prefixWord ++ tailWord_7198872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198872).length < 2 ^ (prefixWord ++ tailWord_7198872).sum := by decide
  have hdescent : baseEnd_7198872 < baseStart_7198872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198907 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_7198907 : Nat := 118140960795 + 7198907 * 2 ^ 59
def prefixEnd_7198907 : Nat := 4983230072969 + 3 ^ 40 * 7198907 * 2
def baseEnd_7198907 : Nat := 3696499478016570976955335

theorem tailTrace_7198907 : CollatzResearch.WordTrace tailWord_7198907 prefixEnd_7198907 3696499478016570976955335 := by
  unfold tailWord_7198907
  simp only [CollatzResearch.WordTrace]
  refine ⟨262565708930596889277170975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175043805953731259518113983 262565708930596889277170975)
  ·
    refine ⟨393848563395895333915756463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262565708930596889277170975 393848563395895333915756463)
    ·
      refine ⟨590772845093843000873634695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393848563395895333915756463 590772845093843000873634695)
      ·
        refine ⟨886159267640764501310452043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590772845093843000873634695 886159267640764501310452043)
        ·
          refine ⟨1329238901461146751965678065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886159267640764501310452043 1329238901461146751965678065)
          ·
            refine ⟨996929176095860063974258549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329238901461146751965678065 996929176095860063974258549)
            ·
              refine ⟨93462110258986880997586739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 996929176095860063974258549 93462110258986880997586739)
              ·
                refine ⟨140193165388480321496380109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93462110258986880997586739 140193165388480321496380109)
                ·
                  refine ⟨52572437020680120561142541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140193165388480321496380109 52572437020680120561142541)
                  ·
                    refine ⟨19714663882755045210428453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52572437020680120561142541 19714663882755045210428453)
                    ·
                      refine ⟨3696499478016570976955335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19714663882755045210428453 3696499478016570976955335)
                      ·
                        rfl

theorem cell23_7198907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_7198907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198907 prefixEnd_7198907 := by exact prefixLift 7198907
  have htrace : WordTrace (prefixWord ++ tailWord_7198907) baseStart_7198907 baseEnd_7198907 := by
    simpa [prefixWord, tailWord_7198907, baseEnd_7198907] using wordTrace_append hprefix tailTrace_7198907
  have hstable : (prefixWord ++ tailWord_7198907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198907).length < 2 ^ (prefixWord ++ tailWord_7198907).sum := by decide
  have hdescent : baseEnd_7198907 < baseStart_7198907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198937 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_7198937 : Nat := 118140960795 + 7198937 * 2 ^ 59
def prefixEnd_7198937 : Nat := 4983230072969 + 3 ^ 40 * 7198937 * 2
def baseEnd_7198937 : Nat := 3696514882436205859580197

theorem tailTrace_7198937 : CollatzResearch.WordTrace tailWord_7198937 prefixEnd_7198937 3696514882436205859580197 := by
  unfold tailWord_7198937
  simp only [CollatzResearch.WordTrace]
  refine ⟨262566803120488204400763065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175044535413658802933842043 262566803120488204400763065)
  ·
    refine ⟨196925102340366153300572299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262566803120488204400763065 196925102340366153300572299)
    ·
      refine ⟨295387653510549229950858449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196925102340366153300572299 295387653510549229950858449)
      ·
        refine ⟨221540740132911922463143837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295387653510549229950858449 221540740132911922463143837)
        ·
          refine ⟨83077777549841970923678939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221540740132911922463143837 83077777549841970923678939)
          ·
            refine ⟨124616666324762956385518409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83077777549841970923678939 124616666324762956385518409)
            ·
              refine ⟨93462499743572217289138807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124616666324762956385518409 93462499743572217289138807)
              ·
                refine ⟨140193749615358325933708211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93462499743572217289138807 140193749615358325933708211)
                ·
                  refine ⟨210290624423037488900562317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140193749615358325933708211 210290624423037488900562317)
                  ·
                    refine ⟨78858984158639058337710869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210290624423037488900562317 78858984158639058337710869)
                    ·
                      refine ⟨3696514882436205859580197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78858984158639058337710869 3696514882436205859580197)
                      ·
                        rfl

theorem cell23_7198937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_7198937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198937 prefixEnd_7198937 := by exact prefixLift 7198937
  have htrace : WordTrace (prefixWord ++ tailWord_7198937) baseStart_7198937 baseEnd_7198937 := by
    simpa [prefixWord, tailWord_7198937, baseEnd_7198937] using wordTrace_append hprefix tailTrace_7198937
  have hstable : (prefixWord ++ tailWord_7198937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198937).length < 2 ^ (prefixWord ++ tailWord_7198937).sum := by decide
  have hdescent : baseEnd_7198937 < baseStart_7198937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198941 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7198941 : Nat := 118140960795 + 7198941 * 2 ^ 59
def prefixEnd_7198941 : Nat := 4983230072969 + 3 ^ 40 * 7198941 * 2
def baseEnd_7198941 : Nat := 3696516936358823843930179

theorem tailTrace_7198941 : CollatzResearch.WordTrace tailWord_7198941 prefixEnd_7198941 3696516936358823843930179 := by
  unfold tailWord_7198941
  simp only [CollatzResearch.WordTrace]
  refine ⟨262566949012473713083908677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175044632674982475389272451 262566949012473713083908677)
  ·
    refine ⟨49231302939838821203232877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262566949012473713083908677 49231302939838821203232877)
    ·
      refine ⟨18461738602439557951212329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49231302939838821203232877 18461738602439557951212329)
      ·
        refine ⟨13846303951829668463409247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18461738602439557951212329 13846303951829668463409247)
        ·
          refine ⟨20769455927744502695113871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13846303951829668463409247 20769455927744502695113871)
          ·
            refine ⟨31154183891616754042670807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20769455927744502695113871 31154183891616754042670807)
            ·
              refine ⟨46731275837425131064006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31154183891616754042670807 46731275837425131064006211)
              ·
                refine ⟨70096913756137696596009317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46731275837425131064006211 70096913756137696596009317)
                ·
                  refine ⟨13143171329275818111751747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70096913756137696596009317 13143171329275818111751747)
                  ·
                    refine ⟨19714756993913727167627621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13143171329275818111751747 19714756993913727167627621)
                    ·
                      refine ⟨3696516936358823843930179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19714756993913727167627621 3696516936358823843930179)
                      ·
                        rfl

theorem cell23_7198941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7198941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198941 prefixEnd_7198941 := by exact prefixLift 7198941
  have htrace : WordTrace (prefixWord ++ tailWord_7198941) baseStart_7198941 baseEnd_7198941 := by
    simpa [prefixWord, tailWord_7198941, baseEnd_7198941] using wordTrace_append hprefix tailTrace_7198941
  have hstable : (prefixWord ++ tailWord_7198941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198941).length < 2 ^ (prefixWord ++ tailWord_7198941).sum := by decide
  have hdescent : baseEnd_7198941 < baseStart_7198941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7198978 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7198978 : Nat := 118140960795 + 7198978 * 2 ^ 59
def prefixEnd_7198978 : Nat := 4983230072969 + 3 ^ 40 * 7198978 * 2
def baseEnd_7198978 : Nat := 3696535935143040199167509

theorem tailTrace_7198978 : CollatzResearch.WordTrace tailWord_7198978 prefixEnd_7198978 3696535935143040199167509 := by
  unfold tailWord_7198978
  simp only [CollatzResearch.WordTrace]
  refine ⟨65642074628334917100751397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175045532342226445602003725 65642074628334917100751397)
  ·
    refine ⟨12307888992812796956390887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65642074628334917100751397 12307888992812796956390887)
    ·
      refine ⟨18461833489219195434586331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307888992812796956390887 18461833489219195434586331)
      ·
        refine ⟨27692750233828793151879497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18461833489219195434586331 27692750233828793151879497)
        ·
          refine ⟨20769562675371594863909623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27692750233828793151879497 20769562675371594863909623)
          ·
            refine ⟨31154344013057392295864435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20769562675371594863909623 31154344013057392295864435)
            ·
              refine ⟨46731516019586088443796653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31154344013057392295864435 46731516019586088443796653)
              ·
                refine ⟨17524318507344783166423745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46731516019586088443796653 17524318507344783166423745)
                ·
                  refine ⟨13143238880508587374817809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17524318507344783166423745 13143238880508587374817809)
                  ·
                    refine ⟨9857429160381440531113357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13143238880508587374817809 9857429160381440531113357)
                    ·
                      refine ⟨3696535935143040199167509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857429160381440531113357 3696535935143040199167509)
                      ·
                        rfl

theorem cell23_7198978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7198978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7198978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7198978 prefixEnd_7198978 := by exact prefixLift 7198978
  have htrace : WordTrace (prefixWord ++ tailWord_7198978) baseStart_7198978 baseEnd_7198978 := by
    simpa [prefixWord, tailWord_7198978, baseEnd_7198978] using wordTrace_append hprefix tailTrace_7198978
  have hstable : (prefixWord ++ tailWord_7198978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7198978).length < 2 ^ (prefixWord ++ tailWord_7198978).sum := by decide
  have hdescent : baseEnd_7198978 < baseStart_7198978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7198978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199002 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_7199002 : Nat := 118140960795 + 7199002 * 2 ^ 59
def prefixEnd_7199002 : Nat := 4983230072969 + 3 ^ 40 * 7199002 * 2
def baseEnd_7199002 : Nat := 1232182752892916035089133

theorem tailTrace_7199002 : CollatzResearch.WordTrace tailWord_7199002 prefixEnd_7199002 1232182752892916035089133 := by
  unfold tailWord_7199002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65642293466313180125469815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175046115910168480334586173 65642293466313180125469815)
  ·
    refine ⟨98463440199469770188204723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65642293466313180125469815 98463440199469770188204723)
    ·
      refine ⟨147695160299204655282307085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98463440199469770188204723 147695160299204655282307085)
      ·
        refine ⟨55385685112201745730865157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147695160299204655282307085 55385685112201745730865157)
        ·
          refine ⟨10384815958537827324537217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55385685112201745730865157 10384815958537827324537217)
          ·
            refine ⟨7788611968903370493402913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384815958537827324537217 7788611968903370493402913)
            ·
              refine ⟨5841458976677527870052185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7788611968903370493402913 5841458976677527870052185)
              ·
                refine ⟨4381094232508145902539139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841458976677527870052185 4381094232508145902539139)
                ·
                  refine ⟨6571641348762218853808709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381094232508145902539139 6571641348762218853808709)
                  ·
                    refine ⟨1232182752892916035089133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6571641348762218853808709 1232182752892916035089133)
                    ·
                      rfl

theorem cell23_7199002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_7199002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199002 prefixEnd_7199002 := by exact prefixLift 7199002
  have htrace : WordTrace (prefixWord ++ tailWord_7199002) baseStart_7199002 baseEnd_7199002 := by
    simpa [prefixWord, tailWord_7199002, baseEnd_7199002] using wordTrace_append hprefix tailTrace_7199002
  have hstable : (prefixWord ++ tailWord_7199002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199002).length < 2 ^ (prefixWord ++ tailWord_7199002).sum := by decide
  have hdescent : baseEnd_7199002 < baseStart_7199002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199048 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_7199048 : Nat := 118140960795 + 7199048 * 2 ^ 59
def prefixEnd_7199048 : Nat := 4983230072969 + 3 ^ 40 * 7199048 * 2
def baseEnd_7199048 : Nat := 3696571878788854925292187

theorem tailTrace_7199048 : CollatzResearch.WordTrace tailWord_7199048 prefixEnd_7199048 3696571878788854925292187 := by
  unfold tailWord_7199048
  simp only [CollatzResearch.WordTrace]
  refine ⟨131285425811543035179026899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175047234415390713572035865 131285425811543035179026899)
  ·
    refine ⟨196928138717314552768540349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131285425811543035179026899 196928138717314552768540349)
    ·
      refine ⟨73848052018992957288202631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196928138717314552768540349 73848052018992957288202631)
      ·
        refine ⟨110772078028489435932303947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73848052018992957288202631 110772078028489435932303947)
        ·
          refine ⟨166158117042734153898455921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110772078028489435932303947 166158117042734153898455921)
          ·
            refine ⟨124618587782050615423841941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166158117042734153898455921 124618587782050615423841941)
            ·
              refine ⟨5841496302283622597992591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124618587782050615423841941 5841496302283622597992591)
              ·
                refine ⟨8762244453425433896988887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841496302283622597992591 8762244453425433896988887)
                ·
                  refine ⟨13143366680138150845483331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8762244453425433896988887 13143366680138150845483331)
                  ·
                    refine ⟨19715050020207226268224997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13143366680138150845483331 19715050020207226268224997)
                    ·
                      refine ⟨3696571878788854925292187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19715050020207226268224997 3696571878788854925292187)
                      ·
                        rfl

theorem cell23_7199048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_7199048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199048 prefixEnd_7199048 := by exact prefixLift 7199048
  have htrace : WordTrace (prefixWord ++ tailWord_7199048) baseStart_7199048 baseEnd_7199048 := by
    simpa [prefixWord, tailWord_7199048, baseEnd_7199048] using wordTrace_append hprefix tailTrace_7199048
  have hstable : (prefixWord ++ tailWord_7199048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199048).length < 2 ^ (prefixWord ++ tailWord_7199048).sum := by decide
  have hdescent : baseEnd_7199048 < baseStart_7199048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199058 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_7199058 : Nat := 118140960795 + 7199058 * 2 ^ 59
def prefixEnd_7199058 : Nat := 4983230072969 + 3 ^ 40 * 7199058 * 2
def baseEnd_7199058 : Nat := 1232192337865133295389047

theorem tailTrace_7199058 : CollatzResearch.WordTrace tailWord_7199058 prefixEnd_7199058 1232192337865133295389047 := by
  unfold tailWord_7199058
  simp only [CollatzResearch.WordTrace]
  refine ⟨65642804088262460516479457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175047477568699894710611885 65642804088262460516479457)
  ·
    refine ⟨49232103066196845387359593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65642804088262460516479457 49232103066196845387359593)
    ·
      refine ⟨36924077299647634040519695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49232103066196845387359593 36924077299647634040519695)
      ·
        refine ⟨55386115949471451060779543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36924077299647634040519695 55386115949471451060779543)
        ·
          refine ⟨83079173924207176591169315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55386115949471451060779543 83079173924207176591169315)
          ·
            refine ⟨124618760886310764886753973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83079173924207176591169315 124618760886310764886753973)
            ·
              refine ⟨11683008833091634208133185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124618760886310764886753973 11683008833091634208133185)
              ·
                refine ⟨8762256624818725656099889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11683008833091634208133185 8762256624818725656099889)
                ·
                  refine ⟨6571692468614044242074917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8762256624818725656099889 6571692468614044242074917)
                  ·
                    refine ⟨1232192337865133295389047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6571692468614044242074917 1232192337865133295389047)
                    ·
                      rfl

theorem cell23_7199058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_7199058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199058 prefixEnd_7199058 := by exact prefixLift 7199058
  have htrace : WordTrace (prefixWord ++ tailWord_7199058) baseStart_7199058 baseEnd_7199058 := by
    simpa [prefixWord, tailWord_7199058, baseEnd_7199058] using wordTrace_append hprefix tailTrace_7199058
  have hstable : (prefixWord ++ tailWord_7199058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199058).length < 2 ^ (prefixWord ++ tailWord_7199058).sum := by decide
  have hdescent : baseEnd_7199058 < baseStart_7199058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199104 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_7199104 : Nat := 118140960795 + 7199104 * 2 ^ 59
def prefixEnd_7199104 : Nat := 4983230072969 + 3 ^ 40 * 7199104 * 2
def baseEnd_7199104 : Nat := 3696600633705506706191929

theorem tailTrace_7199104 : CollatzResearch.WordTrace tailWord_7199104 prefixEnd_7199104 3696600633705506706191929 := by
  unfold tailWord_7199104
  simp only [CollatzResearch.WordTrace]
  refine ⟨131286447055441595961046183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175048596073922127948061577 131286447055441595961046183)
  ·
    refine ⟨196929670583162393941569275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131286447055441595961046183 196929670583162393941569275)
    ·
      refine ⟨295394505874743590912353913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196929670583162393941569275 295394505874743590912353913)
      ·
        refine ⟨221545879406057693184265435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295394505874743590912353913 221545879406057693184265435)
        ·
          refine ⟨332318819109086539776398153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221545879406057693184265435 332318819109086539776398153)
          ·
            refine ⟨249239114331814904832298615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332318819109086539776398153 249239114331814904832298615)
            ·
              refine ⟨373858671497722357248447923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249239114331814904832298615 373858671497722357248447923)
              ·
                refine ⟨560788007246583535872671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373858671497722357248447923 560788007246583535872671885)
                ·
                  refine ⟨210295502717468825952251957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560788007246583535872671885 210295502717468825952251957)
                  ·
                    refine ⟨19715203379762702433023621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210295502717468825952251957 19715203379762702433023621)
                    ·
                      refine ⟨3696600633705506706191929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19715203379762702433023621 3696600633705506706191929)
                      ·
                        rfl

theorem cell23_7199104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_7199104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199104 prefixEnd_7199104 := by exact prefixLift 7199104
  have htrace : WordTrace (prefixWord ++ tailWord_7199104) baseStart_7199104 baseEnd_7199104 := by
    simpa [prefixWord, tailWord_7199104, baseEnd_7199104] using wordTrace_append hprefix tailTrace_7199104
  have hstable : (prefixWord ++ tailWord_7199104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199104).length < 2 ^ (prefixWord ++ tailWord_7199104).sum := by decide
  have hdescent : baseEnd_7199104 < baseStart_7199104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199121 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_7199121 : Nat := 118140960795 + 7199121 * 2 ^ 59
def prefixEnd_7199121 : Nat := 4983230072969 + 3 ^ 40 * 7199121 * 2
def baseEnd_7199121 : Nat := 3696609362876633139679351

theorem tailTrace_7199121 : CollatzResearch.WordTrace tailWord_7199121 prefixEnd_7199121 3696609362876633139679351 := by
  unfold tailWord_7199121
  simp only [CollatzResearch.WordTrace]
  refine ⟨262573514151821603825461217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175049009434547735883640811 262573514151821603825461217)
  ·
    refine ⟨196930135613866202869095913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262573514151821603825461217 196930135613866202869095913)
    ·
      refine ⟨147697601710399652151821935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196930135613866202869095913 147697601710399652151821935)
      ·
        refine ⟨221546402565599478227732903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147697601710399652151821935 221546402565599478227732903)
        ·
          refine ⟨332319603848399217341599355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221546402565599478227732903 332319603848399217341599355)
          ·
            refine ⟨498479405772598826012399033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332319603848399217341599355 498479405772598826012399033)
            ·
              refine ⟨373859554329449119509299275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498479405772598826012399033 373859554329449119509299275)
              ·
                refine ⟨560789331494173679263948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373859554329449119509299275 560789331494173679263948913)
                ·
                  refine ⟨420591998620630259447961685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560789331494173679263948913 420591998620630259447961685)
                  ·
                    refine ⟨4928812483835510852905801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 420591998620630259447961685 4928812483835510852905801)
                    ·
                      refine ⟨3696609362876633139679351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928812483835510852905801 3696609362876633139679351)
                      ·
                        rfl

theorem cell23_7199121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_7199121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199121 prefixEnd_7199121 := by exact prefixLift 7199121
  have htrace : WordTrace (prefixWord ++ tailWord_7199121) baseStart_7199121 baseEnd_7199121 := by
    simpa [prefixWord, tailWord_7199121, baseEnd_7199121] using wordTrace_append hprefix tailTrace_7199121
  have hstable : (prefixWord ++ tailWord_7199121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199121).length < 2 ^ (prefixWord ++ tailWord_7199121).sum := by decide
  have hdescent : baseEnd_7199121 < baseStart_7199121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199171 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3]
def baseStart_7199171 : Nat := 118140960795 + 7199171 * 2 ^ 59
def prefixEnd_7199171 : Nat := 4983230072969 + 3 ^ 40 * 7199171 * 2
def baseEnd_7199171 : Nat := 3696635036909357944054121

theorem tailTrace_7199171 : CollatzResearch.WordTrace tailWord_7199171 prefixEnd_7199171 3696635036909357944054121 := by
  unfold tailWord_7199171
  simp only [CollatzResearch.WordTrace]
  refine ⟨262575337801640462364781367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175050225201093641576520911 262575337801640462364781367)
  ·
    refine ⟨393863006702460693547172051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262575337801640462364781367 393863006702460693547172051)
    ·
      refine ⟨590794510053691040320758077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393863006702460693547172051 590794510053691040320758077)
      ·
        refine ⟨221547941270134140120284279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590794510053691040320758077 221547941270134140120284279)
        ·
          refine ⟨332321911905201210180426419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221547941270134140120284279 332321911905201210180426419)
          ·
            refine ⟨498482867857801815270639629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332321911905201210180426419 498482867857801815270639629)
            ·
              refine ⟨186931075446675680726489861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498482867857801815270639629 186931075446675680726489861)
              ·
                refine ⟨35049576646251690136216849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186931075446675680726489861 35049576646251690136216849)
                ·
                  refine ⟨26287182484688767602162637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35049576646251690136216849 26287182484688767602162637)
                  ·
                    refine ⟨9857693431758287850810989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26287182484688767602162637 9857693431758287850810989)
                    ·
                      refine ⟨3696635036909357944054121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857693431758287850810989 3696635036909357944054121)
                      ·
                        rfl

theorem cell23_7199171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_7199171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199171 prefixEnd_7199171 := by exact prefixLift 7199171
  have htrace : WordTrace (prefixWord ++ tailWord_7199171) baseStart_7199171 baseEnd_7199171 := by
    simpa [prefixWord, tailWord_7199171, baseEnd_7199171] using wordTrace_append hprefix tailTrace_7199171
  have hstable : (prefixWord ++ tailWord_7199171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199171).length < 2 ^ (prefixWord ++ tailWord_7199171).sum := by decide
  have hdescent : baseEnd_7199171 < baseStart_7199171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199178 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_7199178 : Nat := 118140960795 + 7199178 * 2 ^ 59
def prefixEnd_7199178 : Nat := 4983230072969 + 3 ^ 40 * 7199178 * 2
def baseEnd_7199178 : Nat := 410737625697104379629621

theorem tailTrace_7199178 : CollatzResearch.WordTrace tailWord_7199178 prefixEnd_7199178 410737625697104379629621 := by
  unfold tailWord_7199178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65643898278153775640071547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175050395408410068373524125 65643898278153775640071547)
  ·
    refine ⟨98465847417230663460107321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65643898278153775640071547 98465847417230663460107321)
    ·
      refine ⟨73849385562922997595080491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98465847417230663460107321 73849385562922997595080491)
      ·
        refine ⟨110774078344384496392620737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73849385562922997595080491 110774078344384496392620737)
        ·
          refine ⟨83080558758288372294465553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110774078344384496392620737 83080558758288372294465553)
          ·
            refine ⟨62310419068716279220849165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83080558758288372294465553 62310419068716279220849165)
            ·
              refine ⟨23366407150768604707818437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62310419068716279220849165 23366407150768604707818437)
              ·
                refine ⟨4381201340769113382715957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23366407150768604707818437 4381201340769113382715957)
                ·
                  refine ⟨410737625697104379629621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381201340769113382715957 410737625697104379629621)
                  ·
                    rfl

theorem cell23_7199178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_7199178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199178 prefixEnd_7199178 := by exact prefixLift 7199178
  have htrace : WordTrace (prefixWord ++ tailWord_7199178) baseStart_7199178 baseEnd_7199178 := by
    simpa [prefixWord, tailWord_7199178, baseEnd_7199178] using wordTrace_append hprefix tailTrace_7199178
  have hstable : (prefixWord ++ tailWord_7199178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199178).length < 2 ^ (prefixWord ++ tailWord_7199178).sum := by decide
  have hdescent : baseEnd_7199178 < baseStart_7199178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199188 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7199188 : Nat := 118140960795 + 7199188 * 2 ^ 59
def prefixEnd_7199188 : Nat := 4983230072969 + 3 ^ 40 * 7199188 * 2
def baseEnd_7199188 : Nat := 3696643766080484377541543

theorem tailTrace_7199188 : CollatzResearch.WordTrace tailWord_7199188 prefixEnd_7199188 3696643766080484377541543 := by
  unfold tailWord_7199188
  simp only [CollatzResearch.WordTrace]
  refine ⟨131287978921289437134075109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175050638561719249512100145 131287978921289437134075109)
  ·
    refine ⟨24616496047741769462639083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131287978921289437134075109 24616496047741769462639083)
    ·
      refine ⟨36924744071612654193958625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24616496047741769462639083 36924744071612654193958625)
      ·
        refine ⟨27693558053709490645468969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36924744071612654193958625 27693558053709490645468969)
        ·
          refine ⟨20770168540282117984101727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27693558053709490645468969 20770168540282117984101727)
          ·
            refine ⟨31155252810423176976152591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20770168540282117984101727 31155252810423176976152591)
            ·
              refine ⟨46732879215634765464228887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31155252810423176976152591 46732879215634765464228887)
              ·
                refine ⟨70099318823452148196343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46732879215634765464228887 70099318823452148196343331)
                ·
                  refine ⟨105148978235178222294514997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70099318823452148196343331 105148978235178222294514997)
                  ·
                    refine ⟨9857716709547958340110781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105148978235178222294514997 9857716709547958340110781)
                    ·
                      refine ⟨3696643766080484377541543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857716709547958340110781 3696643766080484377541543)
                      ·
                        rfl

theorem cell23_7199188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7199188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199188 prefixEnd_7199188 := by exact prefixLift 7199188
  have htrace : WordTrace (prefixWord ++ tailWord_7199188) baseStart_7199188 baseEnd_7199188 := by
    simpa [prefixWord, tailWord_7199188, baseEnd_7199188] using wordTrace_append hprefix tailTrace_7199188
  have hstable : (prefixWord ++ tailWord_7199188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199188).length < 2 ^ (prefixWord ++ tailWord_7199188).sum := by decide
  have hdescent : baseEnd_7199188 < baseStart_7199188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199208 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_7199208 : Nat := 118140960795 + 7199208 * 2 ^ 59
def prefixEnd_7199208 : Nat := 4983230072969 + 3 ^ 40 * 7199208 * 2
def baseEnd_7199208 : Nat := 1232218011897858099763817

theorem tailTrace_7199208 : CollatzResearch.WordTrace tailWord_7199208 prefixEnd_7199208 1232218011897858099763817 := by
  unfold tailWord_7199208
  simp only [CollatzResearch.WordTrace]
  refine ⟨131288343651253208841939139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175051124868337611789252185 131288343651253208841939139)
  ·
    refine ⟨196932515476879813262908709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131288343651253208841939139 196932515476879813262908709)
    ·
      refine ⟨36924846651914964986795383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196932515476879813262908709 36924846651914964986795383)
      ·
        refine ⟨55387269977872447480193075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36924846651914964986795383 55387269977872447480193075)
        ·
          refine ⟨83080904966808671220289613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55387269977872447480193075 83080904966808671220289613)
          ·
            refine ⟨31155339362553251707608605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83080904966808671220289613 31155339362553251707608605)
            ·
              refine ⟨11683252260957469390353227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31155339362553251707608605 11683252260957469390353227)
              ·
                refine ⟨17524878391436204085529841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11683252260957469390353227 17524878391436204085529841)
                ·
                  refine ⟨13143658793577153064147381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17524878391436204085529841 13143658793577153064147381)
                  ·
                    refine ⟨1232218011897858099763817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13143658793577153064147381 1232218011897858099763817)
                    ·
                      rfl

theorem cell23_7199208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_7199208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199208 prefixEnd_7199208 := by exact prefixLift 7199208
  have htrace : WordTrace (prefixWord ++ tailWord_7199208) baseStart_7199208 baseEnd_7199208 := by
    simpa [prefixWord, tailWord_7199208, baseEnd_7199208] using wordTrace_append hprefix tailTrace_7199208
  have hstable : (prefixWord ++ tailWord_7199208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199208).length < 2 ^ (prefixWord ++ tailWord_7199208).sum := by decide
  have hdescent : baseEnd_7199208 < baseStart_7199208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199211 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_7199211 : Nat := 118140960795 + 7199211 * 2 ^ 59
def prefixEnd_7199211 : Nat := 4983230072969 + 3 ^ 40 * 7199211 * 2
def baseEnd_7199211 : Nat := 3696655576135537787553937

theorem tailTrace_7199211 : CollatzResearch.WordTrace tailWord_7199211 prefixEnd_7199211 3696655576135537787553937 := by
  unfold tailWord_7199211
  simp only [CollatzResearch.WordTrace]
  refine ⟨262576796721495549196237487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175051197814330366130824991 262576796721495549196237487)
  ·
    refine ⟨393865195082243323794356231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262576796721495549196237487 393865195082243323794356231)
    ·
      refine ⟨590797792623364985691534347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393865195082243323794356231 590797792623364985691534347)
      ·
        refine ⟨886196688935047478537301521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590797792623364985691534347 886196688935047478537301521)
        ·
          refine ⟨664647516701285608902976141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886196688935047478537301521 664647516701285608902976141)
          ·
            refine ⟨249242818762982103338616053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664647516701285608902976141 249242818762982103338616053)
            ·
              refine ⟨23366514259029572187995255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249242818762982103338616053 23366514259029572187995255)
              ·
                refine ⟨35049771388544358281992883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23366514259029572187995255 35049771388544358281992883)
                ·
                  refine ⟨52574657082816537422989325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35049771388544358281992883 52574657082816537422989325)
                  ·
                    refine ⟨19715496406056201533620997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52574657082816537422989325 19715496406056201533620997)
                    ·
                      refine ⟨3696655576135537787553937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19715496406056201533620997 3696655576135537787553937)
                      ·
                        rfl

theorem cell23_7199211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_7199211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199211 prefixEnd_7199211 := by exact prefixLift 7199211
  have htrace : WordTrace (prefixWord ++ tailWord_7199211) baseStart_7199211 baseEnd_7199211 := by
    simpa [prefixWord, tailWord_7199211, baseEnd_7199211] using wordTrace_append hprefix tailTrace_7199211
  have hstable : (prefixWord ++ tailWord_7199211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199211).length < 2 ^ (prefixWord ++ tailWord_7199211).sum := by decide
  have hdescent : baseEnd_7199211 < baseStart_7199211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199302 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_7199302 : Nat := 118140960795 + 7199302 * 2 ^ 59
def prefixEnd_7199302 : Nat := 4983230072969 + 3 ^ 40 * 7199302 * 2
def baseEnd_7199302 : Nat := 410744700319455214612891

theorem tailTrace_7199302 : CollatzResearch.WordTrace tailWord_7199302 prefixEnd_7199302 410744700319455214612891 := by
  unfold tailWord_7199302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205628617630183491806255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175053410509443914491866773 8205628617630183491806255)
  ·
    refine ⟨12308442926445275237709383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205628617630183491806255 12308442926445275237709383)
    ·
      refine ⟨18462664389667912856564075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12308442926445275237709383 18462664389667912856564075)
      ·
        refine ⟨27693996584501869284846113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18462664389667912856564075 27693996584501869284846113)
        ·
          refine ⟨20770497438376401963634585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27693996584501869284846113 20770497438376401963634585)
          ·
            refine ⟨15577873078782301472725939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20770497438376401963634585 15577873078782301472725939)
            ·
              refine ⟨23366809618173452209088909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15577873078782301472725939 23366809618173452209088909)
              ·
                refine ⟨8762553606815044578408341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23366809618173452209088909 8762553606815044578408341)
                ·
                  refine ⟨410744700319455214612891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8762553606815044578408341 410744700319455214612891)
                  ·
                    rfl

theorem cell23_7199302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_7199302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199302 prefixEnd_7199302 := by exact prefixLift 7199302
  have htrace : WordTrace (prefixWord ++ tailWord_7199302) baseStart_7199302 baseEnd_7199302 := by
    simpa [prefixWord, tailWord_7199302, baseEnd_7199302] using wordTrace_append hprefix tailTrace_7199302
  have hstable : (prefixWord ++ tailWord_7199302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199302).length < 2 ^ (prefixWord ++ tailWord_7199302).sum := by decide
  have hdescent : baseEnd_7199302 < baseStart_7199302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199321 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_7199321 : Nat := 118140960795 + 7199321 * 2 ^ 59
def prefixEnd_7199321 : Nat := 4983230072969 + 3 ^ 40 * 7199321 * 2
def baseEnd_7199321 : Nat := 3696712059007532357178431

theorem tailTrace_7199321 : CollatzResearch.WordTrace tailWord_7199321 prefixEnd_7199321 3696712059007532357178431 := by
  unfold tailWord_7199321
  simp only [CollatzResearch.WordTrace]
  refine ⟨262580808751097037982741817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175053872500731358655161211 262580808751097037982741817)
  ·
    refine ⟨196935606563322778487056363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262580808751097037982741817 196935606563322778487056363)
    ·
      refine ⟨295403409844984167730584545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196935606563322778487056363 295403409844984167730584545)
      ·
        refine ⟨221552557383738125797938409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295403409844984167730584545 221552557383738125797938409)
        ·
          refine ⟨166164418037803594348453807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221552557383738125797938409 166164418037803594348453807)
          ·
            refine ⟨249246627056705391522680711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166164418037803594348453807 249246627056705391522680711)
            ·
              refine ⟨373869940585058087284021067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249246627056705391522680711 373869940585058087284021067)
              ·
                refine ⟨560804910877587130926031601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373869940585058087284021067 560804910877587130926031601)
                ·
                  refine ⟨420603683158190348194523701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560804910877587130926031601 420603683158190348194523701)
                  ·
                    refine ⟨39431595296080345143236597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 420603683158190348194523701 39431595296080345143236597)
                    ·
                      refine ⟨3696712059007532357178431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39431595296080345143236597 3696712059007532357178431)
                      ·
                        rfl

theorem cell23_7199321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_7199321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199321 prefixEnd_7199321 := by exact prefixLift 7199321
  have htrace : WordTrace (prefixWord ++ tailWord_7199321) baseStart_7199321 baseEnd_7199321 := by
    simpa [prefixWord, tailWord_7199321, baseEnd_7199321] using wordTrace_append hprefix tailTrace_7199321
  have hstable : (prefixWord ++ tailWord_7199321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199321).length < 2 ^ (prefixWord ++ tailWord_7199321).sum := by decide
  have hdescent : baseEnd_7199321 < baseStart_7199321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199328 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_7199328 : Nat := 118140960795 + 7199328 * 2 ^ 59
def prefixEnd_7199328 : Nat := 4983230072969 + 3 ^ 40 * 7199328 * 2
def baseEnd_7199328 : Nat := 1232238551124037943263633

theorem tailTrace_7199328 : CollatzResearch.WordTrace tailWord_7199328 prefixEnd_7199328 1232238551124037943263633 := by
  unfold tailWord_7199328
  simp only [CollatzResearch.WordTrace]
  refine ⟨131290532031035839089123319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175054042708047785452164425 131290532031035839089123319)
  ·
    refine ⟨196935798046553758633684979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131290532031035839089123319 196935798046553758633684979)
    ·
      refine ⟨295403697069830637950527469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196935798046553758633684979 295403697069830637950527469)
      ·
        refine ⟨110776386401186489231447801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295403697069830637950527469 110776386401186489231447801)
        ·
          refine ⟨83082289800889866923585851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110776386401186489231447801 83082289800889866923585851)
          ·
            refine ⟨124623434701334800385378777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83082289800889866923585851 124623434701334800385378777)
            ·
              refine ⟨93467576026001100289034083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124623434701334800385378777 93467576026001100289034083)
              ·
                refine ⟨140201364039001650433551125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93467576026001100289034083 140201364039001650433551125)
                ·
                  refine ⟨6571938939328202364072709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140201364039001650433551125 6571938939328202364072709)
                  ·
                    refine ⟨1232238551124037943263633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6571938939328202364072709 1232238551124037943263633)
                    ·
                      rfl

theorem cell23_7199328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_7199328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199328 prefixEnd_7199328 := by exact prefixLift 7199328
  have htrace : WordTrace (prefixWord ++ tailWord_7199328) baseStart_7199328 baseEnd_7199328 := by
    simpa [prefixWord, tailWord_7199328, baseEnd_7199328] using wordTrace_append hprefix tailTrace_7199328
  have hstable : (prefixWord ++ tailWord_7199328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199328).length < 2 ^ (prefixWord ++ tailWord_7199328).sum := by decide
  have hdescent : baseEnd_7199328 < baseStart_7199328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199365 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_7199365 : Nat := 118140960795 + 7199365 * 2 ^ 59
def prefixEnd_7199365 : Nat := 4983230072969 + 3 ^ 40 * 7199365 * 2
def baseEnd_7199365 : Nat := 3696734652156330185028229

theorem tailTrace_7199365 : CollatzResearch.WordTrace tailWord_7199365 prefixEnd_7199365 3696734652156330185028229 := by
  unfold tailWord_7199365
  simp only [CollatzResearch.WordTrace]
  refine ⟨262582413562937633497343549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175054942375291755664895699 262582413562937633497343549)
  ·
    refine ⟨98468405086101612561503831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262582413562937633497343549 98468405086101612561503831)
    ·
      refine ⟨147702607629152418842255747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98468405086101612561503831 147702607629152418842255747)
      ·
        refine ⟨221553911443728628263383621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147702607629152418842255747 221553911443728628263383621)
        ·
          refine ⟨41541358395699117799384429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221553911443728628263383621 41541358395699117799384429)
          ·
            refine ⟨15578009398387169174769161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41541358395699117799384429 15578009398387169174769161)
            ·
              refine ⟨11683507048790376881076871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15578009398387169174769161 11683507048790376881076871)
              ·
                refine ⟨17525260573185565321615307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11683507048790376881076871 17525260573185565321615307)
                ·
                  refine ⟨26287890859778347982422961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17525260573185565321615307 26287890859778347982422961)
                  ·
                    refine ⟨19715918144833760986817221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26287890859778347982422961 19715918144833760986817221)
                    ·
                      refine ⟨3696734652156330185028229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19715918144833760986817221 3696734652156330185028229)
                      ·
                        rfl

theorem cell23_7199365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_7199365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199365 prefixEnd_7199365 := by exact prefixLift 7199365
  have htrace : WordTrace (prefixWord ++ tailWord_7199365) baseStart_7199365 baseEnd_7199365 := by
    simpa [prefixWord, tailWord_7199365, baseEnd_7199365] using wordTrace_append hprefix tailTrace_7199365
  have hstable : (prefixWord ++ tailWord_7199365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199365).length < 2 ^ (prefixWord ++ tailWord_7199365).sum := by decide
  have hdescent : baseEnd_7199365 < baseStart_7199365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199385 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 3]
def baseStart_7199385 : Nat := 118140960795 + 7199385 * 2 ^ 59
def prefixEnd_7199385 : Nat := 4983230072969 + 3 ^ 40 * 7199385 * 2
def baseEnd_7199385 : Nat := 3696744921769420106778137

theorem tailTrace_7199385 : CollatzResearch.WordTrace tailWord_7199385 prefixEnd_7199385 3696744921769420106778137 := by
  unfold tailWord_7199385
  simp only [CollatzResearch.WordTrace]
  refine ⟨262583143022865176913071609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175055428681910117942047739 262583143022865176913071609)
  ·
    refine ⟨196937357267148882684803707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262583143022865176913071609 196937357267148882684803707)
    ·
      refine ⟨295406035900723324027205561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196937357267148882684803707 295406035900723324027205561)
      ·
        refine ⟨221554526925542493020404171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295406035900723324027205561 221554526925542493020404171)
        ·
          refine ⟨332331790388313739530606257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221554526925542493020404171 332331790388313739530606257)
          ·
            refine ⟨249248842791235304647954693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332331790388313739530606257 249248842791235304647954693)
            ·
              refine ⟨46734158023356619621491505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249248842791235304647954693 46734158023356619621491505)
              ·
                refine ⟨35050618517517464716118629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46734158023356619621491505 35050618517517464716118629)
                ·
                  refine ⟨6571990972034524634272243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35050618517517464716118629 6571990972034524634272243)
                  ·
                    refine ⟨9857986458051786951408365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6571990972034524634272243 9857986458051786951408365)
                    ·
                      refine ⟨3696744921769420106778137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9857986458051786951408365 3696744921769420106778137)
                      ·
                        rfl

theorem cell23_7199385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_7199385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199385 prefixEnd_7199385 := by exact prefixLift 7199385
  have htrace : WordTrace (prefixWord ++ tailWord_7199385) baseStart_7199385 baseEnd_7199385 := by
    simpa [prefixWord, tailWord_7199385, baseEnd_7199385] using wordTrace_append hprefix tailTrace_7199385
  have hstable : (prefixWord ++ tailWord_7199385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199385).length < 2 ^ (prefixWord ++ tailWord_7199385).sum := by decide
  have hdescent : baseEnd_7199385 < baseStart_7199385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199386 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7199386 : Nat := 118140960795 + 7199386 * 2 ^ 59
def prefixEnd_7199386 : Nat := 4983230072969 + 3 ^ 40 * 7199386 * 2
def baseEnd_7199386 : Nat := 3696745435250074602865633

theorem tailTrace_7199386 : CollatzResearch.WordTrace tailWord_7199386 prefixEnd_7199386 3696745435250074602865633 := by
  unfold tailWord_7199386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65645794873965388520964503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175055452997241036055905341 65645794873965388520964503)
  ·
    refine ⟨98468692310948082781446755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65645794873965388520964503 98468692310948082781446755)
    ·
      refine ⟨147703038466422124172170133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98468692310948082781446755 147703038466422124172170133)
      ·
        refine ⟨6923579928113537070570475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147703038466422124172170133 6923579928113537070570475)
        ·
          refine ⟨10385369892170305605855713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923579928113537070570475 10385369892170305605855713)
          ·
            refine ⟨7789027419127729204391785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10385369892170305605855713 7789027419127729204391785)
            ·
              refine ⟨5841770564345796903293839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7789027419127729204391785 5841770564345796903293839)
              ·
                refine ⟨8762655846518695354940759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5841770564345796903293839 8762655846518695354940759)
                ·
                  refine ⟨13143983769778043032411139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8762655846518695354940759 13143983769778043032411139)
                  ·
                    refine ⟨19715975654667064548616709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13143983769778043032411139 19715975654667064548616709)
                    ·
                      refine ⟨3696745435250074602865633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19715975654667064548616709 3696745435250074602865633)
                      ·
                        rfl

theorem cell23_7199386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7199386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199386 prefixEnd_7199386 := by exact prefixLift 7199386
  have htrace : WordTrace (prefixWord ++ tailWord_7199386) baseStart_7199386 baseEnd_7199386 := by
    simpa [prefixWord, tailWord_7199386, baseEnd_7199386] using wordTrace_append hprefix tailTrace_7199386
  have hstable : (prefixWord ++ tailWord_7199386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199386).length < 2 ^ (prefixWord ++ tailWord_7199386).sum := by decide
  have hdescent : baseEnd_7199386 < baseStart_7199386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199395 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 5, 3, 2]
def baseStart_7199395 : Nat := 118140960795 + 7199395 * 2 ^ 59
def prefixEnd_7199395 : Nat := 4983230072969 + 3 ^ 40 * 7199395 * 2
def baseEnd_7199395 : Nat := 3696750056575965067653091

theorem tailTrace_7199395 : CollatzResearch.WordTrace tailWord_7199395 prefixEnd_7199395 3696750056575965067653091 := by
  unfold tailWord_7199395
  simp only [CollatzResearch.WordTrace]
  refine ⟨262583507752828948620935639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175055671835219299080623759 262583507752828948620935639)
  ·
    refine ⟨393875261629243422931403459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262583507752828948620935639 393875261629243422931403459)
    ·
      refine ⟨590812892443865134397105189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393875261629243422931403459 590812892443865134397105189)
      ·
        refine ⟨110777417333224712699457223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590812892443865134397105189 110777417333224712699457223)
        ·
          refine ⟨166166125999837069049185835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110777417333224712699457223 166166125999837069049185835)
          ·
            refine ⟨249249188999755603573778753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166166125999837069049185835 249249188999755603573778753)
            ·
              refine ⟨186936891749816702680334065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249249188999755603573778753 186936891749816702680334065)
              ·
                refine ⟨140202668812362527010250549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186936891749816702680334065 140202668812362527010250549)
                ·
                  refine ⟨13144000201158986907210989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140202668812362527010250549 13144000201158986907210989)
                  ·
                    refine ⟨4929000075434620090204121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13144000201158986907210989 4929000075434620090204121)
                    ·
                      refine ⟨3696750056575965067653091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929000075434620090204121 3696750056575965067653091)
                      ·
                        rfl

theorem cell23_7199395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_7199395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199395 prefixEnd_7199395 := by exact prefixLift 7199395
  have htrace : WordTrace (prefixWord ++ tailWord_7199395) baseStart_7199395 baseEnd_7199395 := by
    simpa [prefixWord, tailWord_7199395, baseEnd_7199395] using wordTrace_append hprefix tailTrace_7199395
  have hstable : (prefixWord ++ tailWord_7199395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199395).length < 2 ^ (prefixWord ++ tailWord_7199395).sum := by decide
  have hdescent : baseEnd_7199395 < baseStart_7199395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199418 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_7199418 : Nat := 118140960795 + 7199418 * 2 ^ 59
def prefixEnd_7199418 : Nat := 4983230072969 + 3 ^ 40 * 7199418 * 2
def baseEnd_7199418 : Nat := 1232253955543672825888495

theorem tailTrace_7199418 : CollatzResearch.WordTrace tailWord_7199418 prefixEnd_7199418 1232253955543672825888495 := by
  unfold tailWord_7199418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65646086657936405887255727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175056231087830415699348605 65646086657936405887255727)
  ·
    refine ⟨98469129986904608830883591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65646086657936405887255727 98469129986904608830883591)
    ·
      refine ⟨147703694980356913246325387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98469129986904608830883591 147703694980356913246325387)
      ·
        refine ⟨221555542470535369869488081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147703694980356913246325387 221555542470535369869488081)
        ·
          refine ⟨166166656852901527402116061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221555542470535369869488081 166166656852901527402116061)
          ·
            refine ⟨62312496319838072775793523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166166656852901527402116061 62312496319838072775793523)
            ·
              refine ⟨93468744479757109163690285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62312496319838072775793523 93468744479757109163690285)
              ·
                refine ⟨35050779179908915936383857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93468744479757109163690285 35050779179908915936383857)
                ·
                  refine ⟨26288084384931686952287893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35050779179908915936383857 26288084384931686952287893)
                  ·
                    refine ⟨1232253955543672825888495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26288084384931686952287893 1232253955543672825888495)
                    ·
                      rfl

theorem cell23_7199418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_7199418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199418 prefixEnd_7199418 := by exact prefixLift 7199418
  have htrace : WordTrace (prefixWord ++ tailWord_7199418) baseStart_7199418 baseEnd_7199418 := by
    simpa [prefixWord, tailWord_7199418, baseEnd_7199418] using wordTrace_append hprefix tailTrace_7199418
  have hstable : (prefixWord ++ tailWord_7199418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199418).length < 2 ^ (prefixWord ++ tailWord_7199418).sum := by decide
  have hdescent : baseEnd_7199418 < baseStart_7199418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199437 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7199437 : Nat := 118140960795 + 7199437 * 2 ^ 59
def prefixEnd_7199437 : Nat := 4983230072969 + 3 ^ 40 * 7199437 * 2
def baseEnd_7199437 : Nat := 3696771622763453903327899

theorem tailTrace_7199437 : CollatzResearch.WordTrace tailWord_7199437 prefixEnd_7199437 3696771622763453903327899 := by
  unfold tailWord_7199437
  simp only [CollatzResearch.WordTrace]
  refine ⟨262585039618676789793964565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175056693079117859862643043 262585039618676789793964565)
  ·
    refine ⟨12308673732125474521592089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 262585039618676789793964565 12308673732125474521592089)
    ·
      refine ⟨9231505299094105891194067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12308673732125474521592089 9231505299094105891194067)
      ·
        refine ⟨13847257948641158836791101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9231505299094105891194067 13847257948641158836791101)
        ·
          refine ⟨5192721730740434563796663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13847257948641158836791101 5192721730740434563796663)
          ·
            refine ⟨7789082596110651845694995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192721730740434563796663 7789082596110651845694995)
            ·
              refine ⟨11683623894165977768542493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789082596110651845694995 11683623894165977768542493)
              ·
                refine ⟨4381358960312241663203435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11683623894165977768542493 4381358960312241663203435)
                ·
                  refine ⟨6572038440468362494805153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381358960312241663203435 6572038440468362494805153)
                  ·
                    refine ⟨4929028830351271871103865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6572038440468362494805153 4929028830351271871103865)
                    ·
                      refine ⟨3696771622763453903327899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929028830351271871103865 3696771622763453903327899)
                      ·
                        rfl

theorem cell23_7199437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7199437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199437 prefixEnd_7199437 := by exact prefixLift 7199437
  have htrace : WordTrace (prefixWord ++ tailWord_7199437) baseStart_7199437 baseEnd_7199437 := by
    simpa [prefixWord, tailWord_7199437, baseEnd_7199437] using wordTrace_append hprefix tailTrace_7199437
  have hstable : (prefixWord ++ tailWord_7199437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199437).length < 2 ^ (prefixWord ++ tailWord_7199437).sum := by decide
  have hdescent : baseEnd_7199437 < baseStart_7199437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199459 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7199459 : Nat := 118140960795 + 7199459 * 2 ^ 59
def prefixEnd_7199459 : Nat := 4983230072969 + 3 ^ 40 * 7199459 * 2
def baseEnd_7199459 : Nat := 3696782919337852817252797

theorem tailTrace_7199459 : CollatzResearch.WordTrace tailWord_7199459 prefixEnd_7199459 3696782919337852817252797 := by
  unfold tailWord_7199459
  simp only [CollatzResearch.WordTrace]
  refine ⟨262585842024597087551265431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175057228016398058367510287 262585842024597087551265431)
  ·
    refine ⟨393878763036895631326898147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262585842024597087551265431 393878763036895631326898147)
    ·
      refine ⟨590818144555343446990347221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393878763036895631326898147 590818144555343446990347221)
      ·
        refine ⟨13847300263015862038836263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 590818144555343446990347221 13847300263015862038836263)
        ·
          refine ⟨20770950394523793058254395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13847300263015862038836263 20770950394523793058254395)
          ·
            refine ⟨31156425591785689587381593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20770950394523793058254395 31156425591785689587381593)
            ·
              refine ⟨23367319193839267190536195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31156425591785689587381593 23367319193839267190536195)
              ·
                refine ⟨35050978790758900785804293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23367319193839267190536195 35050978790758900785804293)
                ·
                  refine ⟨6572058523267293897338305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35050978790758900785804293 6572058523267293897338305)
                  ·
                    refine ⟨4929043892450470423003729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6572058523267293897338305 4929043892450470423003729)
                    ·
                      refine ⟨3696782919337852817252797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929043892450470423003729 3696782919337852817252797)
                      ·
                        rfl

theorem cell23_7199459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7199459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199459 prefixEnd_7199459 := by exact prefixLift 7199459
  have htrace : WordTrace (prefixWord ++ tailWord_7199459) baseStart_7199459 baseEnd_7199459 := by
    simpa [prefixWord, tailWord_7199459, baseEnd_7199459] using wordTrace_append hprefix tailTrace_7199459
  have hstable : (prefixWord ++ tailWord_7199459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199459).length < 2 ^ (prefixWord ++ tailWord_7199459).sum := by decide
  have hdescent : baseEnd_7199459 < baseStart_7199459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199465 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 5]
def baseStart_7199465 : Nat := 118140960795 + 7199465 * 2 ^ 59
def prefixEnd_7199465 : Nat := 4983230072969 + 3 ^ 40 * 7199465 * 2
def baseEnd_7199465 : Nat := 410754000024642199308641

theorem tailTrace_7199465 : CollatzResearch.WordTrace tailWord_7199465 prefixEnd_7199465 410754000024642199308641 := by
  unfold tailWord_7199465
  simp only [CollatzResearch.WordTrace]
  refine ⟨262586060862575350575983849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175057373908383567050655899 262586060862575350575983849)
  ·
    refine ⟨196939545646931512931987887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262586060862575350575983849 196939545646931512931987887)
    ·
      refine ⟨295409318470397269397981831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196939545646931512931987887 295409318470397269397981831)
      ·
        refine ⟨443113977705595904096972747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295409318470397269397981831 443113977705595904096972747)
        ·
          refine ⟨664670966558393856145459121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443113977705595904096972747 664670966558393856145459121)
          ·
            refine ⟨498503224918795392109094341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664670966558393856145459121 498503224918795392109094341)
            ·
              refine ⟨93469354672274136020455189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498503224918795392109094341 93469354672274136020455189)
              ·
                refine ⟨4381376000262850125958837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93469354672274136020455189 4381376000262850125958837)
                ·
                  refine ⟨410754000024642199308641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4381376000262850125958837 410754000024642199308641)
                  ·
                    rfl

theorem cell23_7199465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 5].length) (baseStart_7199465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199465 prefixEnd_7199465 := by exact prefixLift 7199465
  have htrace : WordTrace (prefixWord ++ tailWord_7199465) baseStart_7199465 baseEnd_7199465 := by
    simpa [prefixWord, tailWord_7199465, baseEnd_7199465] using wordTrace_append hprefix tailTrace_7199465
  have hstable : (prefixWord ++ tailWord_7199465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199465).length < 2 ^ (prefixWord ++ tailWord_7199465).sum := by decide
  have hdescent : baseEnd_7199465 < baseStart_7199465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199488 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_7199488 : Nat := 118140960795 + 7199488 * 2 ^ 59
def prefixEnd_7199488 : Nat := 4983230072969 + 3 ^ 40 * 7199488 * 2
def baseEnd_7199488 : Nat := 3696797810276833203790163

theorem tailTrace_7199488 : CollatzResearch.WordTrace tailWord_7199488 prefixEnd_7199488 3696797810276833203790163 := by
  unfold tailWord_7199488
  simp only [CollatzResearch.WordTrace]
  refine ⟨131293449870746012752035559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175057933160994683669380745 131293449870746012752035559)
  ·
    refine ⟨196940174806119019128053339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131293449870746012752035559 196940174806119019128053339)
    ·
      refine ⟨295410262209178528692080009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196940174806119019128053339 295410262209178528692080009)
      ·
        refine ⟨221557696656883896519060007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295410262209178528692080009 221557696656883896519060007)
        ·
          refine ⟨332336544985325844778590011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221557696656883896519060007 332336544985325844778590011)
          ·
            refine ⟨498504817477988767167885017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332336544985325844778590011 498504817477988767167885017)
            ·
              refine ⟨373878613108491575375913763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498504817477988767167885017 373878613108491575375913763)
              ·
                refine ⟨560817919662737363063870645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373878613108491575375913763 560817919662737363063870645)
                ·
                  refine ⟨52576679968381627787237873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560817919662737363063870645 52576679968381627787237873)
                  ·
                    refine ⟨39432509976286220840428405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52576679968381627787237873 39432509976286220840428405)
                    ·
                      refine ⟨3696797810276833203790163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39432509976286220840428405 3696797810276833203790163)
                      ·
                        rfl

theorem cell23_7199488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_7199488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199488 prefixEnd_7199488 := by exact prefixLift 7199488
  have htrace : WordTrace (prefixWord ++ tailWord_7199488) baseStart_7199488 baseEnd_7199488 := by
    simpa [prefixWord, tailWord_7199488, baseEnd_7199488] using wordTrace_append hprefix tailTrace_7199488
  have hstable : (prefixWord ++ tailWord_7199488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199488).length < 2 ^ (prefixWord ++ tailWord_7199488).sum := by decide
  have hdescent : baseEnd_7199488 < baseStart_7199488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199532 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_7199532 : Nat := 118140960795 + 7199532 * 2 ^ 59
def prefixEnd_7199532 : Nat := 4983230072969 + 3 ^ 40 * 7199532 * 2
def baseEnd_7199532 : Nat := 3696820403425631031639961

theorem tailTrace_7199532 : CollatzResearch.WordTrace tailWord_7199532 prefixEnd_7199532 3696820403425631031639961 := by
  unfold tailWord_7199532
  simp only [CollatzResearch.WordTrace]
  refine ⟨131294252276666310509336425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175059003035555080679115233 131294252276666310509336425)
  ·
    refine ⟨98470689207499732882002319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131294252276666310509336425 98470689207499732882002319)
    ·
      refine ⟨147706033811249599323003479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98470689207499732882002319 147706033811249599323003479)
      ·
        refine ⟨221559050716874398984505219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147706033811249599323003479 221559050716874398984505219)
        ·
          refine ⟨332338576075311598476757829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221559050716874398984505219 332338576075311598476757829)
          ·
            refine ⟨62313483014120924714392093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332338576075311598476757829 62313483014120924714392093)
            ·
              refine ⟨23367556130295346767897035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62313483014120924714392093 23367556130295346767897035)
              ·
                refine ⟨35051334195443020151845553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23367556130295346767897035 35051334195443020151845553)
                ·
                  refine ⟨26288500646582265113884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35051334195443020151845553 26288500646582265113884165)
                  ·
                    refine ⟨4929093871234174708853281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26288500646582265113884165 4929093871234174708853281)
                    ·
                      refine ⟨3696820403425631031639961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929093871234174708853281 3696820403425631031639961)
                      ·
                        rfl

theorem cell23_7199532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_7199532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199532 prefixEnd_7199532 := by exact prefixLift 7199532
  have htrace : WordTrace (prefixWord ++ tailWord_7199532) baseStart_7199532 baseEnd_7199532 := by
    simpa [prefixWord, tailWord_7199532, baseEnd_7199532] using wordTrace_append hprefix tailTrace_7199532
  have hstable : (prefixWord ++ tailWord_7199532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199532).length < 2 ^ (prefixWord ++ tailWord_7199532).sum := by decide
  have hdescent : baseEnd_7199532 < baseStart_7199532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199572 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 8]
def baseStart_7199572 : Nat := 118140960795 + 7199572 * 2 ^ 59
def prefixEnd_7199572 : Nat := 4983230072969 + 3 ^ 40 * 7199572 * 2
def baseEnd_7199572 : Nat := 410760104739090097237753

theorem tailTrace_7199572 : CollatzResearch.WordTrace tailWord_7199572 prefixEnd_7199572 410760104739090097237753 := by
  unfold tailWord_7199572
  simp only [CollatzResearch.WordTrace]
  refine ⟨131294981736593853925064485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175059975648791805233419313 131294981736593853925064485)
  ·
    refine ⟨24617809075611347610949591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131294981736593853925064485 24617809075611347610949591)
    ·
      refine ⟨36926713613417021416424387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24617809075611347610949591 36926713613417021416424387)
      ·
        refine ⟨55390070420125532124636581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36926713613417021416424387 55390070420125532124636581)
        ·
          refine ⟨10385638203773537273369359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55390070420125532124636581 10385638203773537273369359)
          ·
            refine ⟨15578457305660305910054039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10385638203773537273369359 15578457305660305910054039)
            ·
              refine ⟨23367685958490458865081059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15578457305660305910054039 23367685958490458865081059)
              ·
                refine ⟨35051528937735688297621589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23367685958490458865081059 35051528937735688297621589)
                ·
                  refine ⟨410760104739090097237753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35051528937735688297621589 410760104739090097237753)
                  ·
                    rfl

theorem cell23_7199572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_7199572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199572 prefixEnd_7199572 := by exact prefixLift 7199572
  have htrace : WordTrace (prefixWord ++ tailWord_7199572) baseStart_7199572 baseEnd_7199572 := by
    simpa [prefixWord, tailWord_7199572, baseEnd_7199572] using wordTrace_append hprefix tailTrace_7199572
  have hstable : (prefixWord ++ tailWord_7199572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199572).length < 2 ^ (prefixWord ++ tailWord_7199572).sum := by decide
  have hdescent : baseEnd_7199572 < baseStart_7199572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199575 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_7199575 : Nat := 118140960795 + 7199575 * 2 ^ 59
def prefixEnd_7199575 : Nat := 4983230072969 + 3 ^ 40 * 7199575 * 2
def baseEnd_7199575 : Nat := 3696842483093774363402263

theorem tailTrace_7199575 : CollatzResearch.WordTrace tailWord_7199575 prefixEnd_7199575 3696842483093774363402263 := by
  unfold tailWord_7199575
  simp only [CollatzResearch.WordTrace]
  refine ⟨262590072892176839362488179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175060048594784559574992119 262590072892176839362488179)
  ·
    refine ⟨393885109338265259043732269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262590072892176839362488179 393885109338265259043732269)
    ·
      refine ⟨147706916001849472141399601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393885109338265259043732269 147706916001849472141399601)
      ·
        refine ⟨110780187001387104106049701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147706916001849472141399601 110780187001387104106049701)
        ·
          refine ⟨20771285062760082019884319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110780187001387104106049701 20771285062760082019884319)
          ·
            refine ⟨31156927594140123029826479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20771285062760082019884319 31156927594140123029826479)
            ·
              refine ⟨46735391391210184544739719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31156927594140123029826479 46735391391210184544739719)
              ·
                refine ⟨70103087086815276817109579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46735391391210184544739719 70103087086815276817109579)
                ·
                  refine ⟨105154630630222915225664369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70103087086815276817109579 105154630630222915225664369)
                  ·
                    refine ⟨78865972972667186419248277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105154630630222915225664369 78865972972667186419248277)
                    ·
                      refine ⟨3696842483093774363402263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78865972972667186419248277 3696842483093774363402263)
                      ·
                        rfl

theorem cell23_7199575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_7199575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199575 prefixEnd_7199575 := by exact prefixLift 7199575
  have htrace : WordTrace (prefixWord ++ tailWord_7199575) baseStart_7199575 baseEnd_7199575 := by
    simpa [prefixWord, tailWord_7199575, baseEnd_7199575] using wordTrace_append hprefix tailTrace_7199575
  have hstable : (prefixWord ++ tailWord_7199575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199575).length < 2 ^ (prefixWord ++ tailWord_7199575).sum := by decide
  have hdescent : baseEnd_7199575 < baseStart_7199575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199585 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_7199585 : Nat := 118140960795 + 7199585 * 2 ^ 59
def prefixEnd_7199585 : Nat := 4983230072969 + 3 ^ 40 * 7199585 * 2
def baseEnd_7199585 : Nat := 1232282539300106441425739

theorem tailTrace_7199585 : CollatzResearch.WordTrace tailWord_7199585 prefixEnd_7199585 1232282539300106441425739 := by
  unfold tailWord_7199585
  simp only [CollatzResearch.WordTrace]
  refine ⟨262590437622140611070352209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175060291748093740713568139 262590437622140611070352209)
  ·
    refine ⟨196942828216605458302764157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262590437622140611070352209 196942828216605458302764157)
    ·
      refine ⟨73853560581227046863536559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196942828216605458302764157 73853560581227046863536559)
      ·
        refine ⟨110780340871840570295304839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73853560581227046863536559 110780340871840570295304839)
        ·
          refine ⟨166170511307760855442957259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110780340871840570295304839 166170511307760855442957259)
          ·
            refine ⟨249255766961641283164435889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166170511307760855442957259 249255766961641283164435889)
            ·
              refine ⟨186941825221230962373326917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249255766961641283164435889 186941825221230962373326917)
              ·
                refine ⟨35051592228980805444998797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186941825221230962373326917 35051592228980805444998797)
                ·
                  refine ⟨13144347085867802041874549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35051592228980805444998797 13144347085867802041874549)
                  ·
                    refine ⟨1232282539300106441425739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13144347085867802041874549 1232282539300106441425739)
                    ·
                      rfl

theorem cell23_7199585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_7199585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199585 prefixEnd_7199585 := by exact prefixLift 7199585
  have htrace : WordTrace (prefixWord ++ tailWord_7199585) baseStart_7199585 baseEnd_7199585 := by
    simpa [prefixWord, tailWord_7199585, baseEnd_7199585] using wordTrace_append hprefix tailTrace_7199585
  have hstable : (prefixWord ++ tailWord_7199585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199585).length < 2 ^ (prefixWord ++ tailWord_7199585).sum := by decide
  have hdescent : baseEnd_7199585 < baseStart_7199585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199602 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_7199602 : Nat := 118140960795 + 7199602 * 2 ^ 59
def prefixEnd_7199602 : Nat := 4983230072969 + 3 ^ 40 * 7199602 * 2
def baseEnd_7199602 : Nat := 1232285449023815252588213

theorem tailTrace_7199602 : CollatzResearch.WordTrace tailWord_7199602 prefixEnd_7199602 1232285449023815252588213 := by
  unfold tailWord_7199602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65647764415769755743430265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175060705108719348649147373 65647764415769755743430265)
  ·
    refine ⟨49235823311827316807572699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65647764415769755743430265 49235823311827316807572699)
    ·
      refine ⟨73853734967740975211359049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49235823311827316807572699 73853734967740975211359049)
      ·
        refine ⟨55390301225805731408519287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73853734967740975211359049 55390301225805731408519287)
        ·
          refine ⟨83085451838708597112778931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55390301225805731408519287 83085451838708597112778931)
          ·
            refine ⟨124628177758062895669168397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83085451838708597112778931 124628177758062895669168397)
            ·
              refine ⟨46735566659273585875938149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124628177758062895669168397 46735566659273585875938149)
              ·
                refine ⟨8762918748613797351738403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46735566659273585875938149 8762918748613797351738403)
                ·
                  refine ⟨13144378122920696027607605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8762918748613797351738403 13144378122920696027607605)
                  ·
                    refine ⟨1232285449023815252588213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13144378122920696027607605 1232285449023815252588213)
                    ·
                      rfl

theorem cell23_7199602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_7199602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199602 prefixEnd_7199602 := by exact prefixLift 7199602
  have htrace : WordTrace (prefixWord ++ tailWord_7199602) baseStart_7199602 baseEnd_7199602 := by
    simpa [prefixWord, tailWord_7199602, baseEnd_7199602] using wordTrace_append hprefix tailTrace_7199602
  have hstable : (prefixWord ++ tailWord_7199602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199602).length < 2 ^ (prefixWord ++ tailWord_7199602).sum := by decide
  have hdescent : baseEnd_7199602 < baseStart_7199602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199615 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 1, 6]
def baseStart_7199615 : Nat := 118140960795 + 7199615 * 2 ^ 59
def prefixEnd_7199615 : Nat := 4983230072969 + 3 ^ 40 * 7199615 * 2
def baseEnd_7199615 : Nat := 1232287674106651402300693

theorem tailTrace_7199615 : CollatzResearch.WordTrace tailWord_7199615 prefixEnd_7199615 1232287674106651402300693 := by
  unfold tailWord_7199615
  simp only [CollatzResearch.WordTrace]
  refine ⟨262591531812031926193944299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175061021208021284129296199 262591531812031926193944299)
  ·
    refine ⟨393887297718047889290916449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262591531812031926193944299 393887297718047889290916449)
    ·
      refine ⟨295415473288535916968187337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393887297718047889290916449 295415473288535916968187337)
      ·
        refine ⟨221561604966401937726140503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295415473288535916968187337 221561604966401937726140503)
        ·
          refine ⟨332342407449602906589210755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221561604966401937726140503 332342407449602906589210755)
          ·
            refine ⟨498513611174404359883816133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332342407449602906589210755 498513611174404359883816133)
            ·
              refine ⟨93471302095200817478215525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498513611174404359883816133 93471302095200817478215525)
              ·
                refine ⟨17525869142850153277165411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93471302095200817478215525 17525869142850153277165411)
                ·
                  refine ⟨26288803714275229915748117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17525869142850153277165411 26288803714275229915748117)
                  ·
                    refine ⟨1232287674106651402300693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26288803714275229915748117 1232287674106651402300693)
                    ·
                      rfl

theorem cell23_7199615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_7199615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199615 prefixEnd_7199615 := by exact prefixLift 7199615
  have htrace : WordTrace (prefixWord ++ tailWord_7199615) baseStart_7199615 baseEnd_7199615 := by
    simpa [prefixWord, tailWord_7199615, baseEnd_7199615] using wordTrace_append hprefix tailTrace_7199615
  have hstable : (prefixWord ++ tailWord_7199615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199615).length < 2 ^ (prefixWord ++ tailWord_7199615).sum := by decide
  have hdescent : baseEnd_7199615 < baseStart_7199615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199626 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7199626 : Nat := 118140960795 + 7199626 * 2 ^ 59
def prefixEnd_7199626 : Nat := 4983230072969 + 3 ^ 40 * 7199626 * 2
def baseEnd_7199626 : Nat := 3696868670607153663864529

theorem tailTrace_7199626 : CollatzResearch.WordTrace tailWord_7199626 prefixEnd_7199626 3696868670607153663864529 := by
  unfold tailWord_7199626
  simp only [CollatzResearch.WordTrace]
  refine ⟨65647983253748018768148683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175061288676661383381729821 65647983253748018768148683)
  ·
    refine ⟨98471974880622028152223025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65647983253748018768148683 98471974880622028152223025)
    ·
      refine ⟨73853981160466521114167269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98471974880622028152223025 73853981160466521114167269)
      ·
        refine ⟨13847621467587472708906363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73853981160466521114167269 13847621467587472708906363)
        ·
          refine ⟨20771432201381209063359545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13847621467587472708906363 20771432201381209063359545)
          ·
            refine ⟨15578574151035906797519659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20771432201381209063359545 15578574151035906797519659)
            ·
              refine ⟨23367861226553860196279489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15578574151035906797519659 23367861226553860196279489)
              ·
                refine ⟨17525895919915395147209617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23367861226553860196279489 17525895919915395147209617)
                ·
                  refine ⟨13144421939936546360407213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17525895919915395147209617 13144421939936546360407213)
                  ·
                    refine ⟨4929158227476204885152705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13144421939936546360407213 4929158227476204885152705)
                    ·
                      refine ⟨3696868670607153663864529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929158227476204885152705 3696868670607153663864529)
                      ·
                        rfl

theorem cell23_7199626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7199626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199626 prefixEnd_7199626 := by exact prefixLift 7199626
  have htrace : WordTrace (prefixWord ++ tailWord_7199626) baseStart_7199626 baseEnd_7199626 := by
    simpa [prefixWord, tailWord_7199626, baseEnd_7199626] using wordTrace_append hprefix tailTrace_7199626
  have hstable : (prefixWord ++ tailWord_7199626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199626).length < 2 ^ (prefixWord ++ tailWord_7199626).sum := by decide
  have hdescent : baseEnd_7199626 < baseStart_7199626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199635 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_7199635 : Nat := 118140960795 + 7199635 * 2 ^ 59
def prefixEnd_7199635 : Nat := 4983230072969 + 3 ^ 40 * 7199635 * 2
def baseEnd_7199635 : Nat := 3696873291933044128651987

theorem tailTrace_7199635 : CollatzResearch.WordTrace tailWord_7199635 prefixEnd_7199635 3696873291933044128651987 := by
  unfold tailWord_7199635
  simp only [CollatzResearch.WordTrace]
  refine ⟨262592261271959469609672359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175061507514639646406448239 262592261271959469609672359)
  ·
    refine ⟨393888391907939204414508539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262592261271959469609672359 393888391907939204414508539)
    ·
      refine ⟨590832587861908806621762809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393888391907939204414508539 590832587861908806621762809)
      ·
        refine ⟨443124440896431604966322107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590832587861908806621762809 443124440896431604966322107)
        ·
          refine ⟨664686661344647407449483161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443124440896431604966322107 664686661344647407449483161)
          ·
            refine ⟨498514996008485555587112371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664686661344647407449483161 498514996008485555587112371)
            ·
              refine ⟨747772494012728333380668557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498514996008485555587112371 747772494012728333380668557)
              ·
                refine ⟨280414685254773125017750709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 747772494012728333380668557 280414685254773125017750709)
                ·
                  refine ⟨26288876742634980470414129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280414685254773125017750709 26288876742634980470414129)
                  ·
                    refine ⟨19716657556976235352810597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26288876742634980470414129 19716657556976235352810597)
                    ·
                      refine ⟨3696873291933044128651987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19716657556976235352810597 3696873291933044128651987)
                      ·
                        rfl

theorem cell23_7199635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_7199635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199635 prefixEnd_7199635 := by exact prefixLift 7199635
  have htrace : WordTrace (prefixWord ++ tailWord_7199635) baseStart_7199635 baseEnd_7199635 := by
    simpa [prefixWord, tailWord_7199635, baseEnd_7199635] using wordTrace_append hprefix tailTrace_7199635
  have hstable : (prefixWord ++ tailWord_7199635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199635).length < 2 ^ (prefixWord ++ tailWord_7199635).sum := by decide
  have hdescent : baseEnd_7199635 < baseStart_7199635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199652 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7199652 : Nat := 118140960795 + 7199652 * 2 ^ 59
def prefixEnd_7199652 : Nat := 4983230072969 + 3 ^ 40 * 7199652 * 2
def baseEnd_7199652 : Nat := 3696882021104170562139409

theorem tailTrace_7199652 : CollatzResearch.WordTrace tailWord_7199652 prefixEnd_7199652 3696882021104170562139409 := by
  unfold tailWord_7199652
  simp only [CollatzResearch.WordTrace]
  refine ⟨131296440656448940756520605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175061920875265254342027473 131296440656448940756520605)
  ·
    refine ⟨49236165246168352783695227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131296440656448940756520605 49236165246168352783695227)
    ·
      refine ⟨73854247869252529175542841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49236165246168352783695227 73854247869252529175542841)
      ·
        refine ⟨55390685901939396881657131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73854247869252529175542841 55390685901939396881657131)
        ·
          refine ⟨83086028852909095322485697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55390685901939396881657131 83086028852909095322485697)
          ·
            refine ⟨62314521639681821491864273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83086028852909095322485697 62314521639681821491864273)
            ·
              refine ⟨46735891229761366118898205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62314521639681821491864273 46735891229761366118898205)
              ·
                refine ⟨17525959211160512294586827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46735891229761366118898205 17525959211160512294586827)
                ·
                  refine ⟨26288938816740768441880241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17525959211160512294586827 26288938816740768441880241)
                  ·
                    refine ⟨19716704112555576331410181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26288938816740768441880241 19716704112555576331410181)
                    ·
                      refine ⟨3696882021104170562139409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19716704112555576331410181 3696882021104170562139409)
                      ·
                        rfl

theorem cell23_7199652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7199652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199652 prefixEnd_7199652 := by exact prefixLift 7199652
  have htrace : WordTrace (prefixWord ++ tailWord_7199652) baseStart_7199652 baseEnd_7199652 := by
    simpa [prefixWord, tailWord_7199652, baseEnd_7199652] using wordTrace_append hprefix tailTrace_7199652
  have hstable : (prefixWord ++ tailWord_7199652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199652).length < 2 ^ (prefixWord ++ tailWord_7199652).sum := by decide
  have hdescent : baseEnd_7199652 < baseStart_7199652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199672 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_7199672 : Nat := 118140960795 + 7199672 * 2 ^ 59
def prefixEnd_7199672 : Nat := 4983230072969 + 3 ^ 40 * 7199672 * 2
def baseEnd_7199672 : Nat := 3696892290717260483889317

theorem tailTrace_7199672 : CollatzResearch.WordTrace tailWord_7199672 prefixEnd_7199672 3696892290717260483889317 := by
  unfold tailWord_7199672
  simp only [CollatzResearch.WordTrace]
  refine ⟨131296805386412712464384635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175062407181883616619179513 131296805386412712464384635)
  ·
    refine ⟨196945208079619068696576953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131296805386412712464384635 196945208079619068696576953)
    ·
      refine ⟨147708906059714301522432715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196945208079619068696576953 147708906059714301522432715)
      ·
        refine ⟨221563359089571452283649073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147708906059714301522432715 221563359089571452283649073)
        ·
          refine ⟨166172519317178589212736805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221563359089571452283649073 166172519317178589212736805)
          ·
            refine ⟨31157347371970985477388151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166172519317178589212736805 31157347371970985477388151)
            ·
              refine ⟨46736021057956478216082227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31157347371970985477388151 46736021057956478216082227)
              ·
                refine ⟨70104031586934717324123341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46736021057956478216082227 70104031586934717324123341)
                ·
                  refine ⟨26289011845100518996546253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70104031586934717324123341 26289011845100518996546253)
                  ·
                    refine ⟨9858379441912694623704845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26289011845100518996546253 9858379441912694623704845)
                    ·
                      refine ⟨3696892290717260483889317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9858379441912694623704845 3696892290717260483889317)
                      ·
                        rfl

theorem cell23_7199672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_7199672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199672 prefixEnd_7199672 := by exact prefixLift 7199672
  have htrace : WordTrace (prefixWord ++ tailWord_7199672) baseStart_7199672 baseEnd_7199672 := by
    simpa [prefixWord, tailWord_7199672, baseEnd_7199672] using wordTrace_append hprefix tailTrace_7199672
  have hstable : (prefixWord ++ tailWord_7199672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199672).length < 2 ^ (prefixWord ++ tailWord_7199672).sum := by decide
  have hdescent : baseEnd_7199672 < baseStart_7199672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199684 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7199684 : Nat := 118140960795 + 7199684 * 2 ^ 59
def prefixEnd_7199684 : Nat := 4983230072969 + 3 ^ 40 * 7199684 * 2
def baseEnd_7199684 : Nat := 3696898452485114436939263

theorem tailTrace_7199684 : CollatzResearch.WordTrace tailWord_7199684 prefixEnd_7199684 3696898452485114436939263 := by
  unfold tailWord_7199684
  simp only [CollatzResearch.WordTrace]
  refine ⟨131297024224390975489103053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175062698965854633985470737 131297024224390975489103053)
  ·
    refine ⟨49236384084146615808413645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131297024224390975489103053 49236384084146615808413645)
    ·
      refine ⟨18463644031554980928155117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49236384084146615808413645 18463644031554980928155117)
      ·
        refine ⟨6923866511833117848058169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18463644031554980928155117 6923866511833117848058169)
        ·
          refine ⟨5192899883874838386043627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6923866511833117848058169 5192899883874838386043627)
          ·
            refine ⟨7789349825812257579065441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192899883874838386043627 7789349825812257579065441)
            ·
              refine ⟨5842012369359193184299081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7789349825812257579065441 5842012369359193184299081)
              ·
                refine ⟨4381509277019394888224311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5842012369359193184299081 4381509277019394888224311)
                ·
                  refine ⟨6572263915529092332336467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381509277019394888224311 6572263915529092332336467)
                  ·
                    refine ⟨9858395873293638498504701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6572263915529092332336467 9858395873293638498504701)
                    ·
                      refine ⟨3696898452485114436939263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9858395873293638498504701 3696898452485114436939263)
                      ·
                        rfl

theorem cell23_7199684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7199684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199684 prefixEnd_7199684 := by exact prefixLift 7199684
  have htrace : WordTrace (prefixWord ++ tailWord_7199684) baseStart_7199684 baseEnd_7199684 := by
    simpa [prefixWord, tailWord_7199684, baseEnd_7199684] using wordTrace_append hprefix tailTrace_7199684
  have hstable : (prefixWord ++ tailWord_7199684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199684).length < 2 ^ (prefixWord ++ tailWord_7199684).sum := by decide
  have hdescent : baseEnd_7199684 < baseStart_7199684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199685 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_7199685 : Nat := 118140960795 + 7199685 * 2 ^ 59
def prefixEnd_7199685 : Nat := 4983230072969 + 3 ^ 40 * 7199685 * 2
def baseEnd_7199685 : Nat := 3696898965965768933026757

theorem tailTrace_7199685 : CollatzResearch.WordTrace tailWord_7199685 prefixEnd_7199685 3696898965965768933026757 := by
  unfold tailWord_7199685
  simp only [CollatzResearch.WordTrace]
  refine ⟨262594084921778328148992509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175062723281185552099328339 262594084921778328148992509)
  ·
    refine ⟨98472781845666873055872191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262594084921778328148992509 98472781845666873055872191)
    ·
      refine ⟨147709172768500309583808287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98472781845666873055872191 147709172768500309583808287)
      ·
        refine ⟨221563759152750464375712431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147709172768500309583808287 221563759152750464375712431)
        ·
          refine ⟨332345638729125696563568647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221563759152750464375712431 332345638729125696563568647)
          ·
            refine ⟨498518458093688544845352971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332345638729125696563568647 498518458093688544845352971)
            ·
              refine ⟨747777687140532817268029457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498518458093688544845352971 747777687140532817268029457)
              ·
                refine ⟨560833265355399612951022093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747777687140532817268029457 560833265355399612951022093)
                ·
                  refine ⟨210312474508274854856633285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560833265355399612951022093 210312474508274854856633285)
                  ·
                    refine ⟨39433588970301535285618741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210312474508274854856633285 39433588970301535285618741)
                    ·
                      refine ⟨3696898965965768933026757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39433588970301535285618741 3696898965965768933026757)
                      ·
                        rfl

theorem cell23_7199685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_7199685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199685 prefixEnd_7199685 := by exact prefixLift 7199685
  have htrace : WordTrace (prefixWord ++ tailWord_7199685) baseStart_7199685 baseEnd_7199685 := by
    simpa [prefixWord, tailWord_7199685, baseEnd_7199685] using wordTrace_append hprefix tailTrace_7199685
  have hstable : (prefixWord ++ tailWord_7199685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199685).length < 2 ^ (prefixWord ++ tailWord_7199685).sum := by decide
  have hdescent : baseEnd_7199685 < baseStart_7199685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199706 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_7199706 : Nat := 118140960795 + 7199706 * 2 ^ 59
def prefixEnd_7199706 : Nat := 4983230072969 + 3 ^ 40 * 7199706 * 2
def baseEnd_7199706 : Nat := 3696909749059513350864161

theorem tailTrace_7199706 : CollatzResearch.WordTrace tailWord_7199706 prefixEnd_7199706 3696909749059513350864161 := by
  unfold tailWord_7199706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65648712713675562183876743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175063233903134832490337981 65648712713675562183876743)
  ·
    refine ⟨98473069070513343275815115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65648712713675562183876743 98473069070513343275815115)
    ·
      refine ⟨147709603605770014913722673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98473069070513343275815115 147709603605770014913722673)
      ·
        refine ⟨110782202704327511185292005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147709603605770014913722673 110782202704327511185292005)
        ·
          refine ⟨20771663007061408347242251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110782202704327511185292005 20771663007061408347242251)
          ·
            refine ⟨31157494510592112520863377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20771663007061408347242251 31157494510592112520863377)
            ·
              refine ⟨23368120882944084390647533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31157494510592112520863377 23368120882944084390647533)
              ·
                refine ⟨8763045331104031646492825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23368120882944084390647533 8763045331104031646492825)
                ·
                  refine ⟨6572283998328023734869619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8763045331104031646492825 6572283998328023734869619)
                  ·
                    refine ⟨9858425997492035602304429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6572283998328023734869619 9858425997492035602304429)
                    ·
                      refine ⟨3696909749059513350864161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9858425997492035602304429 3696909749059513350864161)
                      ·
                        rfl

theorem cell23_7199706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_7199706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199706 prefixEnd_7199706 := by exact prefixLift 7199706
  have htrace : WordTrace (prefixWord ++ tailWord_7199706) baseStart_7199706 baseEnd_7199706 := by
    simpa [prefixWord, tailWord_7199706, baseEnd_7199706] using wordTrace_append hprefix tailTrace_7199706
  have hstable : (prefixWord ++ tailWord_7199706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199706).length < 2 ^ (prefixWord ++ tailWord_7199706).sum := by decide
  have hdescent : baseEnd_7199706 < baseStart_7199706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199752 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 7]
def baseStart_7199752 : Nat := 118140960795 + 7199752 * 2 ^ 59
def prefixEnd_7199752 : Nat := 4983230072969 + 3 ^ 40 * 7199752 * 2
def baseEnd_7199752 : Nat := 410770374352180018987661

theorem tailTrace_7199752 : CollatzResearch.WordTrace tailWord_7199752 prefixEnd_7199752 410770374352180018987661 := by
  unfold tailWord_7199752
  simp only [CollatzResearch.WordTrace]
  refine ⟨131298264306267799295840755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175064352408357065727787673 131298264306267799295840755)
  ·
    refine ⟨196947396459401698943761133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131298264306267799295840755 196947396459401698943761133)
    ·
      refine ⟨73855273672275637103910425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196947396459401698943761133 73855273672275637103910425)
      ·
        refine ⟨55391455254206727827932819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73855273672275637103910425 55391455254206727827932819)
        ·
          refine ⟨83087182881310091741899229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55391455254206727827932819 83087182881310091741899229)
          ·
            refine ⟨31157693580491284403212211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83087182881310091741899229 31157693580491284403212211)
            ·
              refine ⟨46736540370736926604818317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31157693580491284403212211 46736540370736926604818317)
              ·
                refine ⟨17526202639026347476806869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46736540370736926604818317 17526202639026347476806869)
                ·
                  refine ⟨410770374352180018987661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17526202639026347476806869 410770374352180018987661)
                  ·
                    rfl

theorem cell23_7199752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_7199752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199752 prefixEnd_7199752 := by exact prefixLift 7199752
  have htrace : WordTrace (prefixWord ++ tailWord_7199752) baseStart_7199752 baseEnd_7199752 := by
    simpa [prefixWord, tailWord_7199752, baseEnd_7199752] using wordTrace_append hprefix tailTrace_7199752
  have hstable : (prefixWord ++ tailWord_7199752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199752).length < 2 ^ (prefixWord ++ tailWord_7199752).sum := by decide
  have hdescent : baseEnd_7199752 < baseStart_7199752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199792 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_7199792 : Nat := 118140960795 + 7199792 * 2 ^ 59
def prefixEnd_7199792 : Nat := 4983230072969 + 3 ^ 40 * 7199792 * 2
def baseEnd_7199792 : Nat := 3696953908395800014388765

theorem tailTrace_7199792 : CollatzResearch.WordTrace tailWord_7199792 prefixEnd_7199792 3696953908395800014388765 := by
  unfold tailWord_7199792
  simp only [CollatzResearch.WordTrace]
  refine ⟨131298993766195342711568815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175065325021593790282091753 131298993766195342711568815)
  ·
    refine ⟨196948490649293014067353223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131298993766195342711568815 196948490649293014067353223)
    ·
      refine ⟨295422735973939521101029835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196948490649293014067353223 295422735973939521101029835)
      ·
        refine ⟨443134103960909281651544753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295422735973939521101029835 443134103960909281651544753)
        ·
          refine ⟨332350577970681961238658565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443134103960909281651544753 332350577970681961238658565)
          ·
            refine ⟨62315733369502867732248481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332350577970681961238658565 62315733369502867732248481)
            ·
              refine ⟨46736800027127150799186361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62315733369502867732248481 46736800027127150799186361)
              ·
                refine ⟨35052600020345363099389771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46736800027127150799186361 35052600020345363099389771)
                ·
                  refine ⟨52578900030518044649084657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35052600020345363099389771 52578900030518044649084657)
                  ·
                    refine ⟨39434175022888533486813493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52578900030518044649084657 39434175022888533486813493)
                    ·
                      refine ⟨3696953908395800014388765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39434175022888533486813493 3696953908395800014388765)
                      ·
                        rfl

theorem cell23_7199792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_7199792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199792 prefixEnd_7199792 := by exact prefixLift 7199792
  have htrace : WordTrace (prefixWord ++ tailWord_7199792) baseStart_7199792 baseEnd_7199792 := by
    simpa [prefixWord, tailWord_7199792, baseEnd_7199792] using wordTrace_append hprefix tailTrace_7199792
  have hstable : (prefixWord ++ tailWord_7199792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199792).length < 2 ^ (prefixWord ++ tailWord_7199792).sum := by decide
  have hdescent : baseEnd_7199792 < baseStart_7199792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199814 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7199814 : Nat := 118140960795 + 7199814 * 2 ^ 59
def prefixEnd_7199814 : Nat := 4983230072969 + 3 ^ 40 * 7199814 * 2
def baseEnd_7199814 : Nat := 3696965204970198928313665

theorem tailTrace_7199814 : CollatzResearch.WordTrace tailWord_7199814 prefixEnd_7199814 3696965204970198928313665 := by
  unfold tailWord_7199814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206212185572218224388703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175065859958873988786958997 8206212185572218224388703)
  ·
    refine ⟨12309318278358327336583055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8206212185572218224388703 12309318278358327336583055)
    ·
      refine ⟨18463977417537491004874583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309318278358327336583055 18463977417537491004874583)
      ·
        refine ⟨27695966126306236507311875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18463977417537491004874583 27695966126306236507311875)
        ·
          refine ⟨41543949189459354760967813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27695966126306236507311875 41543949189459354760967813)
          ·
            refine ⟨7789490473023629017681465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41543949189459354760967813 7789490473023629017681465)
            ·
              refine ⟨5842117854767721763261099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7789490473023629017681465 5842117854767721763261099)
              ·
                refine ⟨8763176782151582644891649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5842117854767721763261099 8763176782151582644891649)
                ·
                  refine ⟨6572382586613686983668737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8763176782151582644891649 6572382586613686983668737)
                  ·
                    refine ⟨4929286939960265237751553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6572382586613686983668737 4929286939960265237751553)
                    ·
                      refine ⟨3696965204970198928313665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929286939960265237751553 3696965204970198928313665)
                      ·
                        rfl

theorem cell23_7199814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7199814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199814 prefixEnd_7199814 := by exact prefixLift 7199814
  have htrace : WordTrace (prefixWord ++ tailWord_7199814) baseStart_7199814 baseEnd_7199814 := by
    simpa [prefixWord, tailWord_7199814, baseEnd_7199814] using wordTrace_append hprefix tailTrace_7199814
  have hstable : (prefixWord ++ tailWord_7199814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199814).length < 2 ^ (prefixWord ++ tailWord_7199814).sum := by decide
  have hdescent : baseEnd_7199814 < baseStart_7199814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199829 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_7199829 : Nat := 118140960795 + 7199829 * 2 ^ 59
def prefixEnd_7199829 : Nat := 4983230072969 + 3 ^ 40 * 7199829 * 2
def baseEnd_7199829 : Nat := 1232324302393338789875365

theorem tailTrace_7199829 : CollatzResearch.WordTrace tailWord_7199829 prefixEnd_7199829 1232324302393338789875365 := by
  unfold tailWord_7199829
  simp only [CollatzResearch.WordTrace]
  refine ⟨262599337033256640742234541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175066224688837760494823027 262599337033256640742234541)
  ·
    refine ⟨98474751387471240278337953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262599337033256640742234541 98474751387471240278337953)
    ·
      refine ⟨73856063540603430208753465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98474751387471240278337953 73856063540603430208753465)
      ·
        refine ⟨55392047655452572656565099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73856063540603430208753465 55392047655452572656565099)
        ·
          refine ⟨83088071483178858984847649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55392047655452572656565099 83088071483178858984847649)
          ·
            refine ⟨62316053612384144238635737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83088071483178858984847649 62316053612384144238635737)
            ·
              refine ⟨46737040209288108178976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62316053612384144238635737 46737040209288108178976803)
              ·
                refine ⟨70105560313932162268465205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46737040209288108178976803 70105560313932162268465205)
                ·
                  refine ⟨6572396279431140212668613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70105560313932162268465205 6572396279431140212668613)
                  ·
                    refine ⟨1232324302393338789875365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6572396279431140212668613 1232324302393338789875365)
                    ·
                      rfl

theorem cell23_7199829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_7199829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199829 prefixEnd_7199829 := by exact prefixLift 7199829
  have htrace : WordTrace (prefixWord ++ tailWord_7199829) baseStart_7199829 baseEnd_7199829 := by
    simpa [prefixWord, tailWord_7199829, baseEnd_7199829] using wordTrace_append hprefix tailTrace_7199829
  have hstable : (prefixWord ++ tailWord_7199829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199829).length < 2 ^ (prefixWord ++ tailWord_7199829).sum := by decide
  have hdescent : baseEnd_7199829 < baseStart_7199829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199836 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7199836 : Nat := 118140960795 + 7199836 * 2 ^ 59
def prefixEnd_7199836 : Nat := 4983230072969 + 3 ^ 40 * 7199836 * 2
def baseEnd_7199836 : Nat := 3696976501544597842238563

theorem tailTrace_7199836 : CollatzResearch.WordTrace tailWord_7199836 prefixEnd_7199836 3696976501544597842238563 := by
  unfold tailWord_7199836
  simp only [CollatzResearch.WordTrace]
  refine ⟨131299796172115640468869681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175066394896154187291826241 131299796172115640468869681)
  ·
    refine ⟨98474847129086730351652261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131299796172115640468869681 98474847129086730351652261)
    ·
      refine ⟨18464033836703761940934799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98474847129086730351652261 18464033836703761940934799)
      ·
        refine ⟨27696050755055642911402199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18464033836703761940934799 27696050755055642911402199)
        ·
          refine ⟨41544076132583464367103299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27696050755055642911402199 41544076132583464367103299)
          ·
            refine ⟨62316114198875196550654949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41544076132583464367103299 62316114198875196550654949)
            ·
              refine ⟨11684271412289099353247803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62316114198875196550654949 11684271412289099353247803)
              ·
                refine ⟨17526407118433649029871705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684271412289099353247803 17526407118433649029871705)
                ·
                  refine ⟨13144805338825236772403779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17526407118433649029871705 13144805338825236772403779)
                  ·
                    refine ⟨19717208008237855158605669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13144805338825236772403779 19717208008237855158605669)
                    ·
                      refine ⟨3696976501544597842238563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19717208008237855158605669 3696976501544597842238563)
                      ·
                        rfl

theorem cell23_7199836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7199836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199836 prefixEnd_7199836 := by exact prefixLift 7199836
  have htrace : WordTrace (prefixWord ++ tailWord_7199836) baseStart_7199836 baseEnd_7199836 := by
    simpa [prefixWord, tailWord_7199836, baseEnd_7199836] using wordTrace_append hprefix tailTrace_7199836
  have hstable : (prefixWord ++ tailWord_7199836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199836).length < 2 ^ (prefixWord ++ tailWord_7199836).sum := by decide
  have hdescent : baseEnd_7199836 < baseStart_7199836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199929 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7199929 : Nat := 118140960795 + 7199929 * 2 ^ 59
def prefixEnd_7199929 : Nat := 4983230072969 + 3 ^ 40 * 7199929 * 2
def baseEnd_7199929 : Nat := 3697024255245465978375635

theorem tailTrace_7199929 : CollatzResearch.WordTrace tailWord_7199929 prefixEnd_7199929 3697024255245465978375635 := by
  unfold tailWord_7199929
  simp only [CollatzResearch.WordTrace]
  refine ⟨262602984332894357820874841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175068656221929571880583227 262602984332894357820874841)
  ·
    refine ⟨196952238249670768365656131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262602984332894357820874841 196952238249670768365656131)
    ·
      refine ⟨295428357374506152548484197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196952238249670768365656131 295428357374506152548484197)
      ·
        refine ⟨55392817007719903602840787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295428357374506152548484197 55392817007719903602840787)
        ·
          refine ⟨83089225511579855404261181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55392817007719903602840787 83089225511579855404261181)
          ·
            refine ⟨31158459566842445776597943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83089225511579855404261181 31158459566842445776597943)
            ·
              refine ⟨46737689350263668664896915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31158459566842445776597943 46737689350263668664896915)
              ·
                refine ⟨70106534025395502997345373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46737689350263668664896915 70106534025395502997345373)
                ·
                  refine ⟨26289950259523313624004515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70106534025395502997345373 26289950259523313624004515)
                  ·
                    refine ⟨39434925389284970436006773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26289950259523313624004515 39434925389284970436006773)
                    ·
                      refine ⟨3697024255245465978375635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39434925389284970436006773 3697024255245465978375635)
                      ·
                        rfl

theorem cell23_7199929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7199929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199929 prefixEnd_7199929 := by exact prefixLift 7199929
  have htrace : WordTrace (prefixWord ++ tailWord_7199929) baseStart_7199929 baseEnd_7199929 := by
    simpa [prefixWord, tailWord_7199929, baseEnd_7199929] using wordTrace_append hprefix tailTrace_7199929
  have hstable : (prefixWord ++ tailWord_7199929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199929).length < 2 ^ (prefixWord ++ tailWord_7199929).sum := by decide
  have hdescent : baseEnd_7199929 < baseStart_7199929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199939 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4]
def baseStart_7199939 : Nat := 118140960795 + 7199939 * 2 ^ 59
def prefixEnd_7199939 : Nat := 4983230072969 + 3 ^ 40 * 7199939 * 2
def baseEnd_7199939 : Nat := 3697029390052010939250589

theorem tailTrace_7199939 : CollatzResearch.WordTrace tailWord_7199939 prefixEnd_7199939 3697029390052010939250589 := by
  unfold tailWord_7199939
  simp only [CollatzResearch.WordTrace]
  refine ⟨262603349062858129528738871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175068899375238753019159247 262603349062858129528738871)
  ·
    refine ⟨393905023594287194293108307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262603349062858129528738871 393905023594287194293108307)
    ·
      refine ⟨590857535391430791439662461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393905023594287194293108307 590857535391430791439662461)
      ·
        refine ⟨221571575771786546789873423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590857535391430791439662461 221571575771786546789873423)
        ·
          refine ⟨332357363657679820184810135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221571575771786546789873423 332357363657679820184810135)
          ·
            refine ⟨498536045486519730277215203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332357363657679820184810135 498536045486519730277215203)
            ·
              refine ⟨747804068229779595415822805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498536045486519730277215203 747804068229779595415822805)
              ·
                refine ⟨17526657849135459267558347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 747804068229779595415822805 17526657849135459267558347)
                ·
                  refine ⟨26289986773703188901337521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17526657849135459267558347 26289986773703188901337521)
                  ·
                    refine ⟨19717490080277391676003141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26289986773703188901337521 19717490080277391676003141)
                    ·
                      refine ⟨3697029390052010939250589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19717490080277391676003141 3697029390052010939250589)
                      ·
                        rfl

theorem cell23_7199939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_7199939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199939 prefixEnd_7199939 := by exact prefixLift 7199939
  have htrace : WordTrace (prefixWord ++ tailWord_7199939) baseStart_7199939 baseEnd_7199939 := by
    simpa [prefixWord, tailWord_7199939, baseEnd_7199939] using wordTrace_append hprefix tailTrace_7199939
  have hstable : (prefixWord ++ tailWord_7199939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199939).length < 2 ^ (prefixWord ++ tailWord_7199939).sum := by decide
  have hdescent : baseEnd_7199939 < baseStart_7199939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199993 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 3]
def baseStart_7199993 : Nat := 118140960795 + 7199993 * 2 ^ 59
def prefixEnd_7199993 : Nat := 4983230072969 + 3 ^ 40 * 7199993 * 2
def baseEnd_7199993 : Nat := 3697057118007353727975341

theorem tailTrace_7199993 : CollatzResearch.WordTrace tailWord_7199993 prefixEnd_7199993 3697057118007353727975341 := by
  unfold tailWord_7199993
  simp only [CollatzResearch.WordTrace]
  refine ⟨262605318604662496751204633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175070212403108331167469755 262605318604662496751204633)
  ·
    refine ⟨196953988953496872563403475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262605318604662496751204633 196953988953496872563403475)
    ·
      refine ⟨295430983430245308845105213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196953988953496872563403475 295430983430245308845105213)
      ·
        refine ⟨110786618786341990816914455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295430983430245308845105213 110786618786341990816914455)
        ·
          refine ⟨166179928179512986225371683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110786618786341990816914455 166179928179512986225371683)
          ·
            refine ⟨249269892269269479338057525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166179928179512986225371683 249269892269269479338057525)
            ·
              refine ⟨23369052400244013687942893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249269892269269479338057525 23369052400244013687942893)
              ·
                refine ⟨8763394650091505132978585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23369052400244013687942893 8763394650091505132978585)
                ·
                  refine ⟨6572545987568628849733939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8763394650091505132978585 6572545987568628849733939)
                  ·
                    refine ⟨9858818981352943274600909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6572545987568628849733939 9858818981352943274600909)
                    ·
                      refine ⟨3697057118007353727975341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9858818981352943274600909 3697057118007353727975341)
                      ·
                        rfl

theorem cell23_7199993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_7199993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199993 prefixEnd_7199993 := by exact prefixLift 7199993
  have htrace : WordTrace (prefixWord ++ tailWord_7199993) baseStart_7199993 baseEnd_7199993 := by
    simpa [prefixWord, tailWord_7199993, baseEnd_7199993] using wordTrace_append hprefix tailTrace_7199993
  have hstable : (prefixWord ++ tailWord_7199993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199993).length < 2 ^ (prefixWord ++ tailWord_7199993).sum := by decide
  have hdescent : baseEnd_7199993 < baseStart_7199993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200003 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 3, 3, 2]
def baseStart_7200003 : Nat := 118140960795 + 7200003 * 2 ^ 59
def prefixEnd_7200003 : Nat := 4983230072969 + 3 ^ 40 * 7200003 * 2
def baseEnd_7200003 : Nat := 3697062252813898688850295

theorem tailTrace_7200003 : CollatzResearch.WordTrace tailWord_7200003 prefixEnd_7200003 3697062252813898688850295 := by
  unfold tailWord_7200003
  simp only [CollatzResearch.WordTrace]
  refine ⟨262605683334626268459068663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175070455556417512306045775 262605683334626268459068663)
  ·
    refine ⟨393908525001939402688602995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262605683334626268459068663 393908525001939402688602995)
    ·
      refine ⟨590862787502909104032904493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393908525001939402688602995 590862787502909104032904493)
      ·
        refine ⟨221573545313590914012339185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 590862787502909104032904493 221573545313590914012339185)
        ·
          refine ⟨166180158985193185509254389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221573545313590914012339185 166180158985193185509254389)
          ·
            refine ⟨15579389904861861141492599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166180158985193185509254389 15579389904861861141492599)
            ·
              refine ⟨23369084857292791712238899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15579389904861861141492599 23369084857292791712238899)
              ·
                refine ⟨35053627285939187568358349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23369084857292791712238899 35053627285939187568358349)
                ·
                  refine ⟨13145110232227195338134381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35053627285939187568358349 13145110232227195338134381)
                  ·
                    refine ⟨4929416337085198251800393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13145110232227195338134381 4929416337085198251800393)
                    ·
                      refine ⟨3697062252813898688850295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929416337085198251800393 3697062252813898688850295)
                      ·
                        rfl

theorem cell23_7200003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_7200003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200003 prefixEnd_7200003 := by exact prefixLift 7200003
  have htrace : WordTrace (prefixWord ++ tailWord_7200003) baseStart_7200003 baseEnd_7200003 := by
    simpa [prefixWord, tailWord_7200003, baseEnd_7200003] using wordTrace_append hprefix tailTrace_7200003
  have hstable : (prefixWord ++ tailWord_7200003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200003).length < 2 ^ (prefixWord ++ tailWord_7200003).sum := by decide
  have hdescent : baseEnd_7200003 < baseStart_7200003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200036 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_7200036 : Nat := 118140960795 + 7200036 * 2 ^ 59
def prefixEnd_7200036 : Nat := 4983230072969 + 3 ^ 40 * 7200036 * 2
def baseEnd_7200036 : Nat := 3697079197675497059737643

theorem tailTrace_7200036 : CollatzResearch.WordTrace tailWord_7200036 prefixEnd_7200036 3697079197675497059737643 := by
  unfold tailWord_7200036
  simp only [CollatzResearch.WordTrace]
  refine ⟨131303443471753357547509981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175071257962337810063346641 131303443471753357547509981)
  ·
    refine ⟨49238791301907509080316243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131303443471753357547509981 49238791301907509080316243)
    ·
      refine ⟨73858186952861263620474365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49238791301907509080316243 73858186952861263620474365)
      ·
        refine ⟨27696820107322973857677887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73858186952861263620474365 27696820107322973857677887)
        ·
          refine ⟨41545230160984460786516831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27696820107322973857677887 41545230160984460786516831)
          ·
            refine ⟨62317845241476691179775247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41545230160984460786516831 62317845241476691179775247)
            ·
              refine ⟨93476767862215036769662871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62317845241476691179775247 93476767862215036769662871)
              ·
                refine ⟨140215151793322555154494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93476767862215036769662871 140215151793322555154494307)
                ·
                  refine ⟨210322727689983832731741461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140215151793322555154494307 210322727689983832731741461)
                  ·
                    refine ⟨9858877860467992159300381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 210322727689983832731741461 9858877860467992159300381)
                    ·
                      refine ⟨3697079197675497059737643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9858877860467992159300381 3697079197675497059737643)
                      ·
                        rfl

theorem cell23_7200036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_7200036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200036 prefixEnd_7200036 := by exact prefixLift 7200036
  have htrace : WordTrace (prefixWord ++ tailWord_7200036) baseStart_7200036 baseEnd_7200036 := by
    simpa [prefixWord, tailWord_7200036, baseEnd_7200036] using wordTrace_append hprefix tailTrace_7200036
  have hstable : (prefixWord ++ tailWord_7200036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200036).length < 2 ^ (prefixWord ++ tailWord_7200036).sum := by decide
  have hdescent : baseEnd_7200036 < baseStart_7200036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200050 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_7200050 : Nat := 118140960795 + 7200050 * 2 ^ 59
def prefixEnd_7200050 : Nat := 4983230072969 + 3 ^ 40 * 7200050 * 2
def baseEnd_7200050 : Nat := 3697086386404660004962579

theorem tailTrace_7200050 : CollatzResearch.WordTrace tailWord_7200050 prefixEnd_7200050 3697086386404660004962579 := by
  unfold tailWord_7200050
  simp only [CollatzResearch.WordTrace]
  refine ⟨65651849391363998871507401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175071598376970663657353069 65651849391363998871507401)
  ·
    refine ⟨49238887043522999153630551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65651849391363998871507401 49238887043522999153630551)
    ·
      refine ⟨73858330565284498730445827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49238887043522999153630551 73858330565284498730445827)
      ·
        refine ⟨110787495847926748095668741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73858330565284498730445827 110787495847926748095668741)
        ·
          refine ⟨20772655471486265267937889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110787495847926748095668741 20772655471486265267937889)
          ·
            refine ⟨15579491603614698950953417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20772655471486265267937889 15579491603614698950953417)
            ·
              refine ⟨11684618702711024213215063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15579491603614698950953417 11684618702711024213215063)
              ·
                refine ⟨17526928054066536319822595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684618702711024213215063 17526928054066536319822595)
                ·
                  refine ⟨26290392081099804479733893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17526928054066536319822595 26290392081099804479733893)
                  ·
                    refine ⟨4929448515206213339950105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26290392081099804479733893 4929448515206213339950105)
                    ·
                      refine ⟨3697086386404660004962579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929448515206213339950105 3697086386404660004962579)
                      ·
                        rfl

theorem cell23_7200050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_7200050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200050 prefixEnd_7200050 := by exact prefixLift 7200050
  have htrace : WordTrace (prefixWord ++ tailWord_7200050) baseStart_7200050 baseEnd_7200050 := by
    simpa [prefixWord, tailWord_7200050, baseEnd_7200050] using wordTrace_append hprefix tailTrace_7200050
  have hstable : (prefixWord ++ tailWord_7200050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200050).length < 2 ^ (prefixWord ++ tailWord_7200050).sum := by decide
  have hdescent : baseEnd_7200050 < baseStart_7200050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200200 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_7200200 : Nat := 118140960795 + 7200200 * 2 ^ 59
def prefixEnd_7200200 : Nat := 4983230072969 + 3 ^ 40 * 7200200 * 2
def baseEnd_7200200 : Nat := 3697163408502834418086889

theorem tailTrace_7200200 : CollatzResearch.WordTrace tailWord_7200200 prefixEnd_7200200 3697163408502834418086889 := by
  unfold tailWord_7200200
  simp only [CollatzResearch.WordTrace]
  refine ⟨131306434257456285551995027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175075245676608380735993369 131306434257456285551995027)
  ·
    refine ⟨196959651386184428327992541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131306434257456285551995027 196959651386184428327992541)
    ·
      refine ⟨73859869269819160622997203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196959651386184428327992541 73859869269819160622997203)
      ·
        refine ⟨110789803904728740934495805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73859869269819160622997203 110789803904728740934495805)
        ·
          refine ⟨41546176464273277850435927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110789803904728740934495805 41546176464273277850435927)
          ·
            refine ⟨62319264696409916775653891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41546176464273277850435927 62319264696409916775653891)
            ·
              refine ⟨93478897044614875163480837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62319264696409916775653891 93478897044614875163480837)
              ·
                refine ⟨17527293195865289093152657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93478897044614875163480837 17527293195865289093152657)
                ·
                  refine ⟨13145469896898966819864493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17527293195865289093152657 13145469896898966819864493)
                  ·
                    refine ⟨4929551211337112557449185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13145469896898966819864493 4929551211337112557449185)
                    ·
                      refine ⟨3697163408502834418086889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929551211337112557449185 3697163408502834418086889)
                      ·
                        rfl

theorem cell23_7200200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_7200200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200200 prefixEnd_7200200 := by exact prefixLift 7200200
  have htrace : WordTrace (prefixWord ++ tailWord_7200200) baseStart_7200200 baseEnd_7200200 := by
    simpa [prefixWord, tailWord_7200200, baseEnd_7200200] using wordTrace_append hprefix tailTrace_7200200
  have hstable : (prefixWord ++ tailWord_7200200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200200).length < 2 ^ (prefixWord ++ tailWord_7200200).sum := by decide
  have hdescent : baseEnd_7200200 < baseStart_7200200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200213 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7200213 : Nat := 118140960795 + 7200213 * 2 ^ 59
def prefixEnd_7200213 : Nat := 4983230072969 + 3 ^ 40 * 7200213 * 2
def baseEnd_7200213 : Nat := 3697170083751342867224329

theorem tailTrace_7200213 : CollatzResearch.WordTrace tailWord_7200213 prefixEnd_7200213 3697170083751342867224329 := by
  unfold tailWord_7200213
  simp only [CollatzResearch.WordTrace]
  refine ⟨262613342663865474324213293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175075561775910316216142195 262613342663865474324213293)
  ·
    refine ⟨98480003498949552871579985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262613342663865474324213293 98480003498949552871579985)
    ·
      refine ⟨73860002624212164653684989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98480003498949552871579985 73860002624212164653684989)
      ·
        refine ⟨27697500984079561745131871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73860002624212164653684989 27697500984079561745131871)
        ·
          refine ⟨41546251476119342617697807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27697500984079561745131871 41546251476119342617697807)
          ·
            refine ⟨62319377214179013926546711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41546251476119342617697807 62319377214179013926546711)
            ·
              refine ⟨93479065821268520889820067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62319377214179013926546711 93479065821268520889820067)
              ·
                refine ⟨140218598731902781334730101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93479065821268520889820067 140218598731902781334730101)
                ·
                  refine ⟨13145493631115885750130947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140218598731902781334730101 13145493631115885750130947)
                  ·
                    refine ⟨19718240446673828625196421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13145493631115885750130947 19718240446673828625196421)
                    ·
                      refine ⟨3697170083751342867224329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19718240446673828625196421 3697170083751342867224329)
                      ·
                        rfl

theorem cell23_7200213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7200213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200213 prefixEnd_7200213 := by exact prefixLift 7200213
  have htrace : WordTrace (prefixWord ++ tailWord_7200213) baseStart_7200213 baseEnd_7200213 := by
    simpa [prefixWord, tailWord_7200213, baseEnd_7200213] using wordTrace_append hprefix tailTrace_7200213
  have hstable : (prefixWord ++ tailWord_7200213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200213).length < 2 ^ (prefixWord ++ tailWord_7200213).sum := by decide
  have hdescent : baseEnd_7200213 < baseStart_7200213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200223 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 1, 6]
def baseStart_7200223 : Nat := 118140960795 + 7200223 * 2 ^ 59
def prefixEnd_7200223 : Nat := 4983230072969 + 3 ^ 40 * 7200223 * 2
def baseEnd_7200223 : Nat := 1232391739519295942699761

theorem tailTrace_7200223 : CollatzResearch.WordTrace tailWord_7200223 prefixEnd_7200223 1232391739519295942699761 := by
  unfold tailWord_7200223
  simp only [CollatzResearch.WordTrace]
  refine ⟨262613707393829246032077323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175075804929219497354718215 262613707393829246032077323)
  ·
    refine ⟨393920561090743869048115985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262613707393829246032077323 393920561090743869048115985)
    ·
      refine ⟨295440420818057901786086989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393920561090743869048115985 295440420818057901786086989)
      ·
        refine ⟨110790157806771713169782621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295440420818057901786086989 110790157806771713169782621)
        ·
          refine ⟨41546309177539392438668483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110790157806771713169782621 41546309177539392438668483)
          ·
            refine ⟨62319463766309088658002725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41546309177539392438668483 62319463766309088658002725)
            ·
              refine ⟨11684899456182954123375511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62319463766309088658002725 11684899456182954123375511)
              ·
                refine ⟨17527349184274431185063267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684899456182954123375511 17527349184274431185063267)
                ·
                  refine ⟨26291023776411646777594901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17527349184274431185063267 26291023776411646777594901)
                  ·
                    refine ⟨1232391739519295942699761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26291023776411646777594901 1232391739519295942699761)
                    ·
                      rfl

theorem cell23_7200223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_7200223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200223 prefixEnd_7200223 := by exact prefixLift 7200223
  have htrace : WordTrace (prefixWord ++ tailWord_7200223) baseStart_7200223 baseEnd_7200223 := by
    simpa [prefixWord, tailWord_7200223, baseEnd_7200223] using wordTrace_append hprefix tailTrace_7200223
  have hstable : (prefixWord ++ tailWord_7200223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200223).length < 2 ^ (prefixWord ++ tailWord_7200223).sum := by decide
  have hdescent : baseEnd_7200223 < baseStart_7200223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200234 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_7200234 : Nat := 118140960795 + 7200234 * 2 ^ 59
def prefixEnd_7200234 : Nat := 4983230072969 + 3 ^ 40 * 7200234 * 2
def baseEnd_7200234 : Nat := 3697180866845087285061733

theorem tailTrace_7200234 : CollatzResearch.WordTrace tailWord_7200234 prefixEnd_7200234 3697180866845087285061733 := by
  unfold tailWord_7200234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65653527149197348727681939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175076072397859596607151837 65653527149197348727681939)
  ·
    refine ⟨98480290723796023091522909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65653527149197348727681939 98480290723796023091522909)
    ·
      refine ⟨36930109021423508659321091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98480290723796023091522909 36930109021423508659321091)
      ·
        refine ⟨55395163532135262988981637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36930109021423508659321091 55395163532135262988981637)
        ·
          refine ⟨10386593162275361810434057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55395163532135262988981637 10386593162275361810434057)
          ·
            refine ⟨7789944871706521357825543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10386593162275361810434057 7789944871706521357825543)
            ·
              refine ⟨11684917307559782036738315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7789944871706521357825543 11684917307559782036738315)
              ·
                refine ⟨17527375961339673055107473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684917307559782036738315 17527375961339673055107473)
                ·
                  refine ⟨13145531971004754791330605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17527375961339673055107473 13145531971004754791330605)
                  ·
                    refine ⟨4929574489126783046748977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13145531971004754791330605 4929574489126783046748977)
                    ·
                      refine ⟨3697180866845087285061733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929574489126783046748977 3697180866845087285061733)
                      ·
                        rfl

theorem cell23_7200234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_7200234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200234 prefixEnd_7200234 := by exact prefixLift 7200234
  have htrace : WordTrace (prefixWord ++ tailWord_7200234) baseStart_7200234 baseEnd_7200234 := by
    simpa [prefixWord, tailWord_7200234, baseEnd_7200234] using wordTrace_append hprefix tailTrace_7200234
  have hstable : (prefixWord ++ tailWord_7200234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200234).length < 2 ^ (prefixWord ++ tailWord_7200234).sum := by decide
  have hdescent : baseEnd_7200234 < baseStart_7200234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200250 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_7200250 : Nat := 118140960795 + 7200250 * 2 ^ 59
def prefixEnd_7200250 : Nat := 4983230072969 + 3 ^ 40 * 7200250 * 2
def baseEnd_7200250 : Nat := 3697189082535559222461659

theorem tailTrace_7200250 : CollatzResearch.WordTrace tailWord_7200250 prefixEnd_7200250 3697189082535559222461659 := by
  unfold tailWord_7200250
  simp only [CollatzResearch.WordTrace]
  refine ⟨65653673041182857410827551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175076461443154286428873469 65653673041182857410827551)
  ·
    refine ⟨98480509561774286116241327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65653673041182857410827551 98480509561774286116241327)
    ·
      refine ⟨147720764342661429174361991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98480509561774286116241327 147720764342661429174361991)
      ·
        refine ⟨221581146513992143761542987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147720764342661429174361991 221581146513992143761542987)
        ·
          refine ⟨332371719770988215642314481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221581146513992143761542987 332371719770988215642314481)
          ·
            refine ⟨249278789828241161731735861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332371719770988215642314481 249278789828241161731735861)
            ·
              refine ⟨23369886546397608912350237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249278789828241161731735861 23369886546397608912350237)
              ·
                refine ⟨8763707454899103342131339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23369886546397608912350237 8763707454899103342131339)
                ·
                  refine ⟨13145561182348655013197009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8763707454899103342131339 13145561182348655013197009)
                  ·
                    refine ⟨9859170886761491259897757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13145561182348655013197009 9859170886761491259897757)
                    ·
                      refine ⟨3697189082535559222461659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9859170886761491259897757 3697189082535559222461659)
                      ·
                        rfl

theorem cell23_7200250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_7200250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200250 prefixEnd_7200250 := by exact prefixLift 7200250
  have htrace : WordTrace (prefixWord ++ tailWord_7200250) baseStart_7200250 baseEnd_7200250 := by
    simpa [prefixWord, tailWord_7200250, baseEnd_7200250] using wordTrace_append hprefix tailTrace_7200250
  have hstable : (prefixWord ++ tailWord_7200250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200250).length < 2 ^ (prefixWord ++ tailWord_7200250).sum := by decide
  have hdescent : baseEnd_7200250 < baseStart_7200250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200264 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_7200264 : Nat := 118140960795 + 7200264 * 2 ^ 59
def prefixEnd_7200264 : Nat := 4983230072969 + 3 ^ 40 * 7200264 * 2
def baseEnd_7200264 : Nat := 3697196271264722167686595

theorem tailTrace_7200264 : CollatzResearch.WordTrace tailWord_7200264 prefixEnd_7200264 3697196271264722167686595 := by
  unfold tailWord_7200264
  simp only [CollatzResearch.WordTrace]
  refine ⟨131307601393340355017159923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175076801857787140022879897 131307601393340355017159923)
  ·
    refine ⟨196961402090010532525739885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131307601393340355017159923 196961402090010532525739885)
    ·
      refine ⟨73860525783753949697152457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196961402090010532525739885 73860525783753949697152457)
      ·
        refine ⟨55395394337815462272864343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73860525783753949697152457 55395394337815462272864343)
        ·
          refine ⟨83093091506723193409296515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55395394337815462272864343 83093091506723193409296515)
          ·
            refine ⟨124639637260084790113944773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83093091506723193409296515 124639637260084790113944773)
            ·
              refine ⟨23369931986265898146364645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124639637260084790113944773 23369931986265898146364645)
              ·
                refine ⟨4381862247424855902443371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23369931986265898146364645 4381862247424855902443371)
                ·
                  refine ⟨6572793371137283853665057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381862247424855902443371 6572793371137283853665057)
                  ·
                    refine ⟨4929595028352962890248793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6572793371137283853665057 4929595028352962890248793)
                    ·
                      refine ⟨3697196271264722167686595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929595028352962890248793 3697196271264722167686595)
                      ·
                        rfl

theorem cell23_7200264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_7200264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200264 prefixEnd_7200264 := by exact prefixLift 7200264
  have htrace : WordTrace (prefixWord ++ tailWord_7200264) baseStart_7200264 baseEnd_7200264 := by
    simpa [prefixWord, tailWord_7200264, baseEnd_7200264] using wordTrace_append hprefix tailTrace_7200264
  have hstable : (prefixWord ++ tailWord_7200264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200264).length < 2 ^ (prefixWord ++ tailWord_7200264).sum := by decide
  have hdescent : baseEnd_7200264 < baseStart_7200264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200307 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 1, 3, 2]
def baseStart_7200307 : Nat := 118140960795 + 7200307 * 2 ^ 59
def prefixEnd_7200307 : Nat := 4983230072969 + 3 ^ 40 * 7200307 * 2
def baseEnd_7200307 : Nat := 3697218350932865499448897

theorem tailTrace_7200307 : CollatzResearch.WordTrace tailWord_7200307 prefixEnd_7200307 3697218350932865499448897 := by
  unfold tailWord_7200307
  simp only [CollatzResearch.WordTrace]
  refine ⟨262616771125524928378135175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175077847417016618918756783 262616771125524928378135175)
  ·
    refine ⟨393925156688287392567202763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262616771125524928378135175 393925156688287392567202763)
    ·
      refine ⟨590887735032431088850804145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393925156688287392567202763 590887735032431088850804145)
      ·
        refine ⟨443165801274323316638103109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590887735032431088850804145 443165801274323316638103109)
        ·
          refine ⟨83093587738935621869644333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443165801274323316638103109 83093587738935621869644333)
          ·
            refine ⟨31160095402100858201116625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83093587738935621869644333 31160095402100858201116625)
            ·
              refine ⟨23370071551575643650837469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31160095402100858201116625 23370071551575643650837469)
              ·
                refine ⟨8763776831840866369064051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23370071551575643650837469 8763776831840866369064051)
                ·
                  refine ⟨13145665247761299553596077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8763776831840866369064051 13145665247761299553596077)
                  ·
                    refine ⟨4929624467910487332598529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13145665247761299553596077 4929624467910487332598529)
                    ·
                      refine ⟨3697218350932865499448897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929624467910487332598529 3697218350932865499448897)
                      ·
                        rfl

theorem cell23_7200307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3, 2].length) (baseStart_7200307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200307 prefixEnd_7200307 := by exact prefixLift 7200307
  have htrace : WordTrace (prefixWord ++ tailWord_7200307) baseStart_7200307 baseEnd_7200307 := by
    simpa [prefixWord, tailWord_7200307, baseEnd_7200307] using wordTrace_append hprefix tailTrace_7200307
  have hstable : (prefixWord ++ tailWord_7200307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200307).length < 2 ^ (prefixWord ++ tailWord_7200307).sum := by decide
  have hdescent : baseEnd_7200307 < baseStart_7200307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200407 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 2, 5]
def baseStart_7200407 : Nat := 118140960795 + 7200407 * 2 ^ 59
def prefixEnd_7200407 : Nat := 4983230072969 + 3 ^ 40 * 7200407 * 2
def baseEnd_7200407 : Nat := 1232423232999438369399479

theorem tailTrace_7200407 : CollatzResearch.WordTrace tailWord_7200407 prefixEnd_7200407 1232423232999438369399479 := by
  unfold tailWord_7200407
  simp only [CollatzResearch.WordTrace]
  refine ⟨262620418425162645456775475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175080278950108430304516983 262620418425162645456775475)
  ·
    refine ⟨393930627637743968185163213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262620418425162645456775475 393930627637743968185163213)
    ·
      refine ⟨147723985364153988069436205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393930627637743968185163213 147723985364153988069436205)
      ·
        refine ⟨55396494511557745526038577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147723985364153988069436205 55396494511557745526038577)
        ·
          refine ⟨41547370883668309144528933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55396494511557745526038577 41547370883668309144528933)
          ·
            refine ⟨7790132040687807964599175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41547370883668309144528933 7790132040687807964599175)
            ·
              refine ⟨11685198061031711946898763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7790132040687807964599175 11685198061031711946898763)
              ·
                refine ⟨17527797091547567920348145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11685198061031711946898763 17527797091547567920348145)
                ·
                  refine ⟨13145847818660675940261109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17527797091547567920348145 13145847818660675940261109)
                  ·
                    refine ⟨1232423232999438369399479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13145847818660675940261109 1232423232999438369399479)
                    ·
                      rfl

theorem cell23_7200407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_7200407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200407 prefixEnd_7200407 := by exact prefixLift 7200407
  have htrace : WordTrace (prefixWord ++ tailWord_7200407) baseStart_7200407 baseEnd_7200407 := by
    simpa [prefixWord, tailWord_7200407, baseEnd_7200407] using wordTrace_append hprefix tailTrace_7200407
  have hstable : (prefixWord ++ tailWord_7200407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200407).length < 2 ^ (prefixWord ++ tailWord_7200407).sum := by decide
  have hdescent : baseEnd_7200407 < baseStart_7200407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200463 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 9]
def baseStart_7200463 : Nat := 118140960795 + 7200463 * 2 ^ 59
def prefixEnd_7200463 : Nat := 4983230072969 + 3 ^ 40 * 7200463 * 2
def baseEnd_7200463 : Nat := 1232432817971655629699393

theorem tailTrace_7200463 : CollatzResearch.WordTrace tailWord_7200463 prefixEnd_7200463 1232432817971655629699393 := by
  unfold tailWord_7200463
  simp only [CollatzResearch.WordTrace]
  refine ⟨262622460912959767020814043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175081640608639844680542695 262622460912959767020814043)
  ·
    refine ⟨393933691369439650531221065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262622460912959767020814043 393933691369439650531221065)
    ·
      refine ⟨295450268527079737898415799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393933691369439650531221065 295450268527079737898415799)
      ·
        refine ⟨443175402790619606847623699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295450268527079737898415799 443175402790619606847623699)
        ·
          refine ⟨664763104185929410271435549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443175402790619606847623699 664763104185929410271435549)
          ·
            refine ⟨249286164069723528851788331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664763104185929410271435549 249286164069723528851788331)
            ·
              refine ⟨373929246104585293277682497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249286164069723528851788331 373929246104585293277682497)
              ·
                refine ⟨280446934578438969958261873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373929246104585293277682497 280446934578438969958261873)
                ·
                  refine ⟨210335200933829227468696405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280446934578438969958261873 210335200933829227468696405)
                  ·
                    refine ⟨1232432817971655629699393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210335200933829227468696405 1232432817971655629699393)
                    ·
                      rfl

theorem cell23_7200463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_7200463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200463 prefixEnd_7200463 := by exact prefixLift 7200463
  have htrace : WordTrace (prefixWord ++ tailWord_7200463) baseStart_7200463 baseEnd_7200463 := by
    simpa [prefixWord, tailWord_7200463, baseEnd_7200463] using wordTrace_append hprefix tailTrace_7200463
  have hstable : (prefixWord ++ tailWord_7200463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200463).length < 2 ^ (prefixWord ++ tailWord_7200463).sum := by decide
  have hdescent : baseEnd_7200463 < baseStart_7200463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200544 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_7200544 : Nat := 118140960795 + 7200544 * 2 ^ 59
def prefixEnd_7200544 : Nat := 4983230072969 + 3 ^ 40 * 7200544 * 2
def baseEnd_7200544 : Nat := 1232446681949327024061769

theorem tailTrace_7200544 : CollatzResearch.WordTrace tailWord_7200544 prefixEnd_7200544 1232446681949327024061769 := by
  unfold tailWord_7200544
  simp only [CollatzResearch.WordTrace]
  refine ⟨131312707612833158927256343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175083610150444211903008457 131312707612833158927256343)
  ·
    refine ⟨196969061419249738390884515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131312707612833158927256343 196969061419249738390884515)
    ·
      refine ⟨295453592128874607586326773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196969061419249738390884515 295453592128874607586326773)
      ·
        refine ⟨27698774262081994461218135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295453592128874607586326773 27698774262081994461218135)
        ·
          refine ⟨41548161393122991691827203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27698774262081994461218135 41548161393122991691827203)
          ·
            refine ⟨62322242089684487537740805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41548161393122991691827203 62322242089684487537740805)
            ·
              refine ⟨11685420391815841413326401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62322242089684487537740805 11685420391815841413326401)
              ·
                refine ⟨8764065293861881059994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11685420391815841413326401 8764065293861881059994801)
                ·
                  refine ⟨6573048970396410794996101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8764065293861881059994801 6573048970396410794996101)
                  ·
                    refine ⟨1232446681949327024061769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6573048970396410794996101 1232446681949327024061769)
                    ·
                      rfl

theorem cell23_7200544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_7200544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200544 prefixEnd_7200544 := by exact prefixLift 7200544
  have htrace : WordTrace (prefixWord ++ tailWord_7200544) baseStart_7200544 baseEnd_7200544 := by
    simpa [prefixWord, tailWord_7200544, baseEnd_7200544] using wordTrace_append hprefix tailTrace_7200544
  have hstable : (prefixWord ++ tailWord_7200544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200544).length < 2 ^ (prefixWord ++ tailWord_7200544).sum := by decide
  have hdescent : baseEnd_7200544 < baseStart_7200544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200564 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7200564 : Nat := 118140960795 + 7200564 * 2 ^ 59
def prefixEnd_7200564 : Nat := 4983230072969 + 3 ^ 40 * 7200564 * 2
def baseEnd_7200564 : Nat := 3697350315461070993935215

theorem tailTrace_7200564 : CollatzResearch.WordTrace tailWord_7200564 prefixEnd_7200564 3697350315461070993935215 := by
  unfold tailWord_7200564
  simp only [CollatzResearch.WordTrace]
  refine ⟨131313072342796930635120373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175084096457062574180160497 131313072342796930635120373)
  ·
    refine ⟨12310600532137212247042535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131313072342796930635120373 12310600532137212247042535)
    ·
      refine ⟨18465900798205818370563803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12310600532137212247042535 18465900798205818370563803)
      ·
        refine ⟨27698851197308727555845705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18465900798205818370563803 27698851197308727555845705)
        ·
          refine ⟨20774138397981545666884279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27698851197308727555845705 20774138397981545666884279)
          ·
            refine ⟨31161207596972318500326419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20774138397981545666884279 31161207596972318500326419)
            ·
              refine ⟨46741811395458477750489629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31161207596972318500326419 46741811395458477750489629)
              ·
                refine ⟨17528179273296929156433611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46741811395458477750489629 17528179273296929156433611)
                ·
                  refine ⟨26292268909945393734650417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17528179273296929156433611 26292268909945393734650417)
                  ·
                    refine ⟨19719201682459045300987813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26292268909945393734650417 19719201682459045300987813)
                    ·
                      refine ⟨3697350315461070993935215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19719201682459045300987813 3697350315461070993935215)
                      ·
                        rfl

theorem cell23_7200564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7200564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200564 prefixEnd_7200564 := by exact prefixLift 7200564
  have htrace : WordTrace (prefixWord ++ tailWord_7200564) baseStart_7200564 baseEnd_7200564 := by
    simpa [prefixWord, tailWord_7200564, baseEnd_7200564] using wordTrace_append hprefix tailTrace_7200564
  have hstable : (prefixWord ++ tailWord_7200564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200564).length < 2 ^ (prefixWord ++ tailWord_7200564).sum := by decide
  have hdescent : baseEnd_7200564 < baseStart_7200564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200574 : List Nat := [4, 2, 1, 2, 2, 2, 3, 7]
def baseStart_7200574 : Nat := 118140960795 + 7200574 * 2 ^ 59
def prefixEnd_7200574 : Nat := 4983230072969 + 3 ^ 40 * 7200574 * 2
def baseEnd_7200574 : Nat := 136939090750652442770747

theorem tailTrace_7200574 : CollatzResearch.WordTrace tailWord_7200574 prefixEnd_7200574 136939090750652442770747 := by
  unfold tailWord_7200574
  simp only [CollatzResearch.WordTrace]
  refine ⟨32828313676944704122263097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175084339610371755318736517 32828313676944704122263097)
  ·
    refine ⟨24621235257708528091697323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32828313676944704122263097 24621235257708528091697323)
    ·
      refine ⟨36931852886562792137545985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24621235257708528091697323 36931852886562792137545985)
      ·
        refine ⟨27698889664922094103159489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36931852886562792137545985 27698889664922094103159489)
        ·
          refine ⟨20774167248691570577369617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27698889664922094103159489 20774167248691570577369617)
          ·
            refine ⟨15580625436518677933027213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20774167248691570577369617 15580625436518677933027213)
            ·
              refine ⟨5842734538694504224885205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15580625436518677933027213 5842734538694504224885205)
              ·
                refine ⟨136939090750652442770747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5842734538694504224885205 136939090750652442770747)
                ·
                  rfl

theorem cell23_7200574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_7200574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200574 prefixEnd_7200574 := by exact prefixLift 7200574
  have htrace : WordTrace (prefixWord ++ tailWord_7200574) baseStart_7200574 baseEnd_7200574 := by
    simpa [prefixWord, tailWord_7200574, baseEnd_7200574] using wordTrace_append hprefix tailTrace_7200574
  have hstable : (prefixWord ++ tailWord_7200574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200574).length < 2 ^ (prefixWord ++ tailWord_7200574).sum := by decide
  have hdescent : baseEnd_7200574 < baseStart_7200574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200588 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7200588 : Nat := 118140960795 + 7200588 * 2 ^ 59
def prefixEnd_7200588 : Nat := 4983230072969 + 3 ^ 40 * 7200588 * 2
def baseEnd_7200588 : Nat := 3697362638996778900035105

theorem tailTrace_7200588 : CollatzResearch.WordTrace tailWord_7200588 prefixEnd_7200588 3697362638996778900035105 := by
  unfold tailWord_7200588
  simp only [CollatzResearch.WordTrace]
  refine ⟨131313510018753456684557209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175084680025004608912742945 131313510018753456684557209)
  ·
    refine ⟨98485132514065092513417907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131313510018753456684557209 98485132514065092513417907)
    ·
      refine ⟨147727698771097638770126861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98485132514065092513417907 147727698771097638770126861)
      ·
        refine ⟨55397887039161614538797573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147727698771097638770126861 55397887039161614538797573)
        ·
          refine ⟨10387103819842802726024545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55397887039161614538797573 10387103819842802726024545)
          ·
            refine ⟨7790327864882102044518409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10387103819842802726024545 7790327864882102044518409)
            ·
              refine ⟨5842745898661576533388807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7790327864882102044518409 5842745898661576533388807)
              ·
                refine ⟨8764118847992364800083211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5842745898661576533388807 8764118847992364800083211)
                ·
                  refine ⟨13146178271988547200124817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764118847992364800083211 13146178271988547200124817)
                  ·
                    refine ⟨9859633703991410400093613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13146178271988547200124817 9859633703991410400093613)
                    ·
                      refine ⟨3697362638996778900035105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9859633703991410400093613 3697362638996778900035105)
                      ·
                        rfl

theorem cell23_7200588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7200588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200588 prefixEnd_7200588 := by exact prefixLift 7200588
  have htrace : WordTrace (prefixWord ++ tailWord_7200588) baseStart_7200588 baseEnd_7200588 := by
    simpa [prefixWord, tailWord_7200588, baseEnd_7200588] using wordTrace_append hprefix tailTrace_7200588
  have hstable : (prefixWord ++ tailWord_7200588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200588).length < 2 ^ (prefixWord ++ tailWord_7200588).sum := by decide
  have hdescent : baseEnd_7200588 < baseStart_7200588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200618 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7200618 : Nat := 118140960795 + 7200618 * 2 ^ 59
def prefixEnd_7200618 : Nat := 4983230072969 + 3 ^ 40 * 7200618 * 2
def baseEnd_7200618 : Nat := 3697378043416413782659967

theorem tailTrace_7200618 : CollatzResearch.WordTrace tailWord_7200618 prefixEnd_7200618 3697378043416413782659967 := by
  unfold tailWord_7200618
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657028556849557123176627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175085409484932152328471005 65657028556849557123176627)
  ·
    refine ⟨98485542835274335684764941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65657028556849557123176627 98485542835274335684764941)
    ·
      refine ⟨36932078563227875881786853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98485542835274335684764941 36932078563227875881786853)
      ·
        refine ⟨6924764730605226727835035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36932078563227875881786853 6924764730605226727835035)
        ·
          refine ⟨10387147095907840091752553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6924764730605226727835035 10387147095907840091752553)
          ·
            refine ⟨7790360321930880068814415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10387147095907840091752553 7790360321930880068814415)
            ·
              refine ⟨11685540482896320103221623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7790360321930880068814415 11685540482896320103221623)
              ·
                refine ⟨17528310724344480154832435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11685540482896320103221623 17528310724344480154832435)
                ·
                  refine ⟨26292466086516720232248653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17528310724344480154832435 26292466086516720232248653)
                  ·
                    refine ⟨9859674782443770087093245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26292466086516720232248653 9859674782443770087093245)
                    ·
                      refine ⟨3697378043416413782659967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9859674782443770087093245 3697378043416413782659967)
                      ·
                        rfl

theorem cell23_7200618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7200618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200618 prefixEnd_7200618 := by exact prefixLift 7200618
  have htrace : WordTrace (prefixWord ++ tailWord_7200618) baseStart_7200618 baseEnd_7200618 := by
    simpa [prefixWord, tailWord_7200618, baseEnd_7200618] using wordTrace_append hprefix tailTrace_7200618
  have hstable : (prefixWord ++ tailWord_7200618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200618).length < 2 ^ (prefixWord ++ tailWord_7200618).sum := by decide
  have hdescent : baseEnd_7200618 < baseStart_7200618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200657 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_7200657 : Nat := 118140960795 + 7200657 * 2 ^ 59
def prefixEnd_7200657 : Nat := 4983230072969 + 3 ^ 40 * 7200657 * 2
def baseEnd_7200657 : Nat := 3697398069161939130072287

theorem tailTrace_7200657 : CollatzResearch.WordTrace tailWord_7200657 prefixEnd_7200657 3697398069161939130072287 := by
  unfold tailWord_7200657
  simp only [CollatzResearch.WordTrace]
  refine ⟨262629536674256938153376225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175086357782837958768917483 262629536674256938153376225)
  ·
    refine ⟨196972152505692703615032169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262629536674256938153376225 196972152505692703615032169)
    ·
      refine ⟨147729114379269527711274127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196972152505692703615032169 147729114379269527711274127)
      ·
        refine ⟨221593671568904291566911191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147729114379269527711274127 221593671568904291566911191)
        ·
          refine ⟨332390507353356437350366787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221593671568904291566911191 332390507353356437350366787)
          ·
            refine ⟨498585761030034656025550181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332390507353356437350366787 498585761030034656025550181)
            ·
              refine ⟨93484830193131498004790659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498585761030034656025550181 93484830193131498004790659)
              ·
                refine ⟨140227245289697247007185989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93484830193131498004790659 140227245289697247007185989)
                ·
                  refine ⟨26292608491818233813847373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140227245289697247007185989 26292608491818233813847373)
                  ·
                    refine ⟨9859728184431837680192765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26292608491818233813847373 9859728184431837680192765)
                    ·
                      refine ⟨3697398069161939130072287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9859728184431837680192765 3697398069161939130072287)
                      ·
                        rfl

theorem cell23_7200657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_7200657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200657 prefixEnd_7200657 := by exact prefixLift 7200657
  have htrace : WordTrace (prefixWord ++ tailWord_7200657) baseStart_7200657 baseEnd_7200657 := by
    simpa [prefixWord, tailWord_7200657, baseEnd_7200657] using wordTrace_append hprefix tailTrace_7200657
  have hstable : (prefixWord ++ tailWord_7200657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200657).length < 2 ^ (prefixWord ++ tailWord_7200657).sum := by decide
  have hdescent : baseEnd_7200657 < baseStart_7200657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200658 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7200658 : Nat := 118140960795 + 7200658 * 2 ^ 59
def prefixEnd_7200658 : Nat := 4983230072969 + 3 ^ 40 * 7200658 * 2
def baseEnd_7200658 : Nat := 3697398582642593626159783

theorem tailTrace_7200658 : CollatzResearch.WordTrace tailWord_7200658 prefixEnd_7200658 3697398582642593626159783 := by
  unfold tailWord_7200658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657393286813328831040657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175086382098168876882775085 65657393286813328831040657)
  ·
    refine ⟨49243044965109996623280493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65657393286813328831040657 49243044965109996623280493)
    ·
      refine ⟨18466141861916248733730185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49243044965109996623280493 18466141861916248733730185)
      ·
        refine ⟨13849606396437186550297639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18466141861916248733730185 13849606396437186550297639)
        ·
          refine ⟨20774409594655779825446459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13849606396437186550297639 20774409594655779825446459)
          ·
            refine ⟨31161614391983669738169689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20774409594655779825446459 31161614391983669738169689)
            ·
              refine ⟨23371210793987752303627267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31161614391983669738169689 23371210793987752303627267)
              ·
                refine ⟨35056816190981628455440901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23371210793987752303627267 35056816190981628455440901)
                ·
                  refine ⟨6573153035809055335395169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35056816190981628455440901 6573153035809055335395169)
                  ·
                    refine ⟨4929864776856791501546377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6573153035809055335395169 4929864776856791501546377)
                    ·
                      refine ⟨3697398582642593626159783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4929864776856791501546377 3697398582642593626159783)
                      ·
                        rfl

theorem cell23_7200658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7200658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200658 prefixEnd_7200658 := by exact prefixLift 7200658
  have htrace : WordTrace (prefixWord ++ tailWord_7200658) baseStart_7200658 baseEnd_7200658 := by
    simpa [prefixWord, tailWord_7200658, baseEnd_7200658] using wordTrace_append hprefix tailTrace_7200658
  have hstable : (prefixWord ++ tailWord_7200658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200658).length < 2 ^ (prefixWord ++ tailWord_7200658).sum := by decide
  have hdescent : baseEnd_7200658 < baseStart_7200658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200714 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_7200714 : Nat := 118140960795 + 7200714 * 2 ^ 59
def prefixEnd_7200714 : Nat := 4983230072969 + 3 ^ 40 * 7200714 * 2
def baseEnd_7200714 : Nat := 3697427337559245407059525

theorem tailTrace_7200714 : CollatzResearch.WordTrace tailWord_7200714 prefixEnd_7200714 3697427337559245407059525 := by
  unfold tailWord_7200714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65657903908762609222050299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175087743756700291258800797 65657903908762609222050299)
  ·
    refine ⟨98486855863143913833075449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65657903908762609222050299 98486855863143913833075449)
    ·
      refine ⟨73865141897357935374806587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98486855863143913833075449 73865141897357935374806587)
      ·
        refine ⟨110797712846036903062209881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73865141897357935374806587 110797712846036903062209881)
        ·
          refine ⟨83098284634527677296657411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110797712846036903062209881 83098284634527677296657411)
          ·
            refine ⟨124647426951791515944986117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83098284634527677296657411 124647426951791515944986117)
            ·
              refine ⟨23371392553460909239684897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124647426951791515944986117 23371392553460909239684897)
              ·
                refine ⟨17528544415095681929763673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23371392553460909239684897 17528544415095681929763673)
                ·
                  refine ⟨13146408311321761447322755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17528544415095681929763673 13146408311321761447322755)
                  ·
                    refine ⟨19719612466982642170984133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13146408311321761447322755 19719612466982642170984133)
                    ·
                      refine ⟨3697427337559245407059525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19719612466982642170984133 3697427337559245407059525)
                      ·
                        rfl

theorem cell23_7200714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_7200714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200714 prefixEnd_7200714 := by exact prefixLift 7200714
  have htrace : WordTrace (prefixWord ++ tailWord_7200714) baseStart_7200714 baseEnd_7200714 := by
    simpa [prefixWord, tailWord_7200714, baseEnd_7200714] using wordTrace_append hprefix tailTrace_7200714
  have hstable : (prefixWord ++ tailWord_7200714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200714).length < 2 ^ (prefixWord ++ tailWord_7200714).sum := by decide
  have hdescent : baseEnd_7200714 < baseStart_7200714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200821 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_7200821 : Nat := 118140960795 + 7200821 * 2 ^ 59
def prefixEnd_7200821 : Nat := 4983230072969 + 3 ^ 40 * 7200821 * 2
def baseEnd_7200821 : Nat := 3697482279989276488421533

theorem tailTrace_7200821 : CollatzResearch.WordTrace tailWord_7200821 prefixEnd_7200821 3697482279989276488421533 := by
  unfold tailWord_7200821
  simp only [CollatzResearch.WordTrace]
  refine ⟨262635518245662794162346317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175090345497108529441564211 262635518245662794162346317)
  ·
    refine ⟨98488319342123547810879869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262635518245662794162346317 98488319342123547810879869)
    ·
      refine ⟨36933119753296330429079951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98488319342123547810879869 36933119753296330429079951)
      ·
        refine ⟨55399679629944495643619927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36933119753296330429079951 55399679629944495643619927)
        ·
          refine ⟨83099519444916743465429891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55399679629944495643619927 83099519444916743465429891)
          ·
            refine ⟨124649279167375115198144837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83099519444916743465429891 124649279167375115198144837)
            ·
              refine ⟨23371739843882834099652157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124649279167375115198144837 23371739843882834099652157)
              ·
                refine ⟨8764402441456062787369559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23371739843882834099652157 8764402441456062787369559)
                ·
                  refine ⟨13146603662184094181054339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764402441456062787369559 13146603662184094181054339)
                  ·
                    refine ⟨19719905493276141271581509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13146603662184094181054339 19719905493276141271581509)
                    ·
                      refine ⟨3697482279989276488421533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19719905493276141271581509 3697482279989276488421533)
                      ·
                        rfl

theorem cell23_7200821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_7200821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200821 prefixEnd_7200821 := by exact prefixLift 7200821
  have htrace : WordTrace (prefixWord ++ tailWord_7200821) baseStart_7200821 baseEnd_7200821 := by
    simpa [prefixWord, tailWord_7200821, baseEnd_7200821] using wordTrace_append hprefix tailTrace_7200821
  have hstable : (prefixWord ++ tailWord_7200821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200821).length < 2 ^ (prefixWord ++ tailWord_7200821).sum := by decide
  have hdescent : baseEnd_7200821 < baseStart_7200821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200838 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7200838 : Nat := 118140960795 + 7200838 * 2 ^ 59
def prefixEnd_7200838 : Nat := 4983230072969 + 3 ^ 40 * 7200838 * 2
def baseEnd_7200838 : Nat := 3697491009160402921908955

theorem tailTrace_7200838 : CollatzResearch.WordTrace tailWord_7200838 prefixEnd_7200838 3697491009160402921908955 := by
  unfold tailWord_7200838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207379321456287689553599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175090758857734137377143445 8207379321456287689553599)
  ·
    refine ⟨12311068982184431534330399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8207379321456287689553599 12311068982184431534330399)
    ·
      refine ⟨18466603473276647301495599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12311068982184431534330399 18466603473276647301495599)
      ·
        refine ⟨27699905209914970952243399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18466603473276647301495599 27699905209914970952243399)
        ·
          refine ⟨41549857814872456428365099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27699905209914970952243399 41549857814872456428365099)
          ·
            refine ⟨62324786722308684642547649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41549857814872456428365099 62324786722308684642547649)
            ·
              refine ⟨46743590041731513481910737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62324786722308684642547649 46743590041731513481910737)
              ·
                refine ⟨35057692531298635111433053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46743590041731513481910737 35057692531298635111433053)
                ·
                  refine ⟨13146634699236988166787395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35057692531298635111433053 13146634699236988166787395)
                  ·
                    refine ⟨19719952048855482250181093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13146634699236988166787395 19719952048855482250181093)
                    ·
                      refine ⟨3697491009160402921908955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19719952048855482250181093 3697491009160402921908955)
                      ·
                        rfl

theorem cell23_7200838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7200838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200838 prefixEnd_7200838 := by exact prefixLift 7200838
  have htrace : WordTrace (prefixWord ++ tailWord_7200838) baseStart_7200838 baseEnd_7200838 := by
    simpa [prefixWord, tailWord_7200838, baseEnd_7200838] using wordTrace_append hprefix tailTrace_7200838
  have hstable : (prefixWord ++ tailWord_7200838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200838).length < 2 ^ (prefixWord ++ tailWord_7200838).sum := by decide
  have hdescent : baseEnd_7200838 < baseStart_7200838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200861 : List Nat := [1, 4, 4, 1, 1, 1, 2, 9]
def baseStart_7200861 : Nat := 118140960795 + 7200861 * 2 ^ 59
def prefixEnd_7200861 : Nat := 4983230072969 + 3 ^ 40 * 7200861 * 2
def baseEnd_7200861 : Nat := 136944548859831715997087

theorem tailTrace_7200861 : CollatzResearch.WordTrace tailWord_7200861 prefixEnd_7200861 136944548859831715997087 := by
  unfold tailWord_7200861
  simp only [CollatzResearch.WordTrace]
  refine ⟨262636977165517880993802437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175091318110345253995868291 262636977165517880993802437)
  ·
    refine ⟨49244433218534602686337957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262636977165517880993802437 49244433218534602686337957)
    ·
      refine ⟨9233331228475238003688367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49244433218534602686337957 9233331228475238003688367)
      ·
        refine ⟨13849996842712857005532551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9233331228475238003688367 13849996842712857005532551)
        ·
          refine ⟨20774995264069285508298827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13849996842712857005532551 20774995264069285508298827)
          ·
            refine ⟨31162492896103928262448241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20774995264069285508298827 31162492896103928262448241)
            ·
              refine ⟨23371869672077946196836181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31162492896103928262448241 23371869672077946196836181)
              ·
                refine ⟨136944548859831715997087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23371869672077946196836181 136944548859831715997087)
                ·
                  rfl

theorem cell23_7200861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 9].length) (baseStart_7200861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200861 prefixEnd_7200861 := by exact prefixLift 7200861
  have htrace : WordTrace (prefixWord ++ tailWord_7200861) baseStart_7200861 baseEnd_7200861 := by
    simpa [prefixWord, tailWord_7200861, baseEnd_7200861] using wordTrace_append hprefix tailTrace_7200861
  have hstable : (prefixWord ++ tailWord_7200861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200861).length < 2 ^ (prefixWord ++ tailWord_7200861).sum := by decide
  have hdescent : baseEnd_7200861 < baseStart_7200861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200871 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_7200871 : Nat := 118140960795 + 7200871 * 2 ^ 59
def prefixEnd_7200871 : Nat := 4983230072969 + 3 ^ 40 * 7200871 * 2
def baseEnd_7200871 : Nat := 3697507954022001292796303

theorem tailTrace_7200871 : CollatzResearch.WordTrace tailWord_7200871 prefixEnd_7200871 3697507954022001292796303 := by
  unfold tailWord_7200871
  simp only [CollatzResearch.WordTrace]
  refine ⟨262637341895481652701666467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175091561263654435134444311 262637341895481652701666467)
  ·
    refine ⟨393956012843222479052499701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262637341895481652701666467 393956012843222479052499701)
    ·
      refine ⟨36933376204052107411171847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 393956012843222479052499701 36933376204052107411171847)
      ·
        refine ⟨55400064306078161116757771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36933376204052107411171847 55400064306078161116757771)
        ·
          refine ⟨83100096459117241675136657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55400064306078161116757771 83100096459117241675136657)
          ·
            refine ⟨62325072344337931256352493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83100096459117241675136657 62325072344337931256352493)
            ·
              refine ⟨23371902129126724221132185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62325072344337931256352493 23371902129126724221132185)
              ·
                refine ⟨17528926596845043165849139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23371902129126724221132185 17528926596845043165849139)
                ·
                  refine ⟨26293389895267564748773709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17528926596845043165849139 26293389895267564748773709)
                  ·
                    refine ⟨9860021210725336780790141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26293389895267564748773709 9860021210725336780790141)
                    ·
                      refine ⟨3697507954022001292796303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9860021210725336780790141 3697507954022001292796303)
                      ·
                        rfl

theorem cell23_7200871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_7200871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200871 prefixEnd_7200871 := by exact prefixLift 7200871
  have htrace : WordTrace (prefixWord ++ tailWord_7200871) baseStart_7200871 baseEnd_7200871 := by
    simpa [prefixWord, tailWord_7200871, baseEnd_7200871] using wordTrace_append hprefix tailTrace_7200871
  have hstable : (prefixWord ++ tailWord_7200871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200871).length < 2 ^ (prefixWord ++ tailWord_7200871).sum := by decide
  have hdescent : baseEnd_7200871 < baseStart_7200871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200889 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 1, 2, 2]
def baseStart_7200889 : Nat := 118140960795 + 7200889 * 2 ^ 59
def prefixEnd_7200889 : Nat := 4983230072969 + 3 ^ 40 * 7200889 * 2
def baseEnd_7200889 : Nat := 3697517196673782222371221

theorem tailTrace_7200889 : CollatzResearch.WordTrace tailWord_7200889 prefixEnd_7200889 3697517196673782222371221 := by
  unfold tailWord_7200889
  simp only [CollatzResearch.WordTrace]
  refine ⟨262637998409416441775821721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175091998939610961183881147 262637998409416441775821721)
  ·
    refine ⟨196978498807062331331866291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262637998409416441775821721 196978498807062331331866291)
    ·
      refine ⟨295467748210593496997799437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196978498807062331331866291 295467748210593496997799437)
      ·
        refine ⟨110800405578972561374174789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295467748210593496997799437 110800405578972561374174789)
        ·
          refine ⟨20775076046057355257657773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110800405578972561374174789 20775076046057355257657773)
          ·
            refine ⟨7790653517271508221621665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20775076046057355257657773 7790653517271508221621665)
            ·
              refine ⟨5842990137953631166216249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7790653517271508221621665 5842990137953631166216249)
              ·
                refine ⟨4382242603465223374662187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5842990137953631166216249 4382242603465223374662187)
                ·
                  refine ⟨6573363905197835061993281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382242603465223374662187 6573363905197835061993281)
                  ·
                    refine ⟨4930022928898376296494961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6573363905197835061993281 4930022928898376296494961)
                    ·
                      refine ⟨3697517196673782222371221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930022928898376296494961 3697517196673782222371221)
                      ·
                        rfl

theorem cell23_7200889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_7200889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200889 prefixEnd_7200889 := by exact prefixLift 7200889
  have htrace : WordTrace (prefixWord ++ tailWord_7200889) baseStart_7200889 baseEnd_7200889 := by
    simpa [prefixWord, tailWord_7200889, baseEnd_7200889] using wordTrace_append hprefix tailTrace_7200889
  have hstable : (prefixWord ++ tailWord_7200889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200889).length < 2 ^ (prefixWord ++ tailWord_7200889).sum := by decide
  have hdescent : baseEnd_7200889 < baseStart_7200889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200928 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2]
def baseStart_7200928 : Nat := 118140960795 + 7200928 * 2 ^ 59
def prefixEnd_7200928 : Nat := 4983230072969 + 3 ^ 40 * 7200928 * 2
def baseEnd_7200928 : Nat := 3697537222419307569783541

theorem tailTrace_7200928 : CollatzResearch.WordTrace tailWord_7200928 prefixEnd_7200928 3697537222419307569783541 := by
  unfold tailWord_7200928
  simp only [CollatzResearch.WordTrace]
  refine ⟨131319710428137575718245719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175092947237516767624327625 131319710428137575718245719)
  ·
    refine ⟨196979565642206363577368579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131319710428137575718245719 196979565642206363577368579)
    ·
      refine ⟨295469348463309545366052869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196979565642206363577368579 295469348463309545366052869)
      ·
        refine ⟨55400502836870539756134913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295469348463309545366052869 55400502836870539756134913)
        ·
          refine ⟨41550377127652904817101185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55400502836870539756134913 41550377127652904817101185)
          ·
            refine ⟨31162782845739678612825889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41550377127652904817101185 31162782845739678612825889)
            ·
              refine ⟨23372087134304758959619417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31162782845739678612825889 23372087134304758959619417)
              ·
                refine ⟨17529065350728569219714563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23372087134304758959619417 17529065350728569219714563)
                ·
                  refine ⟨26293598026092853829571845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17529065350728569219714563 26293598026092853829571845)
                  ·
                    refine ⟨4930049629892410093044721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26293598026092853829571845 4930049629892410093044721)
                    ·
                      refine ⟨3697537222419307569783541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930049629892410093044721 3697537222419307569783541)
                      ·
                        rfl

theorem cell23_7200928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_7200928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200928 prefixEnd_7200928 := by exact prefixLift 7200928
  have htrace : WordTrace (prefixWord ++ tailWord_7200928) baseStart_7200928 baseEnd_7200928 := by
    simpa [prefixWord, tailWord_7200928, baseEnd_7200928] using wordTrace_append hprefix tailTrace_7200928
  have hstable : (prefixWord ++ tailWord_7200928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200928).length < 2 ^ (prefixWord ++ tailWord_7200928).sum := by decide
  have hdescent : baseEnd_7200928 < baseStart_7200928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7200951 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 7]
def baseStart_7200951 : Nat := 118140960795 + 7200951 * 2 ^ 59
def prefixEnd_7200951 : Nat := 4983230072969 + 3 ^ 40 * 7200951 * 2
def baseEnd_7200951 : Nat := 410838781386040108866215

theorem tailTrace_7200951 : CollatzResearch.WordTrace tailWord_7200951 prefixEnd_7200951 410838781386040108866215 := by
  unfold tailWord_7200951
  simp only [CollatzResearch.WordTrace]
  refine ⟨262640259735191826364578707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175093506490127884243052471 262640259735191826364578707)
  ·
    refine ⟨393960389602787739546868061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262640259735191826364578707 393960389602787739546868061)
    ·
      refine ⟨147735146101045402330075523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393960389602787739546868061 147735146101045402330075523)
      ·
        refine ⟨221602719151568103495113285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147735146101045402330075523 221602719151568103495113285)
        ·
          refine ⟨41550509840919019405333741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221602719151568103495113285 41550509840919019405333741)
          ·
            refine ⟨15581441190344632277000153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41550509840919019405333741 15581441190344632277000153)
            ·
              refine ⟨11686080892758474207750115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15581441190344632277000153 11686080892758474207750115)
              ·
                refine ⟨17529121339137711311625173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686080892758474207750115 17529121339137711311625173)
                ·
                  refine ⟨410838781386040108866215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17529121339137711311625173 410838781386040108866215)
                  ·
                    rfl

theorem cell23_7200951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 7].length) (baseStart_7200951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7200951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7200951 prefixEnd_7200951 := by exact prefixLift 7200951
  have htrace : WordTrace (prefixWord ++ tailWord_7200951) baseStart_7200951 baseEnd_7200951 := by
    simpa [prefixWord, tailWord_7200951, baseEnd_7200951] using wordTrace_append hprefix tailTrace_7200951
  have hstable : (prefixWord ++ tailWord_7200951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7200951).length < 2 ^ (prefixWord ++ tailWord_7200951).sum := by decide
  have hdescent : baseEnd_7200951 < baseStart_7200951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7200951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201001 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_7201001 : Nat := 118140960795 + 7201001 * 2 ^ 59
def prefixEnd_7201001 : Nat := 4983230072969 + 3 ^ 40 * 7201001 * 2
def baseEnd_7201001 : Nat := 3697574706507085784170705

theorem tailTrace_7201001 : CollatzResearch.WordTrace tailWord_7201001 prefixEnd_7201001 3697574706507085784170705 := by
  unfold tailWord_7201001
  simp only [CollatzResearch.WordTrace]
  refine ⟨262642083385010684903898857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175094722256673789935932571 262642083385010684903898857)
  ·
    refine ⟨196981562538758013677924143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262642083385010684903898857 196981562538758013677924143)
    ·
      refine ⟨295472343808137020516886215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196981562538758013677924143 295472343808137020516886215)
      ·
        refine ⟨443208515712205530775329323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295472343808137020516886215 443208515712205530775329323)
        ·
          refine ⟨664812773568308296162993985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443208515712205530775329323 664812773568308296162993985)
          ·
            refine ⟨498609580176231222122245489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664812773568308296162993985 498609580176231222122245489)
            ·
              refine ⟨373957185132173416591684117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498609580176231222122245489 373957185132173416591684117)
              ·
                refine ⟨17529243053070628902735193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373957185132173416591684117 17529243053070628902735193)
                ·
                  refine ⟨13146932289802971677051395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17529243053070628902735193 13146932289802971677051395)
                  ·
                    refine ⟨19720398434704457515577093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13146932289802971677051395 19720398434704457515577093)
                    ·
                      refine ⟨3697574706507085784170705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19720398434704457515577093 3697574706507085784170705)
                      ·
                        rfl

theorem cell23_7201001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_7201001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201001 prefixEnd_7201001 := by exact prefixLift 7201001
  have htrace : WordTrace (prefixWord ++ tailWord_7201001) baseStart_7201001 baseEnd_7201001 := by
    simpa [prefixWord, tailWord_7201001, baseEnd_7201001] using wordTrace_append hprefix tailTrace_7201001
  have hstable : (prefixWord ++ tailWord_7201001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201001).length < 2 ^ (prefixWord ++ tailWord_7201001).sum := by decide
  have hdescent : baseEnd_7201001 < baseStart_7201001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201021 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_7201021 : Nat := 118140960795 + 7201021 * 2 ^ 59
def prefixEnd_7201021 : Nat := 4983230072969 + 3 ^ 40 * 7201021 * 2
def baseEnd_7201021 : Nat := 3697584976120175705920613

theorem tailTrace_7201021 : CollatzResearch.WordTrace tailWord_7201021 prefixEnd_7201021 3697584976120175705920613 := by
  unfold tailWord_7201021
  simp only [CollatzResearch.WordTrace]
  refine ⟨262642812844938228319626917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175095208563292152213084611 262642812844938228319626917)
  ·
    refine ⟨49245527408425917809930047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262642812844938228319626917 49245527408425917809930047)
    ·
      refine ⟨73868291112638876714895071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49245527408425917809930047 73868291112638876714895071)
      ·
        refine ⟨110802436668958315072342607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73868291112638876714895071 110802436668958315072342607)
        ·
          refine ⟨166203655003437472608513911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110802436668958315072342607 166203655003437472608513911)
          ·
            refine ⟨249305482505156208912770867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166203655003437472608513911 249305482505156208912770867)
            ·
              refine ⟨373958223757734313369156301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249305482505156208912770867 373958223757734313369156301)
              ·
                refine ⟨140234333909150367513433613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373958223757734313369156301 140234333909150367513433613)
                ·
                  refine ⟨52587875215931387817537605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140234333909150367513433613 52587875215931387817537605)
                  ·
                    refine ⟨9860226602987135215788301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52587875215931387817537605 9860226602987135215788301)
                    ·
                      refine ⟨3697584976120175705920613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9860226602987135215788301 3697584976120175705920613)
                      ·
                        rfl

theorem cell23_7201021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_7201021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201021 prefixEnd_7201021 := by exact prefixLift 7201021
  have htrace : WordTrace (prefixWord ++ tailWord_7201021) baseStart_7201021 baseEnd_7201021 := by
    simpa [prefixWord, tailWord_7201021, baseEnd_7201021] using wordTrace_append hprefix tailTrace_7201021
  have hstable : (prefixWord ++ tailWord_7201021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201021).length < 2 ^ (prefixWord ++ tailWord_7201021).sum := by decide
  have hdescent : baseEnd_7201021 < baseStart_7201021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201058 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7201058 : Nat := 118140960795 + 7201058 * 2 ^ 59
def prefixEnd_7201058 : Nat := 4983230072969 + 3 ^ 40 * 7201058 * 2
def baseEnd_7201058 : Nat := 410844886100488006795327

theorem tailTrace_7201058 : CollatzResearch.WordTrace tailWord_7201058 prefixEnd_7201058 410844886100488006795327 := by
  unfold tailWord_7201058
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661040586451045909680957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175096108230536122425815885 65661040586451045909680957)
  ·
    refine ⟨24622890219919142216130359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65661040586451045909680957 24622890219919142216130359)
    ·
      refine ⟨36934335329878713324195539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24622890219919142216130359 36934335329878713324195539)
      ·
        refine ⟨55401502994818069986293309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36934335329878713324195539 55401502994818069986293309)
        ·
          refine ⟨20775563623056776244859991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55401502994818069986293309 20775563623056776244859991)
          ·
            refine ⟨31163345434585164367289987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20775563623056776244859991 31163345434585164367289987)
            ·
              refine ⟨46745018151877746550934981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31163345434585164367289987 46745018151877746550934981)
              ·
                refine ⟨8764690903477077478300309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46745018151877746550934981 8764690903477077478300309)
                ·
                  refine ⟨410844886100488006795327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8764690903477077478300309 410844886100488006795327)
                  ·
                    rfl

theorem cell23_7201058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7201058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201058 prefixEnd_7201058 := by exact prefixLift 7201058
  have htrace : WordTrace (prefixWord ++ tailWord_7201058) baseStart_7201058 baseEnd_7201058 := by
    simpa [prefixWord, tailWord_7201058, baseEnd_7201058] using wordTrace_append hprefix tailTrace_7201058
  have hstable : (prefixWord ++ tailWord_7201058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201058).length < 2 ^ (prefixWord ++ tailWord_7201058).sum := by decide
  have hdescent : baseEnd_7201058 < baseStart_7201058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201071 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 3, 5]
def baseStart_7201071 : Nat := 118140960795 + 7201071 * 2 ^ 59
def prefixEnd_7201071 : Nat := 4983230072969 + 3 ^ 40 * 7201071 * 2
def baseEnd_7201071 : Nat := 1232536883384300170098461

theorem tailTrace_7201071 : CollatzResearch.WordTrace tailWord_7201071 prefixEnd_7201071 1232536883384300170098461 := by
  unfold tailWord_7201071
  simp only [CollatzResearch.WordTrace]
  refine ⟨262644636494757086858947067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175096424329838057905964711 262644636494757086858947067)
  ·
    refine ⟨393966954742135630288420601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262644636494757086858947067 393966954742135630288420601)
    ·
      refine ⟨295475216056601722716315451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393966954742135630288420601 295475216056601722716315451)
      ·
        refine ⟨443212824084902584074473177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295475216056601722716315451 443212824084902584074473177)
        ·
          refine ⟨332409618063676938055854883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443212824084902584074473177 332409618063676938055854883)
          ·
            refine ⟨498614427095515407083782325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332409618063676938055854883 498614427095515407083782325)
            ·
              refine ⟨46745102540204569414104593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 498614427095515407083782325 46745102540204569414104593)
              ·
                refine ⟨35058826905153427060578445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46745102540204569414104593 35058826905153427060578445)
                ·
                  refine ⟨13147060089432535147716917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35058826905153427060578445 13147060089432535147716917)
                  ·
                    refine ⟨1232536883384300170098461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13147060089432535147716917 1232536883384300170098461)
                    ·
                      rfl

theorem cell23_7201071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_7201071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201071 prefixEnd_7201071 := by exact prefixLift 7201071
  have htrace : WordTrace (prefixWord ++ tailWord_7201071) baseStart_7201071 baseEnd_7201071 := by
    simpa [prefixWord, tailWord_7201071, baseEnd_7201071] using wordTrace_append hprefix tailTrace_7201071
  have hstable : (prefixWord ++ tailWord_7201071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201071).length < 2 ^ (prefixWord ++ tailWord_7201071).sum := by decide
  have hdescent : baseEnd_7201071 < baseStart_7201071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201089 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7201089 : Nat := 118140960795 + 7201089 * 2 ^ 59
def prefixEnd_7201089 : Nat := 4983230072969 + 3 ^ 40 * 7201089 * 2
def baseEnd_7201089 : Nat := 3697619892804681439870301

theorem tailTrace_7201089 : CollatzResearch.WordTrace tailWord_7201089 prefixEnd_7201089 3697619892804681439870301 := by
  unfold tailWord_7201089
  simp only [CollatzResearch.WordTrace]
  refine ⟨262645293008691875933102321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175096862005794583955401547 262645293008691875933102321)
  ·
    refine ⟨196983969756518906949826741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262645293008691875933102321 196983969756518906949826741)
    ·
      refine ⟨18467247164673647526546257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196983969756518906949826741 18467247164673647526546257)
      ·
        refine ⟨13850435373505235644909693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18467247164673647526546257 13850435373505235644909693)
        ·
          refine ⟨5193913265064463366841135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13850435373505235644909693 5193913265064463366841135)
          ·
            refine ⟨7790869897596695050261703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193913265064463366841135 7790869897596695050261703)
            ·
              refine ⟨11686304846395042575392555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7790869897596695050261703 11686304846395042575392555)
              ·
                refine ⟨17529457269592563863088833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686304846395042575392555 17529457269592563863088833)
                ·
                  refine ⟨13147092952194422897316625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17529457269592563863088833 13147092952194422897316625)
                  ·
                    refine ⟨9860319714145817172987469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13147092952194422897316625 9860319714145817172987469)
                    ·
                      refine ⟨3697619892804681439870301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9860319714145817172987469 3697619892804681439870301)
                      ·
                        rfl

theorem cell23_7201089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7201089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201089 prefixEnd_7201089 := by exact prefixLift 7201089
  have htrace : WordTrace (prefixWord ++ tailWord_7201089) baseStart_7201089 baseEnd_7201089 := by
    simpa [prefixWord, tailWord_7201089, baseEnd_7201089] using wordTrace_append hprefix tailTrace_7201089
  have hstable : (prefixWord ++ tailWord_7201089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201089).length < 2 ^ (prefixWord ++ tailWord_7201089).sum := by decide
  have hdescent : baseEnd_7201089 < baseStart_7201089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201105 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 1, 5]
def baseStart_7201105 : Nat := 118140960795 + 7201105 * 2 ^ 59
def prefixEnd_7201105 : Nat := 4983230072969 + 3 ^ 40 * 7201105 * 2
def baseEnd_7201105 : Nat := 1232542702831717792423409

theorem tailTrace_7201105 : CollatzResearch.WordTrace tailWord_7201105 prefixEnd_7201105 1232542702831717792423409 := by
  unfold tailWord_7201105
  simp only [CollatzResearch.WordTrace]
  refine ⟨262645876576633910665684769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175097251051089273777123179 262645876576633910665684769)
  ·
    refine ⟨196984407432475432999263577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262645876576633910665684769 196984407432475432999263577)
    ·
      refine ⟨147738305574356574749447683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196984407432475432999263577 147738305574356574749447683)
      ·
        refine ⟨221607458361534862124171525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147738305574356574749447683 221607458361534862124171525)
        ·
          refine ⟨41551398442787786648282161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221607458361534862124171525 41551398442787786648282161)
          ·
            refine ⟨31163548832090839986211621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41551398442787786648282161 31163548832090839986211621)
            ·
              refine ⟨5843165406017032497414679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31163548832090839986211621 5843165406017032497414679)
              ·
                refine ⟨8764748109025548746122019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843165406017032497414679 8764748109025548746122019)
                ·
                  refine ⟨13147122163538323119183029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8764748109025548746122019 13147122163538323119183029)
                  ·
                    refine ⟨1232542702831717792423409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13147122163538323119183029 1232542702831717792423409)
                    ·
                      rfl

theorem cell23_7201105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_7201105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201105 prefixEnd_7201105 := by exact prefixLift 7201105
  have htrace : WordTrace (prefixWord ++ tailWord_7201105) baseStart_7201105 baseEnd_7201105 := by
    simpa [prefixWord, tailWord_7201105, baseEnd_7201105] using wordTrace_append hprefix tailTrace_7201105
  have hstable : (prefixWord ++ tailWord_7201105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201105).length < 2 ^ (prefixWord ++ tailWord_7201105).sum := by decide
  have hdescent : baseEnd_7201105 < baseStart_7201105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201121 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7201121 : Nat := 118140960795 + 7201121 * 2 ^ 59
def prefixEnd_7201121 : Nat := 4983230072969 + 3 ^ 40 * 7201121 * 2
def baseEnd_7201121 : Nat := 3697636324185625314670153

theorem tailTrace_7201121 : CollatzResearch.WordTrace tailWord_7201121 prefixEnd_7201121 3697636324185625314670153 := by
  unfold tailWord_7201121
  simp only [CollatzResearch.WordTrace]
  refine ⟨262646460144575945398267217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175097640096383963598844811 262646460144575945398267217)
  ·
    refine ⟨196984845108431959048700413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262646460144575945398267217 196984845108431959048700413)
    ·
      refine ⟨73869316915661984643262655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196984845108431959048700413 73869316915661984643262655)
      ·
        refine ⟨110803975373492976964893983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73869316915661984643262655 110803975373492976964893983)
        ·
          refine ⟨166205963060239465447340975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110803975373492976964893983 166205963060239465447340975)
          ·
            refine ⟨249308944590359198171011463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166205963060239465447340975 249308944590359198171011463)
            ·
              refine ⟨373963416885538797256517195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249308944590359198171011463 373963416885538797256517195)
              ·
                refine ⟨560945125328308195884775793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373963416885538797256517195 560945125328308195884775793)
                ·
                  refine ⟨420708843996231146913581845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560945125328308195884775793 420708843996231146913581845)
                  ·
                    refine ⟨19720727062323335011574149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 420708843996231146913581845 19720727062323335011574149)
                    ·
                      refine ⟨3697636324185625314670153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19720727062323335011574149 3697636324185625314670153)
                      ·
                        rfl

theorem cell23_7201121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7201121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201121 prefixEnd_7201121 := by exact prefixLift 7201121
  have htrace : WordTrace (prefixWord ++ tailWord_7201121) baseStart_7201121 baseEnd_7201121 := by
    simpa [prefixWord, tailWord_7201121, baseEnd_7201121] using wordTrace_append hprefix tailTrace_7201121
  have hstable : (prefixWord ++ tailWord_7201121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201121).length < 2 ^ (prefixWord ++ tailWord_7201121).sum := by decide
  have hdescent : baseEnd_7201121 < baseStart_7201121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201128 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7201128 : Nat := 118140960795 + 7201128 * 2 ^ 59
def prefixEnd_7201128 : Nat := 4983230072969 + 3 ^ 40 * 7201128 * 2
def baseEnd_7201128 : Nat := 3697639918550206787282621

theorem tailTrace_7201128 : CollatzResearch.WordTrace tailWord_7201128 prefixEnd_7201128 3697639918550206787282621 := by
  unfold tailWord_7201128
  simp only [CollatzResearch.WordTrace]
  refine ⟨131323357727775292796886019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175097810303700390395848025 131323357727775292796886019)
  ·
    refine ⟨196985036591662939195329029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131323357727775292796886019 196985036591662939195329029)
    ·
      refine ⟨36934694360936801099124193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196985036591662939195329029 36934694360936801099124193)
      ·
        refine ⟨27701020770702600824343145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36934694360936801099124193 27701020770702600824343145)
        ·
          refine ⟨20775765578026950618257359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27701020770702600824343145 20775765578026950618257359)
          ·
            refine ⟨31163648367040425927386039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20775765578026950618257359 31163648367040425927386039)
            ·
              refine ⟨46745472550560638891079059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31163648367040425927386039 46745472550560638891079059)
              ·
                refine ⟨70118208825840958336618589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46745472550560638891079059 70118208825840958336618589)
                ·
                  refine ⟨26294328309690359376231971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70118208825840958336618589 26294328309690359376231971)
                  ·
                    refine ⟨39441492464535539064347957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26294328309690359376231971 39441492464535539064347957)
                    ·
                      refine ⟨3697639918550206787282621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39441492464535539064347957 3697639918550206787282621)
                      ·
                        rfl

theorem cell23_7201128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7201128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201128 prefixEnd_7201128 := by exact prefixLift 7201128
  have htrace : WordTrace (prefixWord ++ tailWord_7201128) baseStart_7201128 baseEnd_7201128 := by
    simpa [prefixWord, tailWord_7201128, baseEnd_7201128] using wordTrace_append hprefix tailTrace_7201128
  have hstable : (prefixWord ++ tailWord_7201128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201128).length < 2 ^ (prefixWord ++ tailWord_7201128).sum := by decide
  have hdescent : baseEnd_7201128 < baseStart_7201128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201138 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7201138 : Nat := 118140960795 + 7201138 * 2 ^ 59
def prefixEnd_7201138 : Nat := 4983230072969 + 3 ^ 40 * 7201138 * 2
def baseEnd_7201138 : Nat := 3697645053356751748157575

theorem tailTrace_7201138 : CollatzResearch.WordTrace tailWord_7201138 prefixEnd_7201138 3697645053356751748157575 := by
  unfold tailWord_7201138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661770046378589325409017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175098053457009571534424045 65661770046378589325409017)
  ·
    refine ⟨49246327534783941994056763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65661770046378589325409017 49246327534783941994056763)
    ·
      refine ⟨73869491302175912991085145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49246327534783941994056763 73869491302175912991085145)
      ·
        refine ⟨55402118476631934743313859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73869491302175912991085145 55402118476631934743313859)
        ·
          refine ⟨83103177714947902114970789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55402118476631934743313859 83103177714947902114970789)
          ·
            refine ⟨15581845821552731646557023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83103177714947902114970789 15581845821552731646557023)
            ·
              refine ⟨23372768732329097469835535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15581845821552731646557023 23372768732329097469835535)
              ·
                refine ⟨35059153098493646204753303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23372768732329097469835535 35059153098493646204753303)
                ·
                  refine ⟨52588729647740469307129955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35059153098493646204753303 52588729647740469307129955)
                  ·
                    refine ⟨78883094471610703960694933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52588729647740469307129955 78883094471610703960694933)
                    ·
                      refine ⟨3697645053356751748157575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78883094471610703960694933 3697645053356751748157575)
                      ·
                        rfl

theorem cell23_7201138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7201138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201138 prefixEnd_7201138 := by exact prefixLift 7201138
  have htrace : WordTrace (prefixWord ++ tailWord_7201138) baseStart_7201138 baseEnd_7201138 := by
    simpa [prefixWord, tailWord_7201138, baseEnd_7201138] using wordTrace_append hprefix tailTrace_7201138
  have hstable : (prefixWord ++ tailWord_7201138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201138).length < 2 ^ (prefixWord ++ tailWord_7201138).sum := by decide
  have hdescent : baseEnd_7201138 < baseStart_7201138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201162 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7201162 : Nat := 118140960795 + 7201162 * 2 ^ 59
def prefixEnd_7201162 : Nat := 4983230072969 + 3 ^ 40 * 7201162 * 2
def baseEnd_7201162 : Nat := 3697657376892459654257465

theorem tailTrace_7201162 : CollatzResearch.WordTrace tailWord_7201162 prefixEnd_7201162 3697657376892459654257465 := by
  unfold tailWord_7201162
  simp only [CollatzResearch.WordTrace]
  refine ⟨65661988884356852350127435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175098637024951606267006493 65661988884356852350127435)
  ·
    refine ⟨98492983326535278525191153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65661988884356852350127435 98492983326535278525191153)
    ·
      refine ⟨73869737494901458893893365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98492983326535278525191153 73869737494901458893893365)
      ·
        refine ⟨6925287890147011771302503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73869737494901458893893365 6925287890147011771302503)
        ·
          refine ⟨10387931835220517656953755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6925287890147011771302503 10387931835220517656953755)
          ·
            refine ⟨15581897752830776485430633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10387931835220517656953755 15581897752830776485430633)
            ·
              refine ⟨11686423314623082364072975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15581897752830776485430633 11686423314623082364072975)
              ·
                refine ⟨17529634971934623546109463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686423314623082364072975 17529634971934623546109463)
                ·
                  refine ⟨26294452457901935319164195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17529634971934623546109463 26294452457901935319164195)
                  ·
                    refine ⟨39441678686852902978746293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26294452457901935319164195 39441678686852902978746293)
                    ·
                      refine ⟨3697657376892459654257465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39441678686852902978746293 3697657376892459654257465)
                      ·
                        rfl

theorem cell23_7201162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7201162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201162 prefixEnd_7201162 := by exact prefixLift 7201162
  have htrace : WordTrace (prefixWord ++ tailWord_7201162) baseStart_7201162 baseEnd_7201162 := by
    simpa [prefixWord, tailWord_7201162, baseEnd_7201162] using wordTrace_append hprefix tailTrace_7201162
  have hstable : (prefixWord ++ tailWord_7201162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201162).length < 2 ^ (prefixWord ++ tailWord_7201162).sum := by decide
  have hdescent : baseEnd_7201162 < baseStart_7201162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201175 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_7201175 : Nat := 118140960795 + 7201175 * 2 ^ 59
def prefixEnd_7201175 : Nat := 4983230072969 + 3 ^ 40 * 7201175 * 2
def baseEnd_7201175 : Nat := 3697664052140968103394905

theorem tailTrace_7201175 : CollatzResearch.WordTrace tailWord_7201175 prefixEnd_7201175 3697664052140968103394905 := by
  unfold tailWord_7201175
  simp only [CollatzResearch.WordTrace]
  refine ⟨262648429686380312620732979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175098953124253541747155319 262648429686380312620732979)
  ·
    refine ⟨393972644529570468931099469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262648429686380312620732979 393972644529570468931099469)
    ·
      refine ⟨147739741698588925849162301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393972644529570468931099469 147739741698588925849162301)
      ·
        refine ⟨55402403136970847193435863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147739741698588925849162301 55402403136970847193435863)
        ·
          refine ⟨83103604705456270790153795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55402403136970847193435863 83103604705456270790153795)
          ·
            refine ⟨124655407058184406185230693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83103604705456270790153795 124655407058184406185230693)
            ·
              refine ⟨23372888823409576159730755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124655407058184406185230693 23372888823409576159730755)
              ·
                refine ⟨35059333235114364239596133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23372888823409576159730755 35059333235114364239596133)
                ·
                  refine ⟨6573624981583943294924275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35059333235114364239596133 6573624981583943294924275)
                  ·
                    refine ⟨9860437472375914942386413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6573624981583943294924275 9860437472375914942386413)
                    ·
                      refine ⟨3697664052140968103394905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9860437472375914942386413 3697664052140968103394905)
                      ·
                        rfl

theorem cell23_7201175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_7201175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201175 prefixEnd_7201175 := by exact prefixLift 7201175
  have htrace : WordTrace (prefixWord ++ tailWord_7201175) baseStart_7201175 baseEnd_7201175 := by
    simpa [prefixWord, tailWord_7201175, baseEnd_7201175] using wordTrace_append hprefix tailTrace_7201175
  have hstable : (prefixWord ++ tailWord_7201175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201175).length < 2 ^ (prefixWord ++ tailWord_7201175).sum := by decide
  have hdescent : baseEnd_7201175 < baseStart_7201175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201245 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7201245 : Nat := 118140960795 + 7201245 * 2 ^ 59
def prefixEnd_7201245 : Nat := 4983230072969 + 3 ^ 40 * 7201245 * 2
def baseEnd_7201245 : Nat := 3697699995786782829519583

theorem tailTrace_7201245 : CollatzResearch.WordTrace tailWord_7201245 prefixEnd_7201245 3697699995786782829519583 := by
  unfold tailWord_7201245
  simp only [CollatzResearch.WordTrace]
  refine ⟨262650982796126714575781189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175100655197417809717187459 262650982796126714575781189)
  ·
    refine ⟨49247059274273758982958973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262650982796126714575781189 49247059274273758982958973)
    ·
      refine ⟨18467647227852659618609615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49247059274273758982958973 18467647227852659618609615)
      ·
        refine ⟨27701470841778989427914423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18467647227852659618609615 27701470841778989427914423)
        ·
          refine ⟨41552206262668484141871635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27701470841778989427914423 41552206262668484141871635)
          ·
            refine ⟨62328309394002726212807453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41552206262668484141871635 62328309394002726212807453)
            ·
              refine ⟨23373116022751022329802795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62328309394002726212807453 23373116022751022329802795)
              ·
                refine ⟨35059674034126533494704193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23373116022751022329802795 35059674034126533494704193)
                ·
                  refine ⟨26294755525594900121028145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35059674034126533494704193 26294755525594900121028145)
                  ·
                    refine ⟨19721066644196175090771109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26294755525594900121028145 19721066644196175090771109)
                    ·
                      refine ⟨3697699995786782829519583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19721066644196175090771109 3697699995786782829519583)
                      ·
                        rfl

theorem cell23_7201245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7201245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201245 prefixEnd_7201245 := by exact prefixLift 7201245
  have htrace : WordTrace (prefixWord ++ tailWord_7201245) baseStart_7201245 baseEnd_7201245 := by
    simpa [prefixWord, tailWord_7201245, baseEnd_7201245] using wordTrace_append hprefix tailTrace_7201245
  have hstable : (prefixWord ++ tailWord_7201245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201245).length < 2 ^ (prefixWord ++ tailWord_7201245).sum := by decide
  have hdescent : baseEnd_7201245 < baseStart_7201245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201328 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 8]
def baseStart_7201328 : Nat := 118140960795 + 7201328 * 2 ^ 59
def prefixEnd_7201328 : Nat := 4983230072969 + 3 ^ 40 * 7201328 * 2
def baseEnd_7201328 : Nat := 410860290520122889420189

theorem tailTrace_7201328 : CollatzResearch.WordTrace tailWord_7201328 prefixEnd_7201328 410860290520122889420189 := by
  unfold tailWord_7201328
  simp only [CollatzResearch.WordTrace]
  refine ⟨131327005027413009875526319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175102673369884013167368425 131327005027413009875526319)
  ·
    refine ⟨196990507541119514813289479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131327005027413009875526319 196990507541119514813289479)
    ·
      refine ⟨295485761311679272219934219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196990507541119514813289479 295485761311679272219934219)
      ·
        refine ⟨443228641967518908329901329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295485761311679272219934219 443228641967518908329901329)
        ·
          refine ⟨332421481475639181247425997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443228641967518908329901329 332421481475639181247425997)
          ·
            refine ⟨124658055553364692967784749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332421481475639181247425997 124658055553364692967784749)
            ·
              refine ⟨46746770832511759862919281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124658055553364692967784749 46746770832511759862919281)
              ·
                refine ⟨35060078124383819897189461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46746770832511759862919281 35060078124383819897189461)
                ·
                  refine ⟨410860290520122889420189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35060078124383819897189461 410860290520122889420189)
                  ·
                    rfl

theorem cell23_7201328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_7201328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201328 prefixEnd_7201328 := by exact prefixLift 7201328
  have htrace : WordTrace (prefixWord ++ tailWord_7201328) baseStart_7201328 baseEnd_7201328 := by
    simpa [prefixWord, tailWord_7201328, baseEnd_7201328] using wordTrace_append hprefix tailTrace_7201328
  have hstable : (prefixWord ++ tailWord_7201328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201328).length < 2 ^ (prefixWord ++ tailWord_7201328).sum := by decide
  have hdescent : baseEnd_7201328 < baseStart_7201328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201345 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 8]
def baseStart_7201345 : Nat := 118140960795 + 7201345 * 2 ^ 59
def prefixEnd_7201345 : Nat := 4983230072969 + 3 ^ 40 * 7201345 * 2
def baseEnd_7201345 : Nat := 410861260428025826474347

theorem tailTrace_7201345 : CollatzResearch.WordTrace tailWord_7201345 prefixEnd_7201345 410861260428025826474347 := by
  unfold tailWord_7201345
  simp only [CollatzResearch.WordTrace]
  refine ⟨262654630095764431654421489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175103086730509621102947659 262654630095764431654421489)
  ·
    refine ⟨196990972571823323740816117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262654630095764431654421489 196990972571823323740816117)
    ·
      refine ⟨18467903678608436600701511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196990972571823323740816117 18467903678608436600701511)
      ·
        refine ⟨27701855517912654901052267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18467903678608436600701511 27701855517912654901052267)
        ·
          refine ⟨41552783276868982351578401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27701855517912654901052267 41552783276868982351578401)
          ·
            refine ⟨31164587457651736763683801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41552783276868982351578401 31164587457651736763683801)
            ·
              refine ⟨23373440593238802572762851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31164587457651736763683801 23373440593238802572762851)
              ·
                refine ⟨35060160889858203859144277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23373440593238802572762851 35060160889858203859144277)
                ·
                  refine ⟨410861260428025826474347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35060160889858203859144277 410861260428025826474347)
                  ·
                    rfl

theorem cell23_7201345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_7201345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201345 prefixEnd_7201345 := by exact prefixLift 7201345
  have htrace : WordTrace (prefixWord ++ tailWord_7201345) baseStart_7201345 baseEnd_7201345 := by
    simpa [prefixWord, tailWord_7201345, baseEnd_7201345] using wordTrace_append hprefix tailTrace_7201345
  have hstable : (prefixWord ++ tailWord_7201345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201345).length < 2 ^ (prefixWord ++ tailWord_7201345).sum := by decide
  have hdescent : baseEnd_7201345 < baseStart_7201345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201412 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7201412 : Nat := 118140960795 + 7201412 * 2 ^ 59
def prefixEnd_7201412 : Nat := 4983230072969 + 3 ^ 40 * 7201412 * 2
def baseEnd_7201412 : Nat := 3697785747056083676131315

theorem tailTrace_7201412 : CollatzResearch.WordTrace tailWord_7201412 prefixEnd_7201412 3697785747056083676131315 := by
  unfold tailWord_7201412
  simp only [CollatzResearch.WordTrace]
  refine ⟨131328536893260851048555245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175104715857681134731406993 131328536893260851048555245)
  ·
    refine ⟨49248201334972819143208217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131328536893260851048555245 49248201334972819143208217)
    ·
      refine ⟨36936151001229614357406163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49248201334972819143208217 36936151001229614357406163)
      ·
        refine ⟨55404226501844421536109245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36936151001229614357406163 55404226501844421536109245)
        ·
          refine ⟨20776584938191658076040967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55404226501844421536109245 20776584938191658076040967)
          ·
            refine ⟨31164877407287487114061451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20776584938191658076040967 31164877407287487114061451)
            ·
              refine ⟨46747316110931230671092177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31164877407287487114061451 46747316110931230671092177)
              ·
                refine ⟨35060487083198423003319133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46747316110931230671092177 35060487083198423003319133)
                ·
                  refine ⟨13147682656199408626244675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35060487083198423003319133 13147682656199408626244675)
                  ·
                    refine ⟨19721523984299112939367013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13147682656199408626244675 19721523984299112939367013)
                    ·
                      refine ⟨3697785747056083676131315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19721523984299112939367013 3697785747056083676131315)
                      ·
                        rfl

theorem cell23_7201412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7201412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201412 prefixEnd_7201412 := by exact prefixLift 7201412
  have htrace : WordTrace (prefixWord ++ tailWord_7201412) baseStart_7201412 baseEnd_7201412 := by
    simpa [prefixWord, tailWord_7201412, baseEnd_7201412] using wordTrace_append hprefix tailTrace_7201412
  have hstable : (prefixWord ++ tailWord_7201412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201412).length < 2 ^ (prefixWord ++ tailWord_7201412).sum := by decide
  have hdescent : baseEnd_7201412 < baseStart_7201412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201415 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_7201415 : Nat := 118140960795 + 7201415 * 2 ^ 59
def prefixEnd_7201415 : Nat := 4983230072969 + 3 ^ 40 * 7201415 * 2
def baseEnd_7201415 : Nat := 3697787287498047164393801

theorem tailTrace_7201415 : CollatzResearch.WordTrace tailWord_7201415 prefixEnd_7201415 3697787287498047164393801 := by
  unfold tailWord_7201415
  simp only [CollatzResearch.WordTrace]
  refine ⟨262657183205510833609469699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175104788803673889072979799 262657183205510833609469699)
  ·
    refine ⟨393985774808266250414204549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262657183205510833609469699 393985774808266250414204549)
    ·
      refine ⟨73872332776549921952663353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393985774808266250414204549 73872332776549921952663353)
      ·
        refine ⟨55404249582412441464497515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73872332776549921952663353 55404249582412441464497515)
        ·
          refine ⟨83106374373618662196746273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55404249582412441464497515 83106374373618662196746273)
          ·
            refine ⟨62329780780213996647559705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83106374373618662196746273 62329780780213996647559705)
            ·
              refine ⟨46747335585160497485669779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62329780780213996647559705 46747335585160497485669779)
              ·
                refine ⟨70121003377740746228504669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46747335585160497485669779 70121003377740746228504669)
                ·
                  refine ⟨26295376266652779835689251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70121003377740746228504669 26295376266652779835689251)
                  ·
                    refine ⟨39443064399979169753533877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26295376266652779835689251 39443064399979169753533877)
                    ·
                      refine ⟨3697787287498047164393801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39443064399979169753533877 3697787287498047164393801)
                      ·
                        rfl

theorem cell23_7201415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_7201415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201415 prefixEnd_7201415 := by exact prefixLift 7201415
  have htrace : WordTrace (prefixWord ++ tailWord_7201415) baseStart_7201415 baseEnd_7201415 := by
    simpa [prefixWord, tailWord_7201415, baseEnd_7201415] using wordTrace_append hprefix tailTrace_7201415
  have hstable : (prefixWord ++ tailWord_7201415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201415).length < 2 ^ (prefixWord ++ tailWord_7201415).sum := by decide
  have hdescent : baseEnd_7201415 < baseStart_7201415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201422 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_7201422 : Nat := 118140960795 + 7201422 * 2 ^ 59
def prefixEnd_7201422 : Nat := 4983230072969 + 3 ^ 40 * 7201422 * 2
def baseEnd_7201422 : Nat := 1232596960620876212335423

theorem tailTrace_7201422 : CollatzResearch.WordTrace tailWord_7201422 prefixEnd_7201422 1232596960620876212335423 := by
  unfold tailWord_7201422
  simp only [CollatzResearch.WordTrace]
  refine ⟨32832179814560684225621815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175104959010990315869983013 32832179814560684225621815)
  ·
    refine ⟨49248269721841026338432723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32832179814560684225621815 49248269721841026338432723)
    ·
      refine ⟨73872404582761539507649085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49248269721841026338432723 73872404582761539507649085)
      ·
        refine ⟨27702151718535577315368407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73872404582761539507649085 27702151718535577315368407)
        ·
          refine ⟨41553227577803365973052611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27702151718535577315368407 41553227577803365973052611)
          ·
            refine ⟨62329841366705048959578917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41553227577803365973052611 62329841366705048959578917)
            ·
              refine ⟨11686845256257196679921047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62329841366705048959578917 11686845256257196679921047)
              ·
                refine ⟨17530267884385795019881571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686845256257196679921047 17530267884385795019881571)
                ·
                  refine ⟨26295401826578692529822357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17530267884385795019881571 26295401826578692529822357)
                  ·
                    refine ⟨1232596960620876212335423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26295401826578692529822357 1232596960620876212335423)
                    ·
                      rfl

theorem cell23_7201422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_7201422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201422 prefixEnd_7201422 := by exact prefixLift 7201422
  have htrace : WordTrace (prefixWord ++ tailWord_7201422) baseStart_7201422 baseEnd_7201422 := by
    simpa [prefixWord, tailWord_7201422, baseEnd_7201422] using wordTrace_append hprefix tailTrace_7201422
  have hstable : (prefixWord ++ tailWord_7201422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201422).length < 2 ^ (prefixWord ++ tailWord_7201422).sum := by decide
  have hdescent : baseEnd_7201422 < baseStart_7201422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201432 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7201432 : Nat := 118140960795 + 7201432 * 2 ^ 59
def prefixEnd_7201432 : Nat := 4983230072969 + 3 ^ 40 * 7201432 * 2
def baseEnd_7201432 : Nat := 3697796016669173597881223

theorem tailTrace_7201432 : CollatzResearch.WordTrace tailWord_7201432 prefixEnd_7201432 3697796016669173597881223 := by
  unfold tailWord_7201432
  simp only [CollatzResearch.WordTrace]
  refine ⟨131328901623224622756419275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175105202164299497008559033 131328901623224622756419275)
  ·
    refine ⟨196993352434836934134628913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131328901623224622756419275 196993352434836934134628913)
    ·
      refine ⟨147745014326127700600971685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196993352434836934134628913 147745014326127700600971685)
      ·
        refine ⟨27702190186148943862682191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147745014326127700600971685 27702190186148943862682191)
        ·
          refine ⟨41553285279223415794023287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27702190186148943862682191 41553285279223415794023287)
          ·
            refine ⟨62329927918835123691034931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41553285279223415794023287 62329927918835123691034931)
            ·
              refine ⟨93494891878252685536552397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62329927918835123691034931 93494891878252685536552397)
              ·
                refine ⟨35060584454344757076207149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93494891878252685536552397 35060584454344757076207149)
                ·
                  refine ⟨13147719170379283903577681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35060584454344757076207149 13147719170379283903577681)
                  ·
                    refine ⟨9860789377784462927683261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13147719170379283903577681 9860789377784462927683261)
                    ·
                      refine ⟨3697796016669173597881223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9860789377784462927683261 3697796016669173597881223)
                      ·
                        rfl

theorem cell23_7201432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7201432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201432 prefixEnd_7201432 := by exact prefixLift 7201432
  have htrace : WordTrace (prefixWord ++ tailWord_7201432) baseStart_7201432 baseEnd_7201432 := by
    simpa [prefixWord, tailWord_7201432, baseEnd_7201432] using wordTrace_append hprefix tailTrace_7201432
  have hstable : (prefixWord ++ tailWord_7201432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201432).length < 2 ^ (prefixWord ++ tailWord_7201432).sum := by decide
  have hdescent : baseEnd_7201432 < baseStart_7201432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201473 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7201473 : Nat := 118140960795 + 7201473 * 2 ^ 59
def prefixEnd_7201473 : Nat := 4983230072969 + 3 ^ 40 * 7201473 * 2
def baseEnd_7201473 : Nat := 1232605689792002645822845

theorem tailTrace_7201473 : CollatzResearch.WordTrace tailWord_7201473 prefixEnd_7201473 1232605689792002645822845 := by
  unfold tailWord_7201473
  simp only [CollatzResearch.WordTrace]
  refine ⟨262659298639300709515081073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175106199092867139676720715 262659298639300709515081073)
  ·
    refine ⟨196994473979475532136310805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262659298639300709515081073 196994473979475532136310805)
    ·
      refine ⟨9234115967787915568889569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196994473979475532136310805 9234115967787915568889569)
      ·
        refine ⟨6925586975840936676667177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9234115967787915568889569 6925586975840936676667177)
        ·
          refine ⟨5194190231880702507500383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6925586975840936676667177 5194190231880702507500383)
          ·
            refine ⟨7791285347821053761250575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194190231880702507500383 7791285347821053761250575)
            ·
              refine ⟨11686928021731580641875863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791285347821053761250575 11686928021731580641875863)
              ·
                refine ⟨17530392032597370962813795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11686928021731580641875863 17530392032597370962813795)
                ·
                  refine ⟨26295588048896056444220693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17530392032597370962813795 26295588048896056444220693)
                  ·
                    refine ⟨1232605689792002645822845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26295588048896056444220693 1232605689792002645822845)
                    ·
                      rfl

theorem cell23_7201473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7201473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201473 prefixEnd_7201473 := by exact prefixLift 7201473
  have htrace : WordTrace (prefixWord ++ tailWord_7201473) baseStart_7201473 baseEnd_7201473 := by
    simpa [prefixWord, tailWord_7201473, baseEnd_7201473] using wordTrace_append hprefix tailTrace_7201473
  have hstable : (prefixWord ++ tailWord_7201473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201473).length < 2 ^ (prefixWord ++ tailWord_7201473).sum := by decide
  have hdescent : baseEnd_7201473 < baseStart_7201473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201592 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_7201592 : Nat := 118140960795 + 7201592 * 2 ^ 59
def prefixEnd_7201592 : Nat := 4983230072969 + 3 ^ 40 * 7201592 * 2
def baseEnd_7201592 : Nat := 3697878173573892971880487

theorem tailTrace_7201592 : CollatzResearch.WordTrace tailWord_7201592 prefixEnd_7201592 3697878173573892971880487 := by
  unfold tailWord_7201592
  simp only [CollatzResearch.WordTrace]
  refine ⟨131331819462934796419331515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175109092617246395225775353 131331819462934796419331515)
  ·
    refine ⟨196997729194402194628997273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131331819462934796419331515 196997729194402194628997273)
    ·
      refine ⟨147748296895801645971747955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196997729194402194628997273 147748296895801645971747955)
      ·
        refine ⟨221622445343702468957621933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147748296895801645971747955 221622445343702468957621933)
        ·
          refine ⟨83108417003888425859108225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221622445343702468957621933 83108417003888425859108225)
          ·
            refine ⟨62331312752916319394331169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83108417003888425859108225 62331312752916319394331169)
            ·
              refine ⟨46748484564687239545748377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62331312752916319394331169 46748484564687239545748377)
              ·
                refine ⟨35061363423515429659311283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46748484564687239545748377 35061363423515429659311283)
                ·
                  refine ⟨52592045135273144488966925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35061363423515429659311283 52592045135273144488966925)
                  ·
                    refine ⟨19722016925727429183362597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52592045135273144488966925 19722016925727429183362597)
                    ·
                      refine ⟨3697878173573892971880487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19722016925727429183362597 3697878173573892971880487)
                      ·
                        rfl

theorem cell23_7201592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_7201592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201592 prefixEnd_7201592 := by exact prefixLift 7201592
  have htrace : WordTrace (prefixWord ++ tailWord_7201592) baseStart_7201592 baseEnd_7201592 := by
    simpa [prefixWord, tailWord_7201592, baseEnd_7201592] using wordTrace_append hprefix tailTrace_7201592
  have hstable : (prefixWord ++ tailWord_7201592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201592).length < 2 ^ (prefixWord ++ tailWord_7201592).sum := by decide
  have hdescent : baseEnd_7201592 < baseStart_7201592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201609 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 4]
def baseStart_7201609 : Nat := 118140960795 + 7201609 * 2 ^ 59
def prefixEnd_7201609 : Nat := 4983230072969 + 3 ^ 40 * 7201609 * 2
def baseEnd_7201609 : Nat := 3697886902745019405367909

theorem tailTrace_7201609 : CollatzResearch.WordTrace tailWord_7201609 prefixEnd_7201609 3697886902745019405367909 := by
  unfold tailWord_7201609
  simp only [CollatzResearch.WordTrace]
  refine ⟨262664258966808004742031881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175109505977872003161354587 262664258966808004742031881)
  ·
    refine ⟨196998194225106003556523911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262664258966808004742031881 196998194225106003556523911)
    ·
      refine ⟨295497291337659005334785867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196998194225106003556523911 295497291337659005334785867)
      ·
        refine ⟨443245937006488508002178801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295497291337659005334785867 443245937006488508002178801)
        ·
          refine ⟨332434452754866381001634101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443245937006488508002178801 332434452754866381001634101)
          ·
            refine ⟨31165729945768723218903197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332434452754866381001634101 31165729945768723218903197)
            ·
              refine ⟨11687148729663271207088699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31165729945768723218903197 11687148729663271207088699)
              ·
                refine ⟨17530723094494906810633049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11687148729663271207088699 17530723094494906810633049)
                ·
                  refine ⟨13148042320871180107974787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17530723094494906810633049 13148042320871180107974787)
                  ·
                    refine ⟨19722063481306770161962181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13148042320871180107974787 19722063481306770161962181)
                    ·
                      refine ⟨3697886902745019405367909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19722063481306770161962181 3697886902745019405367909)
                      ·
                        rfl

theorem cell23_7201609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 4].length) (baseStart_7201609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201609 prefixEnd_7201609 := by exact prefixLift 7201609
  have htrace : WordTrace (prefixWord ++ tailWord_7201609) baseStart_7201609 baseEnd_7201609 := by
    simpa [prefixWord, tailWord_7201609, baseEnd_7201609] using wordTrace_append hprefix tailTrace_7201609
  have hstable : (prefixWord ++ tailWord_7201609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201609).length < 2 ^ (prefixWord ++ tailWord_7201609).sum := by decide
  have hdescent : baseEnd_7201609 < baseStart_7201609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201632 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 8]
def baseStart_7201632 : Nat := 118140960795 + 7201632 * 2 ^ 59
def prefixEnd_7201632 : Nat := 4983230072969 + 3 ^ 40 * 7201632 * 2
def baseEnd_7201632 : Nat := 410877634755563646153367

theorem tailTrace_7201632 : CollatzResearch.WordTrace tailWord_7201632 prefixEnd_7201632 410877634755563646153367 := by
  unfold tailWord_7201632
  simp only [CollatzResearch.WordTrace]
  refine ⟨131332548922862339835059575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175110065230483119780079433 131332548922862339835059575)
  ·
    refine ⟨196998823384293509752589363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131332548922862339835059575 196998823384293509752589363)
    ·
      refine ⟨295498235076440264628884045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196998823384293509752589363 295498235076440264628884045)
      ·
        refine ⟨110811838153665099235831517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295498235076440264628884045 110811838153665099235831517)
        ·
          refine ⟨41554439307624412213436819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110811838153665099235831517 41554439307624412213436819)
          ·
            refine ⟨62331658961436618320155229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41554439307624412213436819 62331658961436618320155229)
            ·
              refine ⟨23374372110538731870058211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62331658961436618320155229 23374372110538731870058211)
              ·
                refine ⟨35061558165808097805087317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23374372110538731870058211 35061558165808097805087317)
                ·
                  refine ⟨410877634755563646153367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35061558165808097805087317 410877634755563646153367)
                  ·
                    rfl

theorem cell23_7201632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_7201632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201632 prefixEnd_7201632 := by exact prefixLift 7201632
  have htrace : WordTrace (prefixWord ++ tailWord_7201632) baseStart_7201632 baseEnd_7201632 := by
    simpa [prefixWord, tailWord_7201632, baseEnd_7201632] using wordTrace_append hprefix tailTrace_7201632
  have hstable : (prefixWord ++ tailWord_7201632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201632).length < 2 ^ (prefixWord ++ tailWord_7201632).sum := by decide
  have hdescent : baseEnd_7201632 < baseStart_7201632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201636 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_7201636 : Nat := 118140960795 + 7201636 * 2 ^ 59
def prefixEnd_7201636 : Nat := 4983230072969 + 3 ^ 40 * 7201636 * 2
def baseEnd_7201636 : Nat := 1232633588907563599910095

theorem tailTrace_7201636 : CollatzResearch.WordTrace tailWord_7201636 prefixEnd_7201636 1232633588907563599910095 := by
  unfold tailWord_7201636
  simp only [CollatzResearch.WordTrace]
  refine ⟨131332621868855094176632381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175110162491806792235509841 131332621868855094176632381)
  ·
    refine ⟨49249733200820660316237143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131332621868855094176632381 49249733200820660316237143)
    ·
      refine ⟨73874599801230990474355715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49249733200820660316237143 73874599801230990474355715)
      ·
        refine ⟨110811899701846485711533573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73874599801230990474355715 110811899701846485711533573)
        ·
          refine ⟨20777231194096216070912545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110811899701846485711533573 20777231194096216070912545)
          ·
            refine ⟨15582923395572162053184409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20777231194096216070912545 15582923395572162053184409)
            ·
              refine ⟨11687192546679121539888307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15582923395572162053184409 11687192546679121539888307)
              ·
                refine ⟨17530788820018682309832461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11687192546679121539888307 17530788820018682309832461)
                ·
                  refine ⟨6574045807507005866187173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17530788820018682309832461 6574045807507005866187173)
                  ·
                    refine ⟨1232633588907563599910095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574045807507005866187173 1232633588907563599910095)
                    ·
                      rfl

theorem cell23_7201636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_7201636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201636 prefixEnd_7201636 := by exact prefixLift 7201636
  have htrace : WordTrace (prefixWord ++ tailWord_7201636) baseStart_7201636 baseEnd_7201636 := by
    simpa [prefixWord, tailWord_7201636, baseEnd_7201636] using wordTrace_append hprefix tailTrace_7201636
  have hstable : (prefixWord ++ tailWord_7201636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201636).length < 2 ^ (prefixWord ++ tailWord_7201636).sum := by decide
  have hdescent : baseEnd_7201636 < baseStart_7201636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201713 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_7201713 : Nat := 118140960795 + 7201713 * 2 ^ 59
def prefixEnd_7201713 : Nat := 4983230072969 + 3 ^ 40 * 7201713 * 2
def baseEnd_7201713 : Nat := 1232646768244362332822477

theorem tailTrace_7201713 : CollatzResearch.WordTrace tailWord_7201713 prefixEnd_7201713 1232646768244362332822477 := by
  unfold tailWord_7201713
  simp only [CollatzResearch.WordTrace]
  refine ⟨262668052158431230503817793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175112034772287487002545195 262668052158431230503817793)
  ·
    refine ⟨197001039118823422877863345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262668052158431230503817793 197001039118823422877863345)
    ·
      refine ⟨147750779339117567158397509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197001039118823422877863345 147750779339117567158397509)
      ·
        refine ⟨27703271126084543842199533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147750779339117567158397509 27703271126084543842199533)
        ·
          refine ⟨10388726672281703940824825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27703271126084543842199533 10388726672281703940824825)
          ·
            refine ⟨7791545004211277955618619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10388726672281703940824825 7791545004211277955618619)
            ·
              refine ⟨11687317506316916933427929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791545004211277955618619 11687317506316916933427929)
              ·
                refine ⟨8765488129737687700070947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11687317506316916933427929 8765488129737687700070947)
                ·
                  refine ⟨13148232194606531550106421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8765488129737687700070947 13148232194606531550106421)
                  ·
                    refine ⟨1232646768244362332822477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13148232194606531550106421 1232646768244362332822477)
                    ·
                      rfl

theorem cell23_7201713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_7201713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201713 prefixEnd_7201713 := by exact prefixLift 7201713
  have htrace : WordTrace (prefixWord ++ tailWord_7201713) baseStart_7201713 baseEnd_7201713 := by
    simpa [prefixWord, tailWord_7201713, baseEnd_7201713] using wordTrace_append hprefix tailTrace_7201713
  have hstable : (prefixWord ++ tailWord_7201713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201713).length < 2 ^ (prefixWord ++ tailWord_7201713).sum := by decide
  have hdescent : baseEnd_7201713 < baseStart_7201713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201722 : List Nat := [3, 1, 1, 1, 2, 1, 3, 11]
def baseStart_7201722 : Nat := 118140960795 + 7201722 * 2 ^ 59
def prefixEnd_7201722 : Nat := 4983230072969 + 3 ^ 40 * 7201722 * 2
def baseEnd_7201722 : Nat := 136960923187369535676107

theorem tailTrace_7201722 : CollatzResearch.WordTrace tailWord_7201722 prefixEnd_7201722 136960923187369535676107 := by
  unfold tailWord_7201722
  simp only [CollatzResearch.WordTrace]
  refine ⟨65667095103849656260223855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175112253610265750027263613 65667095103849656260223855)
  ·
    refine ⟨98500642655774484390335783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65667095103849656260223855 98500642655774484390335783)
    ·
      refine ⟨147750963983661726585503675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98500642655774484390335783 147750963983661726585503675)
      ·
        refine ⟨221626445975492589878255513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147750963983661726585503675 221626445975492589878255513)
        ·
          refine ⟨166219834481619442408691635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221626445975492589878255513 166219834481619442408691635)
          ·
            refine ⟨249329751722429163613037453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166219834481619442408691635 249329751722429163613037453)
            ·
              refine ⟨93498656895910936354889045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249329751722429163613037453 93498656895910936354889045)
              ·
                refine ⟨136960923187369535676107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93498656895910936354889045 136960923187369535676107)
                ·
                  rfl

theorem cell23_7201722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_7201722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201722 prefixEnd_7201722 := by exact prefixLift 7201722
  have htrace : WordTrace (prefixWord ++ tailWord_7201722) baseStart_7201722 baseEnd_7201722 := by
    simpa [prefixWord, tailWord_7201722, baseEnd_7201722] using wordTrace_append hprefix tailTrace_7201722
  have hstable : (prefixWord ++ tailWord_7201722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201722).length < 2 ^ (prefixWord ++ tailWord_7201722).sum := by decide
  have hdescent : baseEnd_7201722 < baseStart_7201722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201794 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7201794 : Nat := 118140960795 + 7201794 * 2 ^ 59
def prefixEnd_7201794 : Nat := 4983230072969 + 3 ^ 40 * 7201794 * 2
def baseEnd_7201794 : Nat := 1232660632222033727184853

theorem tailTrace_7201794 : CollatzResearch.WordTrace tailWord_7201794 prefixEnd_7201794 1232660632222033727184853 := by
  unfold tailWord_7201794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65667751617784445334379109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175114004314091854225010957 65667751617784445334379109)
  ·
    refine ⟨12312703428334583500196083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65667751617784445334379109 12312703428334583500196083)
    ·
      refine ⟨18469055142501875250294125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12312703428334583500196083 18469055142501875250294125)
      ·
        refine ⟨6925895678438203218860297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18469055142501875250294125 6925895678438203218860297)
        ·
          refine ⟨5194421758828652414145223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6925895678438203218860297 5194421758828652414145223)
          ·
            refine ⟨7791632638242978621217835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194421758828652414145223 7791632638242978621217835)
            ·
              refine ⟨11687448957364467931826753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791632638242978621217835 11687448957364467931826753)
              ·
                refine ⟨8765586718023350948870065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11687448957364467931826753 8765586718023350948870065)
                ·
                  refine ⟨6574190038517513211652549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765586718023350948870065 6574190038517513211652549)
                  ·
                    refine ⟨1232660632222033727184853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574190038517513211652549 1232660632222033727184853)
                    ·
                      rfl

theorem cell23_7201794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7201794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201794 prefixEnd_7201794 := by exact prefixLift 7201794
  have htrace : WordTrace (prefixWord ++ tailWord_7201794) baseStart_7201794 baseEnd_7201794 := by
    simpa [prefixWord, tailWord_7201794, baseEnd_7201794] using wordTrace_append hprefix tailTrace_7201794
  have hstable : (prefixWord ++ tailWord_7201794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201794).length < 2 ^ (prefixWord ++ tailWord_7201794).sum := by decide
  have hdescent : baseEnd_7201794 < baseStart_7201794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201799 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 4, 6]
def baseStart_7201799 : Nat := 118140960795 + 7201799 * 2 ^ 59
def prefixEnd_7201799 : Nat := 4983230072969 + 3 ^ 40 * 7201799 * 2
def baseEnd_7201799 : Nat := 1232661488023124553997345

theorem tailTrace_7201799 : CollatzResearch.WordTrace tailWord_7201799 prefixEnd_7201799 1232661488023124553997345 := by
  unfold tailWord_7201799
  simp only [CollatzResearch.WordTrace]
  refine ⟨262671188836119667191448451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175114125890746444794298967 262671188836119667191448451)
  ·
    refine ⟨394006783254179500787172677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262671188836119667191448451 394006783254179500787172677)
    ·
      refine ⟨73876271860158656397594877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394006783254179500787172677 73876271860158656397594877)
      ·
        refine ⟨27703601947559496149098079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73876271860158656397594877 27703601947559496149098079)
        ·
          refine ⟨41555402921339244223647119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27703601947559496149098079 41555402921339244223647119)
          ·
            refine ⟨62333104382008866335470679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41555402921339244223647119 62333104382008866335470679)
            ·
              refine ⟨93499656573013299503206019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62333104382008866335470679 93499656573013299503206019)
              ·
                refine ⟨140249484859519949254809029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93499656573013299503206019 140249484859519949254809029)
                ·
                  refine ⟨26296778411159990485276693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140249484859519949254809029 26296778411159990485276693)
                  ·
                    refine ⟨1232661488023124553997345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26296778411159990485276693 1232661488023124553997345)
                    ·
                      rfl

theorem cell23_7201799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_7201799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201799 prefixEnd_7201799 := by exact prefixLift 7201799
  have htrace : WordTrace (prefixWord ++ tailWord_7201799) baseStart_7201799 baseEnd_7201799 := by
    simpa [prefixWord, tailWord_7201799, baseEnd_7201799] using wordTrace_append hprefix tailTrace_7201799
  have hstable : (prefixWord ++ tailWord_7201799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201799).length < 2 ^ (prefixWord ++ tailWord_7201799).sum := by decide
  have hdescent : baseEnd_7201799 < baseStart_7201799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201800 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_7201800 : Nat := 118140960795 + 7201800 * 2 ^ 59
def prefixEnd_7201800 : Nat := 4983230072969 + 3 ^ 40 * 7201800 * 2
def baseEnd_7201800 : Nat := 3697984977550028158079531

theorem tailTrace_7201800 : CollatzResearch.WordTrace tailWord_7201800 prefixEnd_7201800 3697984977550028158079531 := by
  unfold tailWord_7201800
  simp only [CollatzResearch.WordTrace]
  refine ⟨131335612654558022181117427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175114150206077362908156569 131335612654558022181117427)
  ·
    refine ⟨197003418981837033271676141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131335612654558022181117427 197003418981837033271676141)
    ·
      refine ⟨73876282118188887476878553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197003418981837033271676141 73876282118188887476878553)
      ·
        refine ⟨55407211588641665607658915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73876282118188887476878553 55407211588641665607658915)
        ·
          refine ⟨83110817382962498411488373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55407211588641665607658915 83110817382962498411488373)
          ·
            refine ⟨7791639129652734226077035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83110817382962498411488373 7791639129652734226077035)
            ·
              refine ⟨11687458694479101339115553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791639129652734226077035 11687458694479101339115553)
              ·
                refine ⟨8765594020859326004336665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11687458694479101339115553 8765594020859326004336665)
                ·
                  refine ⟨6574195515644494503252499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765594020859326004336665 6574195515644494503252499)
                  ·
                    refine ⟨9861293273466741754878749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6574195515644494503252499 9861293273466741754878749)
                    ·
                      refine ⟨3697984977550028158079531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861293273466741754878749 3697984977550028158079531)
                      ·
                        rfl

theorem cell23_7201800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_7201800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201800 prefixEnd_7201800 := by exact prefixLift 7201800
  have htrace : WordTrace (prefixWord ++ tailWord_7201800) baseStart_7201800 baseEnd_7201800 := by
    simpa [prefixWord, tailWord_7201800, baseEnd_7201800] using wordTrace_append hprefix tailTrace_7201800
  have hstable : (prefixWord ++ tailWord_7201800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201800).length < 2 ^ (prefixWord ++ tailWord_7201800).sum := by decide
  have hdescent : baseEnd_7201800 < baseStart_7201800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_7201809 : Nat := 118140960795 + 7201809 * 2 ^ 59
def prefixEnd_7201809 : Nat := 4983230072969 + 3 ^ 40 * 7201809 * 2
def baseEnd_7201809 : Nat := 3697989598875918622866989

theorem tailTrace_7201809 : CollatzResearch.WordTrace tailWord_7201809 prefixEnd_7201809 3697989598875918622866989 := by
  unfold tailWord_7201809
  simp only [CollatzResearch.WordTrace]
  refine ⟨262671553566083438899312481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175114369044055625932874987 262671553566083438899312481)
  ·
    refine ⟨197003665174562579174484361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262671553566083438899312481 197003665174562579174484361)
    ·
      refine ⟨147752748880921934380863271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197003665174562579174484361 147752748880921934380863271)
      ·
        refine ⟨221629123321382901571294907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147752748880921934380863271 221629123321382901571294907)
        ·
          refine ⟨332443684982074352356942361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221629123321382901571294907 332443684982074352356942361)
          ·
            refine ⟨249332763736555764267706771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332443684982074352356942361 249332763736555764267706771)
            ·
              refine ⟨373999145604833646401560157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249332763736555764267706771 373999145604833646401560157)
              ·
                refine ⟨140249679601812617400585059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373999145604833646401560157 140249679601812617400585059)
                ·
                  refine ⟨210374519402718926100877589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140249679601812617400585059 210374519402718926100877589)
                  ·
                    refine ⟨9861305597002449660978637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 210374519402718926100877589 9861305597002449660978637)
                    ·
                      refine ⟨3697989598875918622866989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861305597002449660978637 3697989598875918622866989)
                      ·
                        rfl

theorem cell23_7201809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_7201809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201809 prefixEnd_7201809 := by exact prefixLift 7201809
  have htrace : WordTrace (prefixWord ++ tailWord_7201809) baseStart_7201809 baseEnd_7201809 := by
    simpa [prefixWord, tailWord_7201809, baseEnd_7201809] using wordTrace_append hprefix tailTrace_7201809
  have hstable : (prefixWord ++ tailWord_7201809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201809).length < 2 ^ (prefixWord ++ tailWord_7201809).sum := by decide
  have hdescent : baseEnd_7201809 < baseStart_7201809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201823 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 1, 4, 2]
def baseStart_7201823 : Nat := 118140960795 + 7201823 * 2 ^ 59
def prefixEnd_7201823 : Nat := 4983230072969 + 3 ^ 40 * 7201823 * 2
def baseEnd_7201823 : Nat := 3697996787605081568091925

theorem tailTrace_7201823 : CollatzResearch.WordTrace tailWord_7201823 prefixEnd_7201823 3697996787605081568091925 := by
  unfold tailWord_7201823
  simp only [CollatzResearch.WordTrace]
  refine ⟨262672064188032719290322123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175114709458688479526881415 262672064188032719290322123)
  ·
    refine ⟨394008096282049078935483185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262672064188032719290322123 394008096282049078935483185)
    ·
      refine ⟨295506072211536809201612389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394008096282049078935483185 295506072211536809201612389)
      ·
        refine ⟨55407388539663151725302323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295506072211536809201612389 55407388539663151725302323)
        ·
          refine ⟨83111082809494727587953485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55407388539663151725302323 83111082809494727587953485)
          ·
            refine ⟨31166656053560522845482557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83111082809494727587953485 31166656053560522845482557)
            ·
              refine ⟨11687496020085196067055959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31166656053560522845482557 11687496020085196067055959)
              ·
                refine ⟨17531244030127794100583939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11687496020085196067055959 17531244030127794100583939)
                ·
                  refine ⟨26296866045191691150875909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17531244030127794100583939 26296866045191691150875909)
                  ·
                    refine ⟨4930662383473442090789233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26296866045191691150875909 4930662383473442090789233)
                    ·
                      refine ⟨3697996787605081568091925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930662383473442090789233 3697996787605081568091925)
                      ·
                        rfl

theorem cell23_7201823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_7201823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201823 prefixEnd_7201823 := by exact prefixLift 7201823
  have htrace : WordTrace (prefixWord ++ tailWord_7201823) baseStart_7201823 baseEnd_7201823 := by
    simpa [prefixWord, tailWord_7201823, baseEnd_7201823] using wordTrace_append hprefix tailTrace_7201823
  have hstable : (prefixWord ++ tailWord_7201823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201823).length < 2 ^ (prefixWord ++ tailWord_7201823).sum := by decide
  have hdescent : baseEnd_7201823 < baseStart_7201823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201829 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 7]
def baseStart_7201829 : Nat := 118140960795 + 7201829 * 2 ^ 59
def prefixEnd_7201829 : Nat := 4983230072969 + 3 ^ 40 * 7201829 * 2
def baseEnd_7201829 : Nat := 410888874276556504957433

theorem tailTrace_7201829 : CollatzResearch.WordTrace tailWord_7201829 prefixEnd_7201829 410888874276556504957433 := by
  unfold tailWord_7201829
  simp only [CollatzResearch.WordTrace]
  refine ⟨262672283026010982315040541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175114855350673988210027027 262672283026010982315040541)
  ·
    refine ⟨98502106134754118368140203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262672283026010982315040541 98502106134754118368140203)
    ·
      refine ⟨147753159202131177552210305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98502106134754118368140203 147753159202131177552210305)
      ·
        refine ⟨110814869401598383164157729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147753159202131177552210305 110814869401598383164157729)
        ·
          refine ⟨83111152051198787373118297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110814869401598383164157729 83111152051198787373118297)
          ·
            refine ⟨62333364038399090529838723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83111152051198787373118297 62333364038399090529838723)
            ·
              refine ⟨93500046057598635794758085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62333364038399090529838723 93500046057598635794758085)
              ·
                refine ⟨17531258635799744211517141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93500046057598635794758085 17531258635799744211517141)
                ·
                  refine ⟨410888874276556504957433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17531258635799744211517141 410888874276556504957433)
                  ·
                    rfl

theorem cell23_7201829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_7201829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201829 prefixEnd_7201829 := by exact prefixLift 7201829
  have htrace : WordTrace (prefixWord ++ tailWord_7201829) baseStart_7201829 baseEnd_7201829 := by
    simpa [prefixWord, tailWord_7201829, baseEnd_7201829] using wordTrace_append hprefix tailTrace_7201829
  have hstable : (prefixWord ++ tailWord_7201829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201829).length < 2 ^ (prefixWord ++ tailWord_7201829).sum := by decide
  have hdescent : baseEnd_7201829 < baseStart_7201829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201874 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_7201874 : Nat := 118140960795 + 7201874 * 2 ^ 59
def prefixEnd_7201874 : Nat := 4983230072969 + 3 ^ 40 * 7201874 * 2
def baseEnd_7201874 : Nat := 3698022975118460868554191

theorem tailTrace_7201874 : CollatzResearch.WordTrace tailWord_7201874 prefixEnd_7201874 3698022975118460868554191 := by
  unfold tailWord_7201874
  simp only [CollatzResearch.WordTrace]
  refine ⟨65668481077711988750107169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175115949540565303333619117 65668481077711988750107169)
  ·
    refine ⟨49251360808283991562580377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65668481077711988750107169 49251360808283991562580377)
    ·
      refine ⟨36938520606212993671935283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49251360808283991562580377 36938520606212993671935283)
      ·
        refine ⟨55407780909319490507902925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36938520606212993671935283 55407780909319490507902925)
        ·
          refine ⟨20777917840994808940463597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55407780909319490507902925 20777917840994808940463597)
          ·
            refine ⟨7791719190373053352673849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20777917840994808940463597 7791719190373053352673849)
            ·
              refine ⟨5843789392779790014505387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791719190373053352673849 5843789392779790014505387)
              ·
                refine ⟨8765684089169685021758081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843789392779790014505387 8765684089169685021758081)
                ·
                  refine ⟨6574263066877263766318561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765684089169685021758081 6574263066877263766318561)
                  ·
                    refine ⟨4930697300157947824738921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574263066877263766318561 4930697300157947824738921)
                    ·
                      refine ⟨3698022975118460868554191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930697300157947824738921 3698022975118460868554191)
                      ·
                        rfl

theorem cell23_7201874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_7201874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201874 prefixEnd_7201874 := by exact prefixLift 7201874
  have htrace : WordTrace (prefixWord ++ tailWord_7201874) baseStart_7201874 baseEnd_7201874 := by
    simpa [prefixWord, tailWord_7201874, baseEnd_7201874] using wordTrace_append hprefix tailTrace_7201874
  have hstable : (prefixWord ++ tailWord_7201874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201874).length < 2 ^ (prefixWord ++ tailWord_7201874).sum := by decide
  have hdescent : baseEnd_7201874 < baseStart_7201874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201889 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_7201889 : Nat := 118140960795 + 7201889 * 2 ^ 59
def prefixEnd_7201889 : Nat := 4983230072969 + 3 ^ 40 * 7201889 * 2
def baseEnd_7201889 : Nat := 1232676892442759436622207

theorem tailTrace_7201889 : CollatzResearch.WordTrace tailWord_7201889 prefixEnd_7201889 1232676892442759436622207 := by
  unfold tailWord_7201889
  simp only [CollatzResearch.WordTrace]
  refine ⟨262674471405793612562224721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175116314270529075041483147 262674471405793612562224721)
  ·
    refine ⟨197005853554345209421668541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262674471405793612562224721 197005853554345209421668541)
    ·
      refine ⟨73877195082879453533125703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197005853554345209421668541 73877195082879453533125703)
      ·
        refine ⟨110815792624319180299688555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73877195082879453533125703 110815792624319180299688555)
        ·
          refine ⟨166223688936478770449532833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110815792624319180299688555 166223688936478770449532833)
          ·
            refine ⟨124667766702359077837149625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166223688936478770449532833 124667766702359077837149625)
            ·
              refine ⟨93500825026769308377862219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124667766702359077837149625 93500825026769308377862219)
              ·
                refine ⟨140251237540153962566793329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93500825026769308377862219 140251237540153962566793329)
                ·
                  refine ⟨105188428155115471925094997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140251237540153962566793329 105188428155115471925094997)
                  ·
                    refine ⟨1232676892442759436622207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105188428155115471925094997 1232676892442759436622207)
                    ·
                      rfl

theorem cell23_7201889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_7201889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201889 prefixEnd_7201889 := by exact prefixLift 7201889
  have htrace : WordTrace (prefixWord ++ tailWord_7201889) baseStart_7201889 baseEnd_7201889 := by
    simpa [prefixWord, tailWord_7201889, baseEnd_7201889] using wordTrace_append hprefix tailTrace_7201889
  have hstable : (prefixWord ++ tailWord_7201889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201889).length < 2 ^ (prefixWord ++ tailWord_7201889).sum := by decide
  have hdescent : baseEnd_7201889 < baseStart_7201889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201950 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7201950 : Nat := 118140960795 + 7201950 * 2 ^ 59
def prefixEnd_7201950 : Nat := 4983230072969 + 3 ^ 40 * 7201950 * 2
def baseEnd_7201950 : Nat := 3698061999648202571203841

theorem tailTrace_7201950 : CollatzResearch.WordTrace tailWord_7201950 prefixEnd_7201950 3698061999648202571203841 := by
  unfold tailWord_7201950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32834587032321577497524413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175117797505715079986796869 32834587032321577497524413)
  ·
    refine ⟨12312970137120591561571655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32834587032321577497524413 12312970137120591561571655)
    ·
      refine ⟨18469455205680887342357483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12312970137120591561571655 18469455205680887342357483)
      ·
        refine ⟨27704182808521331013536225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18469455205680887342357483 27704182808521331013536225)
        ·
          refine ⟨20778137106390998260152169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27704182808521331013536225 20778137106390998260152169)
          ·
            refine ⟨15583602829793248695114127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20778137106390998260152169 15583602829793248695114127)
            ·
              refine ⟨23375404244689873042671191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15583602829793248695114127 23375404244689873042671191)
              ·
                refine ⟨35063106367034809564006787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23375404244689873042671191 35063106367034809564006787)
                ·
                  refine ⟨52594659550552214346010181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35063106367034809564006787 52594659550552214346010181)
                  ·
                    refine ⟨9861498665728540189876909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52594659550552214346010181 9861498665728540189876909)
                    ·
                      refine ⟨3698061999648202571203841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861498665728540189876909 3698061999648202571203841)
                      ·
                        rfl

theorem cell23_7201950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7201950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201950 prefixEnd_7201950 := by exact prefixLift 7201950
  have htrace : WordTrace (prefixWord ++ tailWord_7201950) baseStart_7201950 baseEnd_7201950 := by
    simpa [prefixWord, tailWord_7201950, baseEnd_7201950] using wordTrace_append hprefix tailTrace_7201950
  have hstable : (prefixWord ++ tailWord_7201950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201950).length < 2 ^ (prefixWord ++ tailWord_7201950).sum := by decide
  have hdescent : baseEnd_7201950 < baseStart_7201950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201974 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7201974 : Nat := 118140960795 + 7201974 * 2 ^ 59
def prefixEnd_7201974 : Nat := 4983230072969 + 3 ^ 40 * 7201974 * 2
def baseEnd_7201974 : Nat := 1232691441061303492434577

theorem tailTrace_7201974 : CollatzResearch.WordTrace tailWord_7201974 prefixEnd_7201974 1232691441061303492434577 := by
  unfold tailWord_7201974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16417348225655354504941811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175118381073657114719379317 16417348225655354504941811)
  ·
    refine ⟨24626022338483031757412717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16417348225655354504941811 24626022338483031757412717)
    ·
      refine ⟨9234758376931136909029769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24626022338483031757412717 9234758376931136909029769)
      ·
        refine ⟨6926068782698352681772327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9234758376931136909029769 6926068782698352681772327)
        ·
          refine ⟨10389103174047529022658491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926068782698352681772327 10389103174047529022658491)
          ·
            refine ⟨15583654761071293533987737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10389103174047529022658491 15583654761071293533987737)
            ·
              refine ⟨11687741070803470150490803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15583654761071293533987737 11687741070803470150490803)
              ·
                refine ⟨17531611606205205225736205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11687741070803470150490803 17531611606205205225736205)
                ·
                  refine ⟨6574354352326951959651077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17531611606205205225736205 6574354352326951959651077)
                  ·
                    refine ⟨1232691441061303492434577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574354352326951959651077 1232691441061303492434577)
                    ·
                      rfl

theorem cell23_7201974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7201974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201974 prefixEnd_7201974 := by exact prefixLift 7201974
  have htrace : WordTrace (prefixWord ++ tailWord_7201974) baseStart_7201974 baseEnd_7201974 := by
    simpa [prefixWord, tailWord_7201974, baseEnd_7201974] using wordTrace_append hprefix tailTrace_7201974
  have hstable : (prefixWord ++ tailWord_7201974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201974).length < 2 ^ (prefixWord ++ tailWord_7201974).sum := by decide
  have hdescent : baseEnd_7201974 < baseStart_7201974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7201980 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_7201980 : Nat := 118140960795 + 7201980 * 2 ^ 59
def prefixEnd_7201980 : Nat := 4983230072969 + 3 ^ 40 * 7201980 * 2
def baseEnd_7201980 : Nat := 3698077404067837453828703

theorem tailTrace_7201980 : CollatzResearch.WordTrace tailWord_7201980 prefixEnd_7201980 3698077404067837453828703 := by
  unfold tailWord_7201980
  simp only [CollatzResearch.WordTrace]
  refine ⟨131338895224231967551893697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175118526965642623402524929 131338895224231967551893697)
  ·
    refine ⟨98504171418173975663920273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131338895224231967551893697 98504171418173975663920273)
    ·
      refine ⟨73878128563630481747940205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98504171418173975663920273 73878128563630481747940205)
      ·
        refine ⟨27704298211361430655477577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73878128563630481747940205 27704298211361430655477577)
        ·
          refine ⟨20778223658521072991608183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27704298211361430655477577 20778223658521072991608183)
          ·
            refine ⟨31167335487781609487412275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20778223658521072991608183 31167335487781609487412275)
            ·
              refine ⟨46751003231672414231118413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31167335487781609487412275 46751003231672414231118413)
              ·
                refine ⟨17531626211877155336669405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46751003231672414231118413 17531626211877155336669405)
                ·
                  refine ⟨6574359829453933251251027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17531626211877155336669405 6574359829453933251251027)
                  ·
                    refine ⟨9861539744180899876876541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6574359829453933251251027 9861539744180899876876541)
                    ·
                      refine ⟨3698077404067837453828703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861539744180899876876541 3698077404067837453828703)
                      ·
                        rfl

theorem cell23_7201980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_7201980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7201980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7201980 prefixEnd_7201980 := by exact prefixLift 7201980
  have htrace : WordTrace (prefixWord ++ tailWord_7201980) baseStart_7201980 baseEnd_7201980 := by
    simpa [prefixWord, tailWord_7201980, baseEnd_7201980] using wordTrace_append hprefix tailTrace_7201980
  have hstable : (prefixWord ++ tailWord_7201980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7201980).length < 2 ^ (prefixWord ++ tailWord_7201980).sum := by decide
  have hdescent : baseEnd_7201980 < baseStart_7201980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7201980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202020 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_7202020 : Nat := 118140960795 + 7202020 * 2 ^ 59
def prefixEnd_7202020 : Nat := 4983230072969 + 3 ^ 40 * 7202020 * 2
def baseEnd_7202020 : Nat := 3698097943294017297328519

theorem tailTrace_7202020 : CollatzResearch.WordTrace tailWord_7202020 prefixEnd_7202020 3698097943294017297328519 := by
  unfold tailWord_7202020
  simp only [CollatzResearch.WordTrace]
  refine ⟨131339624684159510967621757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175119499578879347956829009 131339624684159510967621757)
  ·
    refine ⟨49252359256559816612858159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131339624684159510967621757 49252359256559816612858159)
    ·
      refine ⟨73878538884839724919287239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49252359256559816612858159 73878538884839724919287239)
      ·
        refine ⟨110817808327259587378930859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73878538884839724919287239 110817808327259587378930859)
        ·
          refine ⟨166226712490889381068396289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110817808327259587378930859 166226712490889381068396289)
          ·
            refine ⟨124670034368167035801297217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166226712490889381068396289 124670034368167035801297217)
            ·
              refine ⟨93502525776125276850972913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124670034368167035801297217 93502525776125276850972913)
              ·
                refine ⟨70126894332093957638229685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93502525776125276850972913 70126894332093957638229685)
                ·
                  refine ⟨6574396343633808528584033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70126894332093957638229685 6574396343633808528584033)
                  ·
                    refine ⟨4930797257725356396438025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574396343633808528584033 4930797257725356396438025)
                    ·
                      refine ⟨3698097943294017297328519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930797257725356396438025 3698097943294017297328519)
                      ·
                        rfl

theorem cell23_7202020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_7202020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202020 prefixEnd_7202020 := by exact prefixLift 7202020
  have htrace : WordTrace (prefixWord ++ tailWord_7202020) baseStart_7202020 baseEnd_7202020 := by
    simpa [prefixWord, tailWord_7202020, baseEnd_7202020] using wordTrace_append hprefix tailTrace_7202020
  have hstable : (prefixWord ++ tailWord_7202020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202020).length < 2 ^ (prefixWord ++ tailWord_7202020).sum := by decide
  have hdescent : baseEnd_7202020 < baseStart_7202020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202026 : List Nat := [3, 1, 3, 1, 1, 3, 11]
def baseStart_7202026 : Nat := 118140960795 + 7202026 * 2 ^ 59
def prefixEnd_7202026 : Nat := 4983230072969 + 3 ^ 40 * 7202026 * 2
def baseEnd_7202026 : Nat := 45655568199727707084611

theorem tailTrace_7202026 : CollatzResearch.WordTrace tailWord_7202026 prefixEnd_7202026 45655568199727707084611 := by
  unfold tailWord_7202026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65669867051574321239990483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175119645470864856639974621 65669867051574321239990483)
  ·
    refine ⟨98504800577361481859985725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65669867051574321239990483 98504800577361481859985725)
    ·
      refine ⟨36939300216510555697494647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98504800577361481859985725 36939300216510555697494647)
      ·
        refine ⟨55408950324765833546241971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36939300216510555697494647 55408950324765833546241971)
        ·
          refine ⟨83113425487148750319362957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55408950324765833546241971 83113425487148750319362957)
          ·
            refine ⟨31167534557680781369761109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83113425487148750319362957 31167534557680781369761109)
            ·
              refine ⟨45655568199727707084611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31167534557680781369761109 45655568199727707084611)
              ·
                rfl

theorem cell23_7202026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 11].length) (baseStart_7202026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202026 prefixEnd_7202026 := by exact prefixLift 7202026
  have htrace : WordTrace (prefixWord ++ tailWord_7202026) baseStart_7202026 baseEnd_7202026 := by
    simpa [prefixWord, tailWord_7202026, baseEnd_7202026] using wordTrace_append hprefix tailTrace_7202026
  have hstable : (prefixWord ++ tailWord_7202026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202026).length < 2 ^ (prefixWord ++ tailWord_7202026).sum := by decide
  have hdescent : baseEnd_7202026 < baseStart_7202026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202047 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 2, 4]
def baseStart_7202047 : Nat := 118140960795 + 7202047 * 2 ^ 59
def prefixEnd_7202047 : Nat := 4983230072969 + 3 ^ 40 * 7202047 * 2
def baseEnd_7202047 : Nat := 1232703935757229563896965

theorem tailTrace_7202047 : CollatzResearch.WordTrace tailWord_7202047 prefixEnd_7202047 1232703935757229563896965 := by
  unfold tailWord_7202047
  simp only [CollatzResearch.WordTrace]
  refine ⟨262680234139221205546476395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175120156092814137030984263 262680234139221205546476395)
  ·
    refine ⟨394020351208831808319714593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262680234139221205546476395 394020351208831808319714593)
    ·
      refine ⟨295515263406623856239785945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394020351208831808319714593 295515263406623856239785945)
      ·
        refine ⟨221636447554967892179839459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295515263406623856239785945 221636447554967892179839459)
        ·
          refine ⟨332454671332451838269759189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221636447554967892179839459 332454671332451838269759189)
          ·
            refine ⟨7791906359354339959447481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 332454671332451838269759189 7791906359354339959447481)
            ·
              refine ⟨5843929769515754969585611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791906359354339959447481 5843929769515754969585611)
              ·
                refine ⟨8765894654273632454378417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843929769515754969585611 8765894654273632454378417)
                ·
                  refine ⟨6574420990705224340783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8765894654273632454378417 6574420990705224340783813)
                  ·
                    refine ⟨1232703935757229563896965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6574420990705224340783813 1232703935757229563896965)
                    ·
                      rfl

theorem cell23_7202047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_7202047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202047 prefixEnd_7202047 := by exact prefixLift 7202047
  have htrace : WordTrace (prefixWord ++ tailWord_7202047) baseStart_7202047 baseEnd_7202047 := by
    simpa [prefixWord, tailWord_7202047, baseEnd_7202047] using wordTrace_append hprefix tailTrace_7202047
  have hstable : (prefixWord ++ tailWord_7202047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202047).length < 2 ^ (prefixWord ++ tailWord_7202047).sum := by decide
  have hdescent : baseEnd_7202047 < baseStart_7202047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202053 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_7202053 : Nat := 118140960795 + 7202053 * 2 ^ 59
def prefixEnd_7202053 : Nat := 4983230072969 + 3 ^ 40 * 7202053 * 2
def baseEnd_7202053 : Nat := 3698114888155615668215867

theorem tailTrace_7202053 : CollatzResearch.WordTrace tailWord_7202053 prefixEnd_7202053 3698114888155615668215867 := by
  unfold tailWord_7202053
  simp only [CollatzResearch.WordTrace]
  refine ⟨262680452977199468571194813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175120301984799645714129875 262680452977199468571194813)
  ·
    refine ⟨98505169866449800714198055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262680452977199468571194813 98505169866449800714198055)
    ·
      refine ⟨147757754799674701071297083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98505169866449800714198055 147757754799674701071297083)
      ·
        refine ⟨221636632199512051606945625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147757754799674701071297083 221636632199512051606945625)
        ·
          refine ⟨166227474149634038705209219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221636632199512051606945625 166227474149634038705209219)
          ·
            refine ⟨249341211224451058057813829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166227474149634038705209219 249341211224451058057813829)
            ·
              refine ⟨46751477104584573385840093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249341211224451058057813829 46751477104584573385840093)
              ·
                refine ⟨17531803914219215019690035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46751477104584573385840093 17531803914219215019690035)
                ·
                  refine ⟨26297705871328822529535053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17531803914219215019690035 26297705871328822529535053)
                  ·
                    refine ⟨9861639701748308448575645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26297705871328822529535053 9861639701748308448575645)
                    ·
                      refine ⟨3698114888155615668215867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861639701748308448575645 3698114888155615668215867)
                      ·
                        rfl

theorem cell23_7202053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_7202053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202053 prefixEnd_7202053 := by exact prefixLift 7202053
  have htrace : WordTrace (prefixWord ++ tailWord_7202053) baseStart_7202053 baseEnd_7202053 := by
    simpa [prefixWord, tailWord_7202053, baseEnd_7202053] using wordTrace_append hprefix tailTrace_7202053
  have hstable : (prefixWord ++ tailWord_7202053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202053).length < 2 ^ (prefixWord ++ tailWord_7202053).sum := by decide
  have hdescent : baseEnd_7202053 < baseStart_7202053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202088 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7202088 : Nat := 118140960795 + 7202088 * 2 ^ 59
def prefixEnd_7202088 : Nat := 4983230072969 + 3 ^ 40 * 7202088 * 2
def baseEnd_7202088 : Nat := 3698132859978523031278207

theorem tailTrace_7202088 : CollatzResearch.WordTrace tailWord_7202088 prefixEnd_7202088 3698132859978523031278207 := by
  unfold tailWord_7202088
  simp only [CollatzResearch.WordTrace]
  refine ⟨131340864766036334774359459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175121153021381779699145945 131340864766036334774359459)
  ·
    refine ⟨197011297149054502161539189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131340864766036334774359459 197011297149054502161539189)
    ·
      refine ⟨18469809107723859577644299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197011297149054502161539189 18469809107723859577644299)
      ·
        refine ⟨27704713661585789366466449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18469809107723859577644299 27704713661585789366466449)
        ·
          refine ⟨20778535246189342024849837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27704713661585789366466449 20778535246189342024849837)
          ·
            refine ⟨7791950717321003259318689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20778535246189342024849837 7791950717321003259318689)
            ·
              refine ⟨5843963037990752444489017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791950717321003259318689 5843963037990752444489017)
              ·
                refine ⟨4382972278493064333366763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843963037990752444489017 4382972278493064333366763)
                ·
                  refine ⟨6574458417739596500050145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382972278493064333366763 6574458417739596500050145)
                  ·
                    refine ⟨4930843813304697375037609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574458417739596500050145 4930843813304697375037609)
                    ·
                      refine ⟨3698132859978523031278207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930843813304697375037609 3698132859978523031278207)
                      ·
                        rfl

theorem cell23_7202088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7202088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202088 prefixEnd_7202088 := by exact prefixLift 7202088
  have htrace : WordTrace (prefixWord ++ tailWord_7202088) baseStart_7202088 baseEnd_7202088 := by
    simpa [prefixWord, tailWord_7202088, baseEnd_7202088] using wordTrace_append hprefix tailTrace_7202088
  have hstable : (prefixWord ++ tailWord_7202088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202088).length < 2 ^ (prefixWord ++ tailWord_7202088).sum := by decide
  have hdescent : baseEnd_7202088 < baseStart_7202088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202144 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2]
def baseStart_7202144 : Nat := 118140960795 + 7202144 * 2 ^ 59
def prefixEnd_7202144 : Nat := 4983230072969 + 3 ^ 40 * 7202144 * 2
def baseEnd_7202144 : Nat := 3698161614895174812177949

theorem tailTrace_7202144 : CollatzResearch.WordTrace tailWord_7202144 prefixEnd_7202144 3698161614895174812177949 := by
  unfold tailWord_7202144
  simp only [CollatzResearch.WordTrace]
  refine ⟨131341886009934895556378743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175122514679913194075171657 131341886009934895556378743)
  ·
    refine ⟨197012829014902343334568115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131341886009934895556378743 197012829014902343334568115)
    ·
      refine ⟨295519243522353515001852173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197012829014902343334568115 295519243522353515001852173)
      ·
        refine ⟨110819716320882568125694565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295519243522353515001852173 110819716320882568125694565)
        ·
          refine ⟨20778696810165481523567731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110819716320882568125694565 20778696810165481523567731)
          ·
            refine ⟨31168045215248222285351597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20778696810165481523567731 31168045215248222285351597)
            ·
              refine ⟨11688016955718083357006849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31168045215248222285351597 11688016955718083357006849)
              ·
                refine ⟨8766012716788562517755137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11688016955718083357006849 8766012716788562517755137)
                ·
                  refine ⟨6574509537591421888316353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8766012716788562517755137 6574509537591421888316353)
                  ·
                    refine ⟨4930882153193566416237265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574509537591421888316353 4930882153193566416237265)
                    ·
                      refine ⟨3698161614895174812177949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930882153193566416237265 3698161614895174812177949)
                      ·
                        rfl

theorem cell23_7202144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_7202144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202144 prefixEnd_7202144 := by exact prefixLift 7202144
  have htrace : WordTrace (prefixWord ++ tailWord_7202144) baseStart_7202144 baseEnd_7202144 := by
    simpa [prefixWord, tailWord_7202144, baseEnd_7202144] using wordTrace_append hprefix tailTrace_7202144
  have hstable : (prefixWord ++ tailWord_7202144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202144).length < 2 ^ (prefixWord ++ tailWord_7202144).sum := by decide
  have hdescent : baseEnd_7202144 < baseStart_7202144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202213 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_7202213 : Nat := 118140960795 + 7202213 * 2 ^ 59
def prefixEnd_7202213 : Nat := 4983230072969 + 3 ^ 40 * 7202213 * 2
def baseEnd_7202213 : Nat := 3698197045060335042215131

theorem tailTrace_7202213 : CollatzResearch.WordTrace tailWord_7202213 prefixEnd_7202213 3698197045060335042215131 := by
  unfold tailWord_7202213
  simp only [CollatzResearch.WordTrace]
  refine ⟨262686288656619815897019293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175124192437746543931346195 262686288656619815897019293)
  ·
    refine ⟨98507358246232430961382235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262686288656619815897019293 98507358246232430961382235)
    ·
      refine ⟨147761037369348646442073353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98507358246232430961382235 147761037369348646442073353)
      ·
        refine ⟨110820778027011484831555015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147761037369348646442073353 110820778027011484831555015)
        ·
          refine ⟨166231167040517227247332523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110820778027011484831555015 166231167040517227247332523)
          ·
            refine ⟨249346750560775840870998785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166231167040517227247332523 249346750560775840870998785)
            ·
              refine ⟨187010062920581880653249089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249346750560775840870998785 187010062920581880653249089)
              ·
                refine ⟨140257547190436410489936817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187010062920581880653249089 140257547190436410489936817)
                ·
                  refine ⟨105193160392827307867452613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140257547190436410489936817 105193160392827307867452613)
                  ·
                    refine ⟨19723717573655120225147365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105193160392827307867452613 19723717573655120225147365)
                    ·
                      refine ⟨3698197045060335042215131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19723717573655120225147365 3698197045060335042215131)
                      ·
                        rfl

theorem cell23_7202213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_7202213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202213 prefixEnd_7202213 := by exact prefixLift 7202213
  have htrace : WordTrace (prefixWord ++ tailWord_7202213) baseStart_7202213 baseEnd_7202213 := by
    simpa [prefixWord, tailWord_7202213, baseEnd_7202213] using wordTrace_append hprefix tailTrace_7202213
  have hstable : (prefixWord ++ tailWord_7202213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202213).length < 2 ^ (prefixWord ++ tailWord_7202213).sum := by decide
  have hdescent : baseEnd_7202213 < baseStart_7202213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202237 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_7202237 : Nat := 118140960795 + 7202237 * 2 ^ 59
def prefixEnd_7202237 : Nat := 4983230072969 + 3 ^ 40 * 7202237 * 2
def baseEnd_7202237 : Nat := 3698209368596042948315021

theorem tailTrace_7202237 : CollatzResearch.WordTrace tailWord_7202237 prefixEnd_7202237 3698209368596042948315021 := by
  unfold tailWord_7202237
  simp only [CollatzResearch.WordTrace]
  refine ⟨262687164008532867995892965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175124776005688578663928643 262687164008532867995892965)
  ·
    refine ⟨49253843251599912749229931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262687164008532867995892965 49253843251599912749229931)
    ·
      refine ⟨73880764877399869123844897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49253843251599912749229931 73880764877399869123844897)
      ·
        refine ⟨55410573658049901842883673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73880764877399869123844897 55410573658049901842883673)
        ·
          refine ⟨41557930243537426382162755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55410573658049901842883673 41557930243537426382162755)
          ·
            refine ⟨62336895365306139573244133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41557930243537426382162755 62336895365306139573244133)
            ·
              refine ⟨11688167880994901169983275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62336895365306139573244133 11688167880994901169983275)
              ·
                refine ⟨17532251821492351754974913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11688167880994901169983275 17532251821492351754974913)
                ·
                  refine ⟨13149188866119263816231185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17532251821492351754974913 13149188866119263816231185)
                  ·
                    refine ⟨9861891649589447862173389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13149188866119263816231185 9861891649589447862173389)
                    ·
                      refine ⟨3698209368596042948315021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861891649589447862173389 3698209368596042948315021)
                      ·
                        rfl

theorem cell23_7202237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_7202237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202237 prefixEnd_7202237 := by exact prefixLift 7202237
  have htrace : WordTrace (prefixWord ++ tailWord_7202237) baseStart_7202237 baseEnd_7202237 := by
    simpa [prefixWord, tailWord_7202237, baseEnd_7202237] using wordTrace_append hprefix tailTrace_7202237
  have hstable : (prefixWord ++ tailWord_7202237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202237).length < 2 ^ (prefixWord ++ tailWord_7202237).sum := by decide
  have hdescent : baseEnd_7202237 < baseStart_7202237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202263 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_7202263 : Nat := 118140960795 + 7202263 * 2 ^ 59
def prefixEnd_7202263 : Nat := 4983230072969 + 3 ^ 40 * 7202263 * 2
def baseEnd_7202263 : Nat := 3698222719093059846589901

theorem tailTrace_7202263 : CollatzResearch.WordTrace tailWord_7202263 prefixEnd_7202263 3698222719093059846589901 := by
  unfold tailWord_7202263
  simp only [CollatzResearch.WordTrace]
  refine ⟨262688112306438674436339443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175125408204292449624226295 262688112306438674436339443)
  ·
    refine ⟨394032168459658011654509165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262688112306438674436339443 394032168459658011654509165)
    ·
      refine ⟨147762063172371754370440937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394032168459658011654509165 147762063172371754370440937)
      ·
        refine ⟨110821547379278815777830703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147762063172371754370440937 110821547379278815777830703)
        ·
          refine ⟨166232321068918223666746055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110821547379278815777830703 166232321068918223666746055)
          ·
            refine ⟨249348481603377335500119083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166232321068918223666746055 249348481603377335500119083)
            ·
              refine ⟨374022722405066003250178625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249348481603377335500119083 374022722405066003250178625)
              ·
                refine ⟨280517041803799502437633969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374022722405066003250178625 280517041803799502437633969)
                ·
                  refine ⟨210387781352849626828225477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280517041803799502437633969 210387781352849626828225477)
                  ·
                    refine ⟨39447709003659305030292277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210387781352849626828225477 39447709003659305030292277)
                    ·
                      refine ⟨3698222719093059846589901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39447709003659305030292277 3698222719093059846589901)
                      ·
                        rfl

theorem cell23_7202263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_7202263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202263 prefixEnd_7202263 := by exact prefixLift 7202263
  have htrace : WordTrace (prefixWord ++ tailWord_7202263) baseStart_7202263 baseEnd_7202263 := by
    simpa [prefixWord, tailWord_7202263, baseEnd_7202263] using wordTrace_append hprefix tailTrace_7202263
  have hstable : (prefixWord ++ tailWord_7202263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202263).length < 2 ^ (prefixWord ++ tailWord_7202263).sum := by decide
  have hdescent : baseEnd_7202263 < baseStart_7202263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202294 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7202294 : Nat := 118140960795 + 7202294 * 2 ^ 59
def prefixEnd_7202294 : Nat := 4983230072969 + 3 ^ 40 * 7202294 * 2
def baseEnd_7202294 : Nat := 3698238636993349225302259

theorem tailTrace_7202294 : CollatzResearch.WordTrace tailWord_7202294 prefixEnd_7202294 3698238636993349225302259 := by
  unfold tailWord_7202294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16418077685582897920669871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175126161979550911153811957 16418077685582897920669871)
  ·
    refine ⟨24627116528374346881004807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16418077685582897920669871 24627116528374346881004807)
    ·
      refine ⟨36940674792561520321507211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24627116528374346881004807 36940674792561520321507211)
      ·
        refine ⟨55411012188842280482260817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36940674792561520321507211 55411012188842280482260817)
        ·
          refine ⟨41558259141631710361695613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55411012188842280482260817 41558259141631710361695613)
          ·
            refine ⟨15584347178111891385635855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41558259141631710361695613 15584347178111891385635855)
            ·
              refine ⟨23376520767167837078453783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15584347178111891385635855 23376520767167837078453783)
              ·
                refine ⟨35064781150751755617680675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23376520767167837078453783 35064781150751755617680675)
                ·
                  refine ⟨52597171726127633426521013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35064781150751755617680675 52597171726127633426521013)
                  ·
                    refine ⟨4930984849324465633736345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52597171726127633426521013 4930984849324465633736345)
                    ·
                      refine ⟨3698238636993349225302259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4930984849324465633736345 3698238636993349225302259)
                      ·
                        rfl

theorem cell23_7202294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7202294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202294 prefixEnd_7202294 := by exact prefixLift 7202294
  have htrace : WordTrace (prefixWord ++ tailWord_7202294) baseStart_7202294 baseEnd_7202294 := by
    simpa [prefixWord, tailWord_7202294, baseEnd_7202294] using wordTrace_append hprefix tailTrace_7202294
  have hstable : (prefixWord ++ tailWord_7202294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202294).length < 2 ^ (prefixWord ++ tailWord_7202294).sum := by decide
  have hdescent : baseEnd_7202294 < baseStart_7202294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202300 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_7202300 : Nat := 118140960795 + 7202300 * 2 ^ 59
def prefixEnd_7202300 : Nat := 4983230072969 + 3 ^ 40 * 7202300 * 2
def baseEnd_7202300 : Nat := 1232747239292425400609077

theorem tailTrace_7202300 : CollatzResearch.WordTrace tailWord_7202300 prefixEnd_7202300 1232747239292425400609077 := by
  unfold tailWord_7202300
  simp only [CollatzResearch.WordTrace]
  refine ⟨131344730903652314877718177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175126307871536419836957569 131344730903652314877718177)
  ·
    refine ⟨98508548177739236158288633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131344730903652314877718177 98508548177739236158288633)
    ·
      refine ⟨73881411133304427118716475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98508548177739236158288633 73881411133304427118716475)
      ·
        refine ⟨110822116699956640678074713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73881411133304427118716475 110822116699956640678074713)
        ·
          refine ⟨83116587524967480508556035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110822116699956640678074713 83116587524967480508556035)
          ·
            refine ⟨124674881287451220762834053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83116587524967480508556035 124674881287451220762834053)
            ·
              refine ⟨23376540241397103893031385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124674881287451220762834053 23376540241397103893031385)
              ·
                refine ⟨17532405181047827919773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23376540241397103893031385 17532405181047827919773539)
                ·
                  refine ⟨26298607771571741879660309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17532405181047827919773539 26298607771571741879660309)
                  ·
                    refine ⟨1232747239292425400609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26298607771571741879660309 1232747239292425400609077)
                    ·
                      rfl

theorem cell23_7202300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_7202300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202300 prefixEnd_7202300 := by exact prefixLift 7202300
  have htrace : WordTrace (prefixWord ++ tailWord_7202300) baseStart_7202300 baseEnd_7202300 := by
    simpa [prefixWord, tailWord_7202300, baseEnd_7202300] using wordTrace_append hprefix tailTrace_7202300
  have hstable : (prefixWord ++ tailWord_7202300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202300).length < 2 ^ (prefixWord ++ tailWord_7202300).sum := by decide
  have hdescent : baseEnd_7202300 < baseStart_7202300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202301 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_7202301 : Nat := 118140960795 + 7202301 * 2 ^ 59
def prefixEnd_7202301 : Nat := 4983230072969 + 3 ^ 40 * 7202301 * 2
def baseEnd_7202301 : Nat := 3698242231357930697914727

theorem tailTrace_7202301 : CollatzResearch.WordTrace tailWord_7202301 prefixEnd_7202301 3698242231357930697914727 := by
  unfold tailWord_7202301
  simp only [CollatzResearch.WordTrace]
  refine ⟨262689498280301006926222757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175126332186867337950815171 262689498280301006926222757)
  ·
    refine ⟨49254280927556438798666767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262689498280301006926222757 49254280927556438798666767)
    ·
      refine ⟨73881421391334658198000151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49254280927556438798666767 73881421391334658198000151)
      ·
        refine ⟨110822132087001987297000227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73881421391334658198000151 110822132087001987297000227)
        ·
          refine ⟨166233198130502980945500341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110822132087001987297000227 166233198130502980945500341)
          ·
            refine ⟨15584362324734654463640657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166233198130502980945500341 15584362324734654463640657)
            ·
              refine ⟨11688271743550990847730493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15584362324734654463640657 11688271743550990847730493)
              ·
                refine ⟨4383101903831621567898935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11688271743550990847730493 4383101903831621567898935)
                ·
                  refine ⟨6574652855747432351848403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383101903831621567898935 6574652855747432351848403)
                  ·
                    refine ⟨9861979283621148527772605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6574652855747432351848403 9861979283621148527772605)
                    ·
                      refine ⟨3698242231357930697914727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9861979283621148527772605 3698242231357930697914727)
                      ·
                        rfl

theorem cell23_7202301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_7202301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202301 prefixEnd_7202301 := by exact prefixLift 7202301
  have htrace : WordTrace (prefixWord ++ tailWord_7202301) baseStart_7202301 baseEnd_7202301 := by
    simpa [prefixWord, tailWord_7202301, baseEnd_7202301] using wordTrace_append hprefix tailTrace_7202301
  have hstable : (prefixWord ++ tailWord_7202301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202301).length < 2 ^ (prefixWord ++ tailWord_7202301).sum := by decide
  have hdescent : baseEnd_7202301 < baseStart_7202301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202313 : List Nat := [1, 2, 1, 1, 3, 1, 14]
def baseStart_7202313 : Nat := 118140960795 + 7202313 * 2 ^ 59
def prefixEnd_7202313 : Nat := 4983230072969 + 3 ^ 40 * 7202313 * 2
def baseEnd_7202313 : Nat := 45657387569454131493391

theorem tailTrace_7202313 : CollatzResearch.WordTrace tailWord_7202313 prefixEnd_7202313 45657387569454131493391 := by
  unfold tailWord_7202313
  simp only [CollatzResearch.WordTrace]
  refine ⟨262689935956257532975659593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175126623970838355317106395 262689935956257532975659593)
  ·
    refine ⟨197017451967193149731744695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262689935956257532975659593 197017451967193149731744695)
    ·
      refine ⟨295526177950789724597617043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197017451967193149731744695 295526177950789724597617043)
      ·
        refine ⟨443289266926184586896425565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295526177950789724597617043 443289266926184586896425565)
        ·
          refine ⟨166233475097319220086159587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443289266926184586896425565 166233475097319220086159587)
          ·
            refine ⟨249350212645978830129239381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166233475097319220086159587 249350212645978830129239381)
            ·
              refine ⟨45657387569454131493391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 249350212645978830129239381 45657387569454131493391)
              ·
                rfl

theorem cell23_7202313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 14].length) (baseStart_7202313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202313 prefixEnd_7202313 := by exact prefixLift 7202313
  have htrace : WordTrace (prefixWord ++ tailWord_7202313) baseStart_7202313 baseEnd_7202313 := by
    simpa [prefixWord, tailWord_7202313, baseEnd_7202313] using wordTrace_append hprefix tailTrace_7202313
  have hstable : (prefixWord ++ tailWord_7202313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202313).length < 2 ^ (prefixWord ++ tailWord_7202313).sum := by decide
  have hdescent : baseEnd_7202313 < baseStart_7202313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202337 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7202337 : Nat := 118140960795 + 7202337 * 2 ^ 59
def prefixEnd_7202337 : Nat := 4983230072969 + 3 ^ 40 * 7202337 * 2
def baseEnd_7202337 : Nat := 3698260716661492557064561

theorem tailTrace_7202337 : CollatzResearch.WordTrace tailWord_7202337 prefixEnd_7202337 3698260716661492557064561 := by
  unfold tailWord_7202337
  simp only [CollatzResearch.WordTrace]
  refine ⟨262690811308170585074533265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175127207538780390049688843 262690811308170585074533265)
  ·
    refine ⟨197018108481127938805899949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262690811308170585074533265 197018108481127938805899949)
    ·
      refine ⟨73881790680422977052212481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197018108481127938805899949 73881790680422977052212481)
      ·
        refine ⟨55411343010317232789159361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73881790680422977052212481 55411343010317232789159361)
        ·
          refine ⟨41558507257737924591869521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55411343010317232789159361 41558507257737924591869521)
          ·
            refine ⟨31168880443303443443902141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41558507257737924591869521 31168880443303443443902141)
            ·
              refine ⟨11688330166238791291463303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31168880443303443443902141 11688330166238791291463303)
              ·
                refine ⟨17532495249358186937194955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11688330166238791291463303 17532495249358186937194955)
                ·
                  refine ⟨26298742874037280405792433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17532495249358186937194955 26298742874037280405792433)
                  ·
                    refine ⟨19724057155527960304344325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26298742874037280405792433 19724057155527960304344325)
                    ·
                      refine ⟨3698260716661492557064561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19724057155527960304344325 3698260716661492557064561)
                      ·
                        rfl

theorem cell23_7202337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7202337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202337 prefixEnd_7202337 := by exact prefixLift 7202337
  have htrace : WordTrace (prefixWord ++ tailWord_7202337) baseStart_7202337 baseEnd_7202337 := by
    simpa [prefixWord, tailWord_7202337, baseEnd_7202337] using wordTrace_append hprefix tailTrace_7202337
  have hstable : (prefixWord ++ tailWord_7202337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202337).length < 2 ^ (prefixWord ++ tailWord_7202337).sum := by decide
  have hdescent : baseEnd_7202337 < baseStart_7202337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202375 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_7202375 : Nat := 118140960795 + 7202375 * 2 ^ 59
def prefixEnd_7202375 : Nat := 4983230072969 + 3 ^ 40 * 7202375 * 2
def baseEnd_7202375 : Nat := 3698280228926363408389387

theorem tailTrace_7202375 : CollatzResearch.WordTrace tailWord_7202375 prefixEnd_7202375 3698280228926363408389387 := by
  unfold tailWord_7202375
  simp only [CollatzResearch.WordTrace]
  refine ⟨262692197282032917564416579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175128131521355278376277719 262692197282032917564416579)
  ·
    refine ⟨394038295923049376346624869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262692197282032917564416579 394038295923049376346624869)
    ·
      refine ⟨73882180485571758064992163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394038295923049376346624869 73882180485571758064992163)
      ·
        refine ⟨110823270728357637097488245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73882180485571758064992163 110823270728357637097488245)
        ·
          refine ⟨10389681630783528477889523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110823270728357637097488245 10389681630783528477889523)
          ·
            refine ⟨15584522446175292716834285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10389681630783528477889523 15584522446175292716834285)
            ·
              refine ⟨5844195917315734768812857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15584522446175292716834285 5844195917315734768812857)
              ·
                refine ⟨4383146937986801076609643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844195917315734768812857 4383146937986801076609643)
                ·
                  refine ⟨6574720406980201614914465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383146937986801076609643 6574720406980201614914465)
                  ·
                    refine ⟨4931040305235151211185849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574720406980201614914465 4931040305235151211185849)
                    ·
                      refine ⟨3698280228926363408389387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931040305235151211185849 3698280228926363408389387)
                      ·
                        rfl

theorem cell23_7202375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_7202375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202375 prefixEnd_7202375 := by exact prefixLift 7202375
  have htrace : WordTrace (prefixWord ++ tailWord_7202375) baseStart_7202375 baseEnd_7202375 := by
    simpa [prefixWord, tailWord_7202375, baseEnd_7202375] using wordTrace_append hprefix tailTrace_7202375
  have hstable : (prefixWord ++ tailWord_7202375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202375).length < 2 ^ (prefixWord ++ tailWord_7202375).sum := by decide
  have hdescent : baseEnd_7202375 < baseStart_7202375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202391 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_7202391 : Nat := 118140960795 + 7202391 * 2 ^ 59
def prefixEnd_7202391 : Nat := 4983230072969 + 3 ^ 40 * 7202391 * 2
def baseEnd_7202391 : Nat := 3698288444616835345789313

theorem tailTrace_7202391 : CollatzResearch.WordTrace tailWord_7202391 prefixEnd_7202391 3698288444616835345789313 := by
  unfold tailWord_7202391
  simp only [CollatzResearch.WordTrace]
  refine ⟨262692780849974952296999027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175128520566649968197999351 262692780849974952296999027)
  ·
    refine ⟨394039171274962428445498541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262692780849974952296999027 394039171274962428445498541)
    ·
      refine ⟨147764689228110910667061953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394039171274962428445498541 147764689228110910667061953)
      ·
        refine ⟨110823516921083183000296465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147764689228110910667061953 110823516921083183000296465)
        ·
          refine ⟨83117637690812387250222349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110823516921083183000296465 83117637690812387250222349)
          ·
            refine ⟨31169114134054645218833381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83117637690812387250222349 31169114134054645218833381)
            ·
              refine ⟨5844208900135245978531259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31169114134054645218833381 5844208900135245978531259)
              ·
                refine ⟨8766313350202868967796889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844208900135245978531259 8766313350202868967796889)
                ·
                  refine ⟨6574735012652151725847667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8766313350202868967796889 6574735012652151725847667)
                  ·
                    refine ⟨9862102518978227588771501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6574735012652151725847667 9862102518978227588771501)
                    ·
                      refine ⟨3698288444616835345789313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9862102518978227588771501 3698288444616835345789313)
                      ·
                        rfl

theorem cell23_7202391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_7202391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202391 prefixEnd_7202391 := by exact prefixLift 7202391
  have htrace : WordTrace (prefixWord ++ tailWord_7202391) baseStart_7202391 baseEnd_7202391 := by
    simpa [prefixWord, tailWord_7202391, baseEnd_7202391] using wordTrace_append hprefix tailTrace_7202391
  have hstable : (prefixWord ++ tailWord_7202391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202391).length < 2 ^ (prefixWord ++ tailWord_7202391).sum := by decide
  have hdescent : baseEnd_7202391 < baseStart_7202391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202418 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7202418 : Nat := 118140960795 + 7202418 * 2 ^ 59
def prefixEnd_7202418 : Nat := 4983230072969 + 3 ^ 40 * 7202418 * 2
def baseEnd_7202418 : Nat := 3698302308594506740151689

theorem tailTrace_7202418 : CollatzResearch.WordTrace tailWord_7202418 prefixEnd_7202418 3698302308594506740151689 := by
  unfold tailWord_7202418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65673441405219283977057977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175129177080584757272154605 65673441405219283977057977)
  ·
    refine ⟨49255081053914462982793483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65673441405219283977057977 49255081053914462982793483)
    ·
      refine ⟨73882621580871694474190225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49255081053914462982793483 73882621580871694474190225)
      ·
        refine ⟨55411966185653770855642669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73882621580871694474190225 55411966185653770855642669)
        ·
          refine ⟨20779487319620164070866001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55411966185653770855642669 20779487319620164070866001)
          ·
            refine ⟨15584615489715123053149501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20779487319620164070866001 15584615489715123053149501)
            ·
              refine ⟨5844230808643171144931063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15584615489715123053149501 5844230808643171144931063)
              ·
                refine ⟨8766346212964756717396595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844230808643171144931063 8766346212964756717396595)
                ·
                  refine ⟨13149519319447135076094893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8766346212964756717396595 13149519319447135076094893)
                  ·
                    refine ⟨4931069744792675653535585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13149519319447135076094893 4931069744792675653535585)
                    ·
                      refine ⟨3698302308594506740151689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931069744792675653535585 3698302308594506740151689)
                      ·
                        rfl

theorem cell23_7202418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7202418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202418 prefixEnd_7202418 := by exact prefixLift 7202418
  have htrace : WordTrace (prefixWord ++ tailWord_7202418) baseStart_7202418 baseEnd_7202418 := by
    simpa [prefixWord, tailWord_7202418, baseEnd_7202418] using wordTrace_append hprefix tailTrace_7202418
  have hstable : (prefixWord ++ tailWord_7202418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202418).length < 2 ^ (prefixWord ++ tailWord_7202418).sum := by decide
  have hdescent : baseEnd_7202418 < baseStart_7202418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202504 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_7202504 : Nat := 118140960795 + 7202504 * 2 ^ 59
def prefixEnd_7202504 : Nat := 4983230072969 + 3 ^ 40 * 7202504 * 2
def baseEnd_7202504 : Nat := 3698346467930793403676293

theorem tailTrace_7202504 : CollatzResearch.WordTrace tailWord_7202504 prefixEnd_7202504 3698346467930793403676293 := by
  unfold tailWord_7202504
  simp only [CollatzResearch.WordTrace]
  refine ⟨131348451149282786297931283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175131268199043715063908377 131348451149282786297931283)
  ·
    refine ⟨197022676723924179446896925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131348451149282786297931283 197022676723924179446896925)
    ·
      refine ⟨73883503771471567292586347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197022676723924179446896925 73883503771471567292586347)
      ·
        refine ⟨110825255657207350938879521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73883503771471567292586347 110825255657207350938879521)
        ·
          refine ⟨83118941742905513204159641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110825255657207350938879521 83118941742905513204159641)
          ·
            refine ⟨62339206307179134903119731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83118941742905513204159641 62339206307179134903119731)
            ·
              refine ⟨93508809460768702354679597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62339206307179134903119731 93508809460768702354679597)
              ·
                refine ⟨35065803547788263383004849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93508809460768702354679597 35065803547788263383004849)
                ·
                  refine ⟨26299352660841197537253637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35065803547788263383004849 26299352660841197537253637)
                  ·
                    refine ⟨4931128623907724538235057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26299352660841197537253637 4931128623907724538235057)
                    ·
                      refine ⟨3698346467930793403676293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931128623907724538235057 3698346467930793403676293)
                      ·
                        rfl

theorem cell23_7202504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_7202504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202504 prefixEnd_7202504 := by exact prefixLift 7202504
  have htrace : WordTrace (prefixWord ++ tailWord_7202504) baseStart_7202504 baseEnd_7202504 := by
    simpa [prefixWord, tailWord_7202504, baseEnd_7202504] using wordTrace_append hprefix tailTrace_7202504
  have hstable : (prefixWord ++ tailWord_7202504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202504).length < 2 ^ (prefixWord ++ tailWord_7202504).sum := by decide
  have hdescent : baseEnd_7202504 < baseStart_7202504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202541 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7202541 : Nat := 118140960795 + 7202541 * 2 ^ 59
def prefixEnd_7202541 : Nat := 4983230072969 + 3 ^ 40 * 7202541 * 2
def baseEnd_7202541 : Nat := 3698365466715009758913623

theorem tailTrace_7202541 : CollatzResearch.WordTrace tailWord_7202541 prefixEnd_7202541 3698365466715009758913623 := by
  unfold tailWord_7202541
  simp only [CollatzResearch.WordTrace]
  refine ⟨262698251799431527914959477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175132167866287685276639651 262698251799431527914959477)
  ·
    refine ⟨24627961106196705742027451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262698251799431527914959477 24627961106196705742027451)
    ·
      refine ⟨36941941659295058613041177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24627961106196705742027451 36941941659295058613041177)
      ·
        refine ⟨27706456244471293959780883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36941941659295058613041177 27706456244471293959780883)
        ·
          refine ⟨41559684366706940939671325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27706456244471293959780883 41559684366706940939671325)
          ·
            refine ⟨15584881637515102852376747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41559684366706940939671325 15584881637515102852376747)
            ·
              refine ⟨23377322456272654278565121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15584881637515102852376747 23377322456272654278565121)
              ·
                refine ⟨17532991842204490708923841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23377322456272654278565121 17532991842204490708923841)
                ·
                  refine ⟨13149743881653368031692881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17532991842204490708923841 13149743881653368031692881)
                  ·
                    refine ⟨9862307911240026023769661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13149743881653368031692881 9862307911240026023769661)
                    ·
                      refine ⟨3698365466715009758913623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9862307911240026023769661 3698365466715009758913623)
                      ·
                        rfl

theorem cell23_7202541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7202541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202541 prefixEnd_7202541 := by exact prefixLift 7202541
  have htrace : WordTrace (prefixWord ++ tailWord_7202541) baseStart_7202541 baseEnd_7202541 := by
    simpa [prefixWord, tailWord_7202541, baseEnd_7202541] using wordTrace_append hprefix tailTrace_7202541
  have hstable : (prefixWord ++ tailWord_7202541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202541).length < 2 ^ (prefixWord ++ tailWord_7202541).sum := by decide
  have hdescent : baseEnd_7202541 < baseStart_7202541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202581 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_7202581 : Nat := 118140960795 + 7202581 * 2 ^ 59
def prefixEnd_7202581 : Nat := 4983230072969 + 3 ^ 40 * 7202581 * 2
def baseEnd_7202581 : Nat := 3698386005941189602413439

theorem tailTrace_7202581 : CollatzResearch.WordTrace tailWord_7202581 prefixEnd_7202581 3698386005941189602413439 := by
  unfold tailWord_7202581
  simp only [CollatzResearch.WordTrace]
  refine ⟨262699710719286614746415597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175133140479524409830943731 262699710719286614746415597)
  ·
    refine ⟨98512391519732480529905849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262699710719286614746415597 98512391519732480529905849)
    ·
      refine ⟨73884293639799360397429387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98512391519732480529905849 73884293639799360397429387)
      ·
        refine ⟨110826440459699040596144081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73884293639799360397429387 110826440459699040596144081)
        ·
          refine ⟨83119830344774280447108061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110826440459699040596144081 83119830344774280447108061)
          ·
            refine ⟨31169936379290355167665523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83119830344774280447108061 31169936379290355167665523)
            ·
              refine ⟨46754904568935532751498285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31169936379290355167665523 46754904568935532751498285)
              ·
                refine ⟨17533089213350824781811857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46754904568935532751498285 17533089213350824781811857)
                ·
                  refine ⟨13149816910013118586358893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17533089213350824781811857 13149816910013118586358893)
                  ·
                    refine ⟨4931181341254919469884585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13149816910013118586358893 4931181341254919469884585)
                    ·
                      refine ⟨3698386005941189602413439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931181341254919469884585 3698386005941189602413439)
                      ·
                        rfl

theorem cell23_7202581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_7202581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202581 prefixEnd_7202581 := by exact prefixLift 7202581
  have htrace : WordTrace (prefixWord ++ tailWord_7202581) baseStart_7202581 baseEnd_7202581 := by
    simpa [prefixWord, tailWord_7202581, baseEnd_7202581] using wordTrace_append hprefix tailTrace_7202581
  have hstable : (prefixWord ++ tailWord_7202581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202581).length < 2 ^ (prefixWord ++ tailWord_7202581).sum := by decide
  have hdescent : baseEnd_7202581 < baseStart_7202581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202587 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 1, 6]
def baseStart_7202587 : Nat := 118140960795 + 7202587 * 2 ^ 59
def prefixEnd_7202587 : Nat := 4983230072969 + 3 ^ 40 * 7202587 * 2
def baseEnd_7202587 : Nat := 1232796362275038859646137

theorem tailTrace_7202587 : CollatzResearch.WordTrace tailWord_7202587 prefixEnd_7202587 1232796362275038859646137 := by
  unfold tailWord_7202587
  simp only [CollatzResearch.WordTrace]
  refine ⟨262699929557264877771134015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175133286371509918514089343 262699929557264877771134015)
  ·
    refine ⟨394049894335897316656701023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262699929557264877771134015 394049894335897316656701023)
    ·
      refine ⟨591074841503845974985051535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394049894335897316656701023 591074841503845974985051535)
      ·
        refine ⟨886612262255768962477577303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591074841503845974985051535 886612262255768962477577303)
        ·
          refine ⟨1329918393383653443716365955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886612262255768962477577303 1329918393383653443716365955)
          ·
            refine ⟨1994877590075480165574548933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329918393383653443716365955 1994877590075480165574548933)
            ·
              refine ⟨374039548139152531045227925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1994877590075480165574548933 374039548139152531045227925)
              ·
                refine ⟨17533103819022774892745059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374039548139152531045227925 17533103819022774892745059)
                ·
                  refine ⟨26299655728534162339117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17533103819022774892745059 26299655728534162339117589)
                  ·
                    refine ⟨1232796362275038859646137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26299655728534162339117589 1232796362275038859646137)
                    ·
                      rfl

theorem cell23_7202587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 6].length) (baseStart_7202587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202587 prefixEnd_7202587 := by exact prefixLift 7202587
  have htrace : WordTrace (prefixWord ++ tailWord_7202587) baseStart_7202587 baseEnd_7202587 := by
    simpa [prefixWord, tailWord_7202587, baseEnd_7202587] using wordTrace_append hprefix tailTrace_7202587
  have hstable : (prefixWord ++ tailWord_7202587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202587).length < 2 ^ (prefixWord ++ tailWord_7202587).sum := by decide
  have hdescent : baseEnd_7202587 < baseStart_7202587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202588 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_7202588 : Nat := 118140960795 + 7202588 * 2 ^ 59
def prefixEnd_7202588 : Nat := 4983230072969 + 3 ^ 40 * 7202588 * 2
def baseEnd_7202588 : Nat := 3698389600305771075025907

theorem tailTrace_7202588 : CollatzResearch.WordTrace tailWord_7202588 prefixEnd_7202588 3698389600305771075025907 := by
  unfold tailWord_7202588
  simp only [CollatzResearch.WordTrace]
  refine ⟨131349983015130627470960209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175133310686840836627946945 131349983015130627470960209)
  ·
    refine ⟨98512487261347970603220157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131349983015130627470960209 98512487261347970603220157)
    ·
      refine ⟨36942182723005488976207559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98512487261347970603220157 36942182723005488976207559)
      ·
        refine ⟨55413274084508233464311339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36942182723005488976207559 55413274084508233464311339)
        ·
          refine ⟨83119911126762350196467009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55413274084508233464311339 83119911126762350196467009)
          ·
            refine ⟨62339933345071762647350257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83119911126762350196467009 62339933345071762647350257)
            ·
              refine ⟨46754950008803821985512693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62339933345071762647350257 46754950008803821985512693)
              ·
                refine ⟨4383276563325358311141815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46754950008803821985512693 4383276563325358311141815)
                ·
                  refine ⟨6574914844988037466712723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383276563325358311141815 6574914844988037466712723)
                  ·
                    refine ⟨9862372267482056200069085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6574914844988037466712723 9862372267482056200069085)
                    ·
                      refine ⟨3698389600305771075025907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9862372267482056200069085 3698389600305771075025907)
                      ·
                        rfl

theorem cell23_7202588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_7202588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202588 prefixEnd_7202588 := by exact prefixLift 7202588
  have htrace : WordTrace (prefixWord ++ tailWord_7202588) baseStart_7202588 baseEnd_7202588 := by
    simpa [prefixWord, tailWord_7202588, baseEnd_7202588] using wordTrace_append hprefix tailTrace_7202588
  have hstable : (prefixWord ++ tailWord_7202588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202588).length < 2 ^ (prefixWord ++ tailWord_7202588).sum := by decide
  have hdescent : baseEnd_7202588 < baseStart_7202588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202591 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 1, 5]
def baseStart_7202591 : Nat := 118140960795 + 7202591 * 2 ^ 59
def prefixEnd_7202591 : Nat := 4983230072969 + 3 ^ 40 * 7202591 * 2
def baseEnd_7202591 : Nat := 1232797046915911521096131

theorem tailTrace_7202591 : CollatzResearch.WordTrace tailWord_7202591 prefixEnd_7202591 1232797046915911521096131 := by
  unfold tailWord_7202591
  simp only [CollatzResearch.WordTrace]
  refine ⟨262700075449250386454279627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175133383632833590969519751 262700075449250386454279627)
  ·
    refine ⟨394050113173875579681419441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262700075449250386454279627 394050113173875579681419441)
    ·
      refine ⟨295537584880406684761064581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394050113173875579681419441 295537584880406684761064581)
      ·
        refine ⟨55413297165076253392699609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295537584880406684761064581 55413297165076253392699609)
        ·
          refine ⟨41559972873807190044524707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55413297165076253392699609 41559972873807190044524707)
          ·
            refine ⟨62339959310710785066787061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41559972873807190044524707 62339959310710785066787061)
            ·
              refine ⟨5844371185379136100011287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62339959310710785066787061 5844371185379136100011287)
              ·
                refine ⟨8766556778068704150016931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844371185379136100011287 8766556778068704150016931)
                ·
                  refine ⟨13149835167103056225025397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8766556778068704150016931 13149835167103056225025397)
                  ·
                    refine ⟨1232797046915911521096131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13149835167103056225025397 1232797046915911521096131)
                    ·
                      rfl

theorem cell23_7202591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_7202591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202591 prefixEnd_7202591 := by exact prefixLift 7202591
  have htrace : WordTrace (prefixWord ++ tailWord_7202591) baseStart_7202591 baseEnd_7202591 := by
    simpa [prefixWord, tailWord_7202591, baseEnd_7202591] using wordTrace_append hprefix tailTrace_7202591
  have hstable : (prefixWord ++ tailWord_7202591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202591).length < 2 ^ (prefixWord ++ tailWord_7202591).sum := by decide
  have hdescent : baseEnd_7202591 < baseStart_7202591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202621 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_7202621 : Nat := 118140960795 + 7202621 * 2 ^ 59
def prefixEnd_7202621 : Nat := 4983230072969 + 3 ^ 40 * 7202621 * 2
def baseEnd_7202621 : Nat := 1232802181722456481971085

theorem tailTrace_7202621 : CollatzResearch.WordTrace tailWord_7202621 prefixEnd_7202621 1232802181722456481971085 := by
  unfold tailWord_7202621
  simp only [CollatzResearch.WordTrace]
  refine ⟨262701169639141701577871717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175134113092761134385247811 262701169639141701577871717)
  ·
    refine ⟨49256469307339069045850947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262701169639141701577871717 49256469307339069045850947)
    ·
      refine ⟨73884703961008603568776421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49256469307339069045850947 73884703961008603568776421)
      ·
        refine ⟨13853381992689113169145579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73884703961008603568776421 13853381992689113169145579)
        ·
          refine ⟨20780072989033669753718369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13853381992689113169145579 20780072989033669753718369)
          ·
            refine ⟨15585054741775252315288777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20780072989033669753718369 15585054741775252315288777)
            ·
              refine ⟨11688791056331439236466583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15585054741775252315288777 11688791056331439236466583)
              ·
                refine ⟨17533186584497158854699875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11688791056331439236466583 17533186584497158854699875)
                ·
                  refine ⟨26299779876745738282049813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17533186584497158854699875 26299779876745738282049813)
                  ·
                    refine ⟨1232802181722456481971085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26299779876745738282049813 1232802181722456481971085)
                    ·
                      rfl

theorem cell23_7202621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_7202621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202621 prefixEnd_7202621 := by exact prefixLift 7202621
  have htrace : WordTrace (prefixWord ++ tailWord_7202621) baseStart_7202621 baseEnd_7202621 := by
    simpa [prefixWord, tailWord_7202621, baseEnd_7202621] using wordTrace_append hprefix tailTrace_7202621
  have hstable : (prefixWord ++ tailWord_7202621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202621).length < 2 ^ (prefixWord ++ tailWord_7202621).sum := by decide
  have hdescent : baseEnd_7202621 < baseStart_7202621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202634 : List Nat := [3, 1, 2, 1, 1, 1, 7, 7]
def baseStart_7202634 : Nat := 118140960795 + 7202634 * 2 ^ 59
def prefixEnd_7202634 : Nat := 4983230072969 + 3 ^ 40 * 7202634 * 2
def baseEnd_7202634 : Nat := 136978267422810292409285

theorem tailTrace_7202634 : CollatzResearch.WordTrace tailWord_7202634 prefixEnd_7202634 136978267422810292409285 := by
  unfold tailWord_7202634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65675410947023651199523739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175134429192063069865396637 65675410947023651199523739)
  ·
    refine ⟨98513116420535476799285609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65675410947023651199523739 98513116420535476799285609)
    ·
      refine ⟨73884837315401607599464207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98513116420535476799285609 73884837315401607599464207)
      ·
        refine ⟨110827255973102411399196311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73884837315401607599464207 110827255973102411399196311)
        ·
          refine ⟨166240883959653617098794467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110827255973102411399196311 166240883959653617098794467)
          ·
            refine ⟨249361325939480425648191701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166240883959653617098794467 249361325939480425648191701)
            ·
              refine ⟨5844406076706572476129493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 249361325939480425648191701 5844406076706572476129493)
              ·
                refine ⟨136978267422810292409285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5844406076706572476129493 136978267422810292409285)
                ·
                  rfl

theorem cell23_7202634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_7202634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202634 prefixEnd_7202634 := by exact prefixLift 7202634
  have htrace : WordTrace (prefixWord ++ tailWord_7202634) baseStart_7202634 baseEnd_7202634 := by
    simpa [prefixWord, tailWord_7202634, baseEnd_7202634] using wordTrace_append hprefix tailTrace_7202634
  have hstable : (prefixWord ++ tailWord_7202634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202634).length < 2 ^ (prefixWord ++ tailWord_7202634).sum := by decide
  have hdescent : baseEnd_7202634 < baseStart_7202634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202645 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7202645 : Nat := 118140960795 + 7202645 * 2 ^ 59
def prefixEnd_7202645 : Nat := 4983230072969 + 3 ^ 40 * 7202645 * 2
def baseEnd_7202645 : Nat := 3698418868703077352013145

theorem tailTrace_7202645 : CollatzResearch.WordTrace tailWord_7202645 prefixEnd_7202645 3698418868703077352013145 := by
  unfold tailWord_7202645
  simp only [CollatzResearch.WordTrace]
  refine ⟨262702044991054753676745389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175134696660703169117830259 262702044991054753676745389)
  ·
    refine ⟨98513266871645532628779521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262702044991054753676745389 98513266871645532628779521)
    ·
      refine ⟨73884950153734149471584641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98513266871645532628779521 73884950153734149471584641)
      ·
        refine ⟨55413712615300612103688481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73884950153734149471584641 55413712615300612103688481)
        ·
          refine ⟨41560284461475459077766361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55413712615300612103688481 41560284461475459077766361)
          ·
            refine ⟨31170213346106594308324771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41560284461475459077766361 31170213346106594308324771)
            ·
              refine ⟨46755320019159891462487157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31170213346106594308324771 46755320019159891462487157)
              ·
                refine ⟨4383311251796239824608171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46755320019159891462487157 4383311251796239824608171)
                ·
                  refine ⟨6574966877694359736912257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383311251796239824608171 6574966877694359736912257)
                  ·
                    refine ⟨4931225158270769802684193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6574966877694359736912257 4931225158270769802684193)
                    ·
                      refine ⟨3698418868703077352013145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931225158270769802684193 3698418868703077352013145)
                      ·
                        rfl

theorem cell23_7202645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7202645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202645 prefixEnd_7202645 := by exact prefixLift 7202645
  have htrace : WordTrace (prefixWord ++ tailWord_7202645) baseStart_7202645 baseEnd_7202645 := by
    simpa [prefixWord, tailWord_7202645, baseEnd_7202645] using wordTrace_append hprefix tailTrace_7202645
  have hstable : (prefixWord ++ tailWord_7202645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202645).length < 2 ^ (prefixWord ++ tailWord_7202645).sum := by decide
  have hdescent : baseEnd_7202645 < baseStart_7202645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202688 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2]
def baseStart_7202688 : Nat := 118140960795 + 7202688 * 2 ^ 59
def prefixEnd_7202688 : Nat := 4983230072969 + 3 ^ 40 * 7202688 * 2
def baseEnd_7202688 : Nat := 3698440948371220683775447

theorem tailTrace_7202688 : CollatzResearch.WordTrace tailWord_7202688 prefixEnd_7202688 3698440948371220683775447 := by
  unfold tailWord_7202688
  simp only [CollatzResearch.WordTrace]
  refine ⟨131351806664949486010280359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175135742219932648013707145 131351806664949486010280359)
  ·
    refine ⟨197027709997424229015420539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131351806664949486010280359 197027709997424229015420539)
    ·
      refine ⟨295541564996136343523130809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197027709997424229015420539 295541564996136343523130809)
      ·
        refine ⟨221656173747102257642348107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295541564996136343523130809 221656173747102257642348107)
        ·
          refine ⟨332484260620653386463522161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221656173747102257642348107 332484260620653386463522161)
          ·
            refine ⟨249363195465490039847641621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332484260620653386463522161 249363195465490039847641621)
            ·
              refine ⟨11688899787444845617858201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249363195465490039847641621 11688899787444845617858201)
              ·
                refine ⟨8766674840583634213393651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11688899787444845617858201 8766674840583634213393651)
                ·
                  refine ⟨13150012260875451320090477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8766674840583634213393651 13150012260875451320090477)
                  ·
                    refine ⟨4931254597828294245033929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13150012260875451320090477 4931254597828294245033929)
                    ·
                      refine ⟨3698440948371220683775447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931254597828294245033929 3698440948371220683775447)
                      ·
                        rfl

theorem cell23_7202688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_7202688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202688 prefixEnd_7202688 := by exact prefixLift 7202688
  have htrace : WordTrace (prefixWord ++ tailWord_7202688) baseStart_7202688 baseEnd_7202688 := by
    simpa [prefixWord, tailWord_7202688, baseEnd_7202688] using wordTrace_append hprefix tailTrace_7202688
  have hstable : (prefixWord ++ tailWord_7202688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202688).length < 2 ^ (prefixWord ++ tailWord_7202688).sum := by decide
  have hdescent : baseEnd_7202688 < baseStart_7202688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202915 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 3, 2, 2]
def baseStart_7202915 : Nat := 118140960795 + 7202915 * 2 ^ 59
def prefixEnd_7202915 : Nat := 4983230072969 + 3 ^ 40 * 7202915 * 2
def baseEnd_7202915 : Nat := 3698557508479791295636903

theorem tailTrace_7202915 : CollatzResearch.WordTrace tailWord_7202915 prefixEnd_7202915 3698557508479791295636903 := by
  unfold tailWord_7202915
  simp only [CollatzResearch.WordTrace]
  refine ⟨262711892700076589789074199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175141261800051059859382799 262711892700076589789074199)
  ·
    refine ⟨394067839050114884683611299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262711892700076589789074199 394067839050114884683611299)
    ·
      refine ⟨591101758575172327025416949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394067839050114884683611299 591101758575172327025416949)
      ·
        refine ⟨55415789866422405658632839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 591101758575172327025416949 55415789866422405658632839)
        ·
          refine ⟨83123684799633608487949259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55415789866422405658632839 83123684799633608487949259)
          ·
            refine ⟨124685527199450412731923889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83123684799633608487949259 124685527199450412731923889)
            ·
              refine ⟨93514145399587809548942917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124685527199450412731923889 93514145399587809548942917)
              ·
                refine ⟨17533902262422714290426797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93514145399587809548942917 17533902262422714290426797)
                ·
                  refine ⟨6575213348408517858910049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17533902262422714290426797 6575213348408517858910049)
                  ·
                    refine ⟨4931410011306388394182537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575213348408517858910049 4931410011306388394182537)
                    ·
                      refine ⟨3698557508479791295636903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931410011306388394182537 3698557508479791295636903)
                      ·
                        rfl

theorem cell23_7202915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_7202915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202915 prefixEnd_7202915 := by exact prefixLift 7202915
  have htrace : WordTrace (prefixWord ++ tailWord_7202915) baseStart_7202915 baseEnd_7202915 := by
    simpa [prefixWord, tailWord_7202915, baseEnd_7202915] using wordTrace_append hprefix tailTrace_7202915
  have hstable : (prefixWord ++ tailWord_7202915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202915).length < 2 ^ (prefixWord ++ tailWord_7202915).sum := by decide
  have hdescent : baseEnd_7202915 < baseStart_7202915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202928 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_7202928 : Nat := 118140960795 + 7202928 * 2 ^ 59
def prefixEnd_7202928 : Nat := 4983230072969 + 3 ^ 40 * 7202928 * 2
def baseEnd_7202928 : Nat := 3698564183728299744774343

theorem tailTrace_7202928 : CollatzResearch.WordTrace tailWord_7202928 prefixEnd_7202928 3698564183728299744774343 := by
  unfold tailWord_7202928
  simp only [CollatzResearch.WordTrace]
  refine ⟨131356183424514746504648719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175141577899352995339531625 131356183424514746504648719)
  ·
    refine ⟨197034275136772119756973079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131356183424514746504648719 197034275136772119756973079)
    ·
      refine ⟨295551412705158179635459619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197034275136772119756973079 295551412705158179635459619)
      ·
        refine ⟨443327119057737269453189429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295551412705158179635459619 443327119057737269453189429)
        ·
          refine ⟨41561917411662869011236509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 443327119057737269453189429 41561917411662869011236509)
          ·
            refine ⟨15585719029373575879213691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41561917411662869011236509 15585719029373575879213691)
            ·
              refine ⟨23378578544060363818820537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15585719029373575879213691 23378578544060363818820537)
              ·
                refine ⟨17533933908045272864115403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23378578544060363818820537 17533933908045272864115403)
                ·
                  refine ⟨26300900862067909296173105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17533933908045272864115403 26300900862067909296173105)
                  ·
                    refine ⟨19725675646550931972129829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26300900862067909296173105 19725675646550931972129829)
                    ·
                      refine ⟨3698564183728299744774343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19725675646550931972129829 3698564183728299744774343)
                      ·
                        rfl

theorem cell23_7202928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_7202928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202928 prefixEnd_7202928 := by exact prefixLift 7202928
  have htrace : WordTrace (prefixWord ++ tailWord_7202928) baseStart_7202928 baseEnd_7202928 := by
    simpa [prefixWord, tailWord_7202928, baseEnd_7202928] using wordTrace_append hprefix tailTrace_7202928
  have hstable : (prefixWord ++ tailWord_7202928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202928).length < 2 ^ (prefixWord ++ tailWord_7202928).sum := by decide
  have hdescent : baseEnd_7202928 < baseStart_7202928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202948 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_7202948 : Nat := 118140960795 + 7202948 * 2 ^ 59
def prefixEnd_7202948 : Nat := 4983230072969 + 3 ^ 40 * 7202948 * 2
def baseEnd_7202948 : Nat := 3698574453341389666524251

theorem tailTrace_7202948 : CollatzResearch.WordTrace tailWord_7202948 prefixEnd_7202948 3698574453341389666524251 := by
  unfold tailWord_7202948
  simp only [CollatzResearch.WordTrace]
  refine ⟨131356548154478518212512749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175142064205971357616683665 131356548154478518212512749)
  ·
    refine ⟨49258705557929444329692281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131356548154478518212512749 49258705557929444329692281)
    ·
      refine ⟨36944029168447083247269211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49258705557929444329692281 36944029168447083247269211)
      ·
        refine ⟨55416043752670624870903817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36944029168447083247269211 55416043752670624870903817)
        ·
          refine ⟨41562032814502968653177863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55416043752670624870903817 41562032814502968653177863)
          ·
            refine ⟨62343049221754452979766795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41562032814502968653177863 62343049221754452979766795)
            ·
              refine ⟨93514573832631679469650193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62343049221754452979766795 93514573832631679469650193)
              ·
                refine ⟨70135930374473759602237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93514573832631679469650193 70135930374473759602237645)
                ·
                  refine ⟨26300973890427659850839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70135930374473759602237645 26300973890427659850839117)
                  ·
                    refine ⟨9862865208910372444064669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26300973890427659850839117 9862865208910372444064669)
                    ·
                      refine ⟨3698574453341389666524251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9862865208910372444064669 3698574453341389666524251)
                      ·
                        rfl

theorem cell23_7202948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_7202948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202948 prefixEnd_7202948 := by exact prefixLift 7202948
  have htrace : WordTrace (prefixWord ++ tailWord_7202948) baseStart_7202948 baseEnd_7202948 := by
    simpa [prefixWord, tailWord_7202948, baseEnd_7202948] using wordTrace_append hprefix tailTrace_7202948
  have hstable : (prefixWord ++ tailWord_7202948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202948).length < 2 ^ (prefixWord ++ tailWord_7202948).sum := by decide
  have hdescent : baseEnd_7202948 < baseStart_7202948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202949 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 1, 2, 2]
def baseStart_7202949 : Nat := 118140960795 + 7202949 * 2 ^ 59
def prefixEnd_7202949 : Nat := 4983230072969 + 3 ^ 40 * 7202949 * 2
def baseEnd_7202949 : Nat := 3698574966822044162611747

theorem tailTrace_7202949 : CollatzResearch.WordTrace tailWord_7202949 prefixEnd_7202949 3698574966822044162611747 := by
  unfold tailWord_7202949
  simp only [CollatzResearch.WordTrace]
  refine ⟨262713132781953413595811901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175142088521302275730541267 262713132781953413595811901)
  ·
    refine ⟨98517424793232530098429463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262713132781953413595811901 98517424793232530098429463)
    ·
      refine ⟨147776137189848795147644195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98517424793232530098429463 147776137189848795147644195)
      ·
        refine ⟨221664205784773192721466293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147776137189848795147644195 221664205784773192721466293)
        ·
          refine ⟨20781019292322486817637465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221664205784773192721466293 20781019292322486817637465)
          ·
            refine ⟨15585764469241865113228099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20781019292322486817637465 15585764469241865113228099)
            ·
              refine ⟨23378646703862797669842149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15585764469241865113228099 23378646703862797669842149)
              ·
                refine ⟨4383496256974274563095403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23378646703862797669842149 4383496256974274563095403)
                ·
                  refine ⟨6575244385461411844643105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383496256974274563095403 6575244385461411844643105)
                  ·
                    refine ⟨4931433289096058883482329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575244385461411844643105 4931433289096058883482329)
                    ·
                      refine ⟨3698574966822044162611747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931433289096058883482329 3698574966822044162611747)
                      ·
                        rfl

theorem cell23_7202949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_7202949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202949 prefixEnd_7202949 := by exact prefixLift 7202949
  have htrace : WordTrace (prefixWord ++ tailWord_7202949) baseStart_7202949 baseEnd_7202949 := by
    simpa [prefixWord, tailWord_7202949, baseEnd_7202949] using wordTrace_append hprefix tailTrace_7202949
  have hstable : (prefixWord ++ tailWord_7202949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202949).length < 2 ^ (prefixWord ++ tailWord_7202949).sum := by decide
  have hdescent : baseEnd_7202949 < baseStart_7202949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202951 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 7]
def baseStart_7202951 : Nat := 118140960795 + 7202951 * 2 ^ 59
def prefixEnd_7202951 : Nat := 4983230072969 + 3 ^ 40 * 7202951 * 2
def baseEnd_7202951 : Nat := 1232858664594451051595579

theorem tailTrace_7202951 : CollatzResearch.WordTrace tailWord_7202951 prefixEnd_7202951 1232858664594451051595579 := by
  unfold tailWord_7202951
  simp only [CollatzResearch.WordTrace]
  refine ⟨262713205727946167937384707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175142137151964111958256471 262713205727946167937384707)
  ·
    refine ⟨394069808591919251906077061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262713205727946167937384707 394069808591919251906077061)
    ·
      refine ⟨73888089110984859732389449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394069808591919251906077061 73888089110984859732389449)
      ·
        refine ⟨55416066833238644799292087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73888089110984859732389449 55416066833238644799292087)
        ·
          refine ⟨83124100249857967198938131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55416066833238644799292087 83124100249857967198938131)
          ·
            refine ⟨124686150374786950798407197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83124100249857967198938131 124686150374786950798407197)
            ·
              refine ⟨46757306390545106549402699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124686150374786950798407197 46757306390545106549402699)
              ·
                refine ⟨70135959585817659824104049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46757306390545106549402699 70135959585817659824104049)
                ·
                  refine ⟨52601969689363244868078037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70135959585817659824104049 52601969689363244868078037)
                  ·
                    refine ⟨1232858664594451051595579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52601969689363244868078037 1232858664594451051595579)
                    ·
                      rfl

theorem cell23_7202951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_7202951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202951 prefixEnd_7202951 := by exact prefixLift 7202951
  have htrace : WordTrace (prefixWord ++ tailWord_7202951) baseStart_7202951 baseEnd_7202951 := by
    simpa [prefixWord, tailWord_7202951, baseEnd_7202951] using wordTrace_append hprefix tailTrace_7202951
  have hstable : (prefixWord ++ tailWord_7202951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202951).length < 2 ^ (prefixWord ++ tailWord_7202951).sum := by decide
  have hdescent : baseEnd_7202951 < baseStart_7202951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202965 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_7202965 : Nat := 118140960795 + 7202965 * 2 ^ 59
def prefixEnd_7202965 : Nat := 4983230072969 + 3 ^ 40 * 7202965 * 2
def baseEnd_7202965 : Nat := 3698583182512516100011673

theorem tailTrace_7202965 : CollatzResearch.WordTrace tailWord_7202965 prefixEnd_7202965 3698583182512516100011673 := by
  unfold tailWord_7202965
  simp only [CollatzResearch.WordTrace]
  refine ⟨262713716349895448328394349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175142477566596965552262899 262713716349895448328394349)
  ·
    refine ⟨98517643631210793123147881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262713716349895448328394349 98517643631210793123147881)
    ·
      refine ⟨73888232723408094842360911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98517643631210793123147881 73888232723408094842360911)
      ·
        refine ⟨110832349085112142263541367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73888232723408094842360911 110832349085112142263541367)
        ·
          refine ⟨166248523627668213395312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110832349085112142263541367 166248523627668213395312051)
          ·
            refine ⟨249372785441502320092968077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166248523627668213395312051 249372785441502320092968077)
            ·
              refine ⟨93514794540563370034863029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249372785441502320092968077 93514794540563370034863029)
              ·
                refine ⟨8767011988177815940768409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93514794540563370034863029 8767011988177815940768409)
                ·
                  refine ⟨6575258991133361955576307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8767011988177815940768409 6575258991133361955576307)
                  ·
                    refine ⟨9862888486700042933364461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6575258991133361955576307 9862888486700042933364461)
                    ·
                      refine ⟨3698583182512516100011673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9862888486700042933364461 3698583182512516100011673)
                      ·
                        rfl

theorem cell23_7202965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_7202965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202965 prefixEnd_7202965 := by exact prefixLift 7202965
  have htrace : WordTrace (prefixWord ++ tailWord_7202965) baseStart_7202965 baseEnd_7202965 := by
    simpa [prefixWord, tailWord_7202965, baseEnd_7202965] using wordTrace_append hprefix tailTrace_7202965
  have hstable : (prefixWord ++ tailWord_7202965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202965).length < 2 ^ (prefixWord ++ tailWord_7202965).sum := by decide
  have hdescent : baseEnd_7202965 < baseStart_7202965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202971 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_7202971 : Nat := 118140960795 + 7202971 * 2 ^ 59
def prefixEnd_7202971 : Nat := 4983230072969 + 3 ^ 40 * 7202971 * 2
def baseEnd_7202971 : Nat := 3698586263396443076536645

theorem tailTrace_7202971 : CollatzResearch.WordTrace tailWord_7202971 prefixEnd_7202971 3698586263396443076536645 := by
  unfold tailWord_7202971
  simp only [CollatzResearch.WordTrace]
  refine ⟨262713935187873711353112767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175142623458582474235408511 262713935187873711353112767)
  ·
    refine ⟨394070902781810567029669151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262713935187873711353112767 394070902781810567029669151)
    ·
      refine ⟨591106354172715850544503727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394070902781810567029669151 591106354172715850544503727)
      ·
        refine ⟨886659531259073775816755591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591106354172715850544503727 886659531259073775816755591)
        ·
          refine ⟨1329989296888610663725133387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886659531259073775816755591 1329989296888610663725133387)
          ·
            refine ⟨1994983945332915995587700081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329989296888610663725133387 1994983945332915995587700081)
            ·
              refine ⟨1496237958999686996690775061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994983945332915995587700081 1496237958999686996690775061)
              ·
                refine ⟨70136154328110327969880081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1496237958999686996690775061 70136154328110327969880081)
                ·
                  refine ⟨52602115746082745977410061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70136154328110327969880081 52602115746082745977410061)
                  ·
                    refine ⟨19725793404781029741528773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52602115746082745977410061 19725793404781029741528773)
                    ·
                      refine ⟨3698586263396443076536645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19725793404781029741528773 3698586263396443076536645)
                      ·
                        rfl

theorem cell23_7202971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_7202971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202971 prefixEnd_7202971 := by exact prefixLift 7202971
  have htrace : WordTrace (prefixWord ++ tailWord_7202971) baseStart_7202971 baseEnd_7202971 := by
    simpa [prefixWord, tailWord_7202971, baseEnd_7202971] using wordTrace_append hprefix tailTrace_7202971
  have hstable : (prefixWord ++ tailWord_7202971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202971).length < 2 ^ (prefixWord ++ tailWord_7202971).sum := by decide
  have hdescent : baseEnd_7202971 < baseStart_7202971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202981 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_7202981 : Nat := 118140960795 + 7202981 * 2 ^ 59
def prefixEnd_7202981 : Nat := 4983230072969 + 3 ^ 40 * 7202981 * 2
def baseEnd_7202981 : Nat := 1232863799400996012470533

theorem tailTrace_7202981 : CollatzResearch.WordTrace tailWord_7202981 prefixEnd_7202981 1232863799400996012470533 := by
  unfold tailWord_7202981
  simp only [CollatzResearch.WordTrace]
  refine ⟨262714299917837483060976797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175142866611891655373984531 262714299917837483060976797)
  ·
    refine ⟨98517862469189056147866299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262714299917837483060976797 98517862469189056147866299)
    ·
      refine ⟨147776793703783584221799449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98517862469189056147866299 147776793703783584221799449)
      ·
        refine ⟨110832595277837688166349587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147776793703783584221799449 110832595277837688166349587)
        ·
          refine ⟨166248892916756532249524381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110832595277837688166349587 166248892916756532249524381)
          ·
            refine ⟨62343334843783699593571643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166248892916756532249524381 62343334843783699593571643)
            ·
              refine ⟨93515002265675549390357465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62343334843783699593571643 93515002265675549390357465)
              ·
                refine ⟨70136251699256662042768099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93515002265675549390357465 70136251699256662042768099)
                ·
                  refine ⟨105204377548884993064152149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70136251699256662042768099 105204377548884993064152149)
                  ·
                    refine ⟨1232863799400996012470533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105204377548884993064152149 1232863799400996012470533)
                    ·
                      rfl

theorem cell23_7202981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_7202981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202981 prefixEnd_7202981 := by exact prefixLift 7202981
  have htrace : WordTrace (prefixWord ++ tailWord_7202981) baseStart_7202981 baseEnd_7202981 := by
    simpa [prefixWord, tailWord_7202981, baseEnd_7202981] using wordTrace_append hprefix tailTrace_7202981
  have hstable : (prefixWord ++ tailWord_7202981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202981).length < 2 ^ (prefixWord ++ tailWord_7202981).sum := by decide
  have hdescent : baseEnd_7202981 < baseStart_7202981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202986 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7202986 : Nat := 118140960795 + 7202986 * 2 ^ 59
def prefixEnd_7202986 : Nat := 4983230072969 + 3 ^ 40 * 7202986 * 2
def baseEnd_7202986 : Nat := 3698593965606260517849077

theorem tailTrace_7202986 : CollatzResearch.WordTrace tailWord_7202986 prefixEnd_7202986 3698593965606260517849077 := by
  unfold tailWord_7202986
  simp only [CollatzResearch.WordTrace]
  refine ⟨65678620570704842228727203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175142988188546245943272541 65678620570704842228727203)
  ·
    refine ⟨98517930856057263343090805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65678620570704842228727203 98517930856057263343090805)
    ·
      refine ⟨9236056017755368438414763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98517930856057263343090805 9236056017755368438414763)
      ·
        refine ⟨13854084026633052657622145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9236056017755368438414763 13854084026633052657622145)
        ·
          refine ⟨10390563019974789493216609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13854084026633052657622145 10390563019974789493216609)
          ·
            refine ⟨7792922264981092119912457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10390563019974789493216609 7792922264981092119912457)
            ·
              refine ⟨5844691698735819089934343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7792922264981092119912457 5844691698735819089934343)
              ·
                refine ⟨8767037548103728634901515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844691698735819089934343 8767037548103728634901515)
                ·
                  refine ⟨13150556322155592952352273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8767037548103728634901515 13150556322155592952352273)
                  ·
                    refine ⟨9862917241616694714264205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13150556322155592952352273 9862917241616694714264205)
                    ·
                      refine ⟨3698593965606260517849077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9862917241616694714264205 3698593965606260517849077)
                      ·
                        rfl

theorem cell23_7202986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7202986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202986 prefixEnd_7202986 := by exact prefixLift 7202986
  have htrace : WordTrace (prefixWord ++ tailWord_7202986) baseStart_7202986 baseEnd_7202986 := by
    simpa [prefixWord, tailWord_7202986, baseEnd_7202986] using wordTrace_append hprefix tailTrace_7202986
  have hstable : (prefixWord ++ tailWord_7202986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202986).length < 2 ^ (prefixWord ++ tailWord_7202986).sum := by decide
  have hdescent : baseEnd_7202986 < baseStart_7202986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202988 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_7202988 : Nat := 118140960795 + 7202988 * 2 ^ 59
def prefixEnd_7202988 : Nat := 4983230072969 + 3 ^ 40 * 7202988 * 2
def baseEnd_7202988 : Nat := 3698594992567569510024067

theorem tailTrace_7202988 : CollatzResearch.WordTrace tailWord_7202988 prefixEnd_7202988 3698594992567569510024067 := by
  unfold tailWord_7202988
  simp only [CollatzResearch.WordTrace]
  refine ⟨131357277614406061628240809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175143036819208082170987745 131357277614406061628240809)
  ·
    refine ⟨98517958210804546221180607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131357277614406061628240809 98517958210804546221180607)
    ·
      refine ⟨147776937316206819331770911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98517958210804546221180607 147776937316206819331770911)
      ·
        refine ⟨221665405974310228997656367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147776937316206819331770911 221665405974310228997656367)
        ·
          refine ⟨332498108961465343496484551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221665405974310228997656367 332498108961465343496484551)
          ·
            refine ⟨498747163442198015244726827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332498108961465343496484551 498747163442198015244726827)
            ·
              refine ⟨748120745163297022867090241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498747163442198015244726827 748120745163297022867090241)
              ·
                refine ⟨561090558872472767150317681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748120745163297022867090241 561090558872472767150317681)
                ·
                  refine ⟨420817919154354575362738261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561090558872472767150317681 420817919154354575362738261)
                  ·
                    refine ⟨4931459990090092680032089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 420817919154354575362738261 4931459990090092680032089)
                    ·
                      refine ⟨3698594992567569510024067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931459990090092680032089 3698594992567569510024067)
                      ·
                        rfl

theorem cell23_7202988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_7202988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202988 prefixEnd_7202988 := by exact prefixLift 7202988
  have htrace : WordTrace (prefixWord ++ tailWord_7202988) baseStart_7202988 baseEnd_7202988 := by
    simpa [prefixWord, tailWord_7202988, baseEnd_7202988] using wordTrace_append hprefix tailTrace_7202988
  have hstable : (prefixWord ++ tailWord_7202988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202988).length < 2 ^ (prefixWord ++ tailWord_7202988).sum := by decide
  have hdescent : baseEnd_7202988 < baseStart_7202988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7202991 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_7202991 : Nat := 118140960795 + 7202991 * 2 ^ 59
def prefixEnd_7202991 : Nat := 4983230072969 + 3 ^ 40 * 7202991 * 2
def baseEnd_7202991 : Nat := 3698596533009532998286553

theorem tailTrace_7202991 : CollatzResearch.WordTrace tailWord_7202991 prefixEnd_7202991 3698596533009532998286553 := by
  unfold tailWord_7202991
  simp only [CollatzResearch.WordTrace]
  refine ⟨262714664647801254768840827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175143109765200836512560551 262714664647801254768840827)
  ·
    refine ⟨394071996971701882153261241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262714664647801254768840827 394071996971701882153261241)
    ·
      refine ⟨295553997728776411614945931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394071996971701882153261241 295553997728776411614945931)
      ·
        refine ⟨443330996593164617422418897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295553997728776411614945931 443330996593164617422418897)
        ·
          refine ⟨332498247444873463066814173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443330996593164617422418897 332498247444873463066814173)
          ·
            refine ⟨124686842791827548650055315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332498247444873463066814173 124686842791827548650055315)
            ·
              refine ⟨187030264187741322975082973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124686842791827548650055315 187030264187741322975082973)
              ·
                refine ⟨70136349070402996115656115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187030264187741322975082973 70136349070402996115656115)
                ·
                  refine ⟨105204523605604494173484173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70136349070402996115656115 105204523605604494173484173)
                  ·
                    refine ⟨39451696352101685315056565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105204523605604494173484173 39451696352101685315056565)
                    ·
                      refine ⟨3698596533009532998286553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39451696352101685315056565 3698596533009532998286553)
                      ·
                        rfl

theorem cell23_7202991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_7202991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7202991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7202991 prefixEnd_7202991 := by exact prefixLift 7202991
  have htrace : WordTrace (prefixWord ++ tailWord_7202991) baseStart_7202991 baseEnd_7202991 := by
    simpa [prefixWord, tailWord_7202991, baseEnd_7202991] using wordTrace_append hprefix tailTrace_7202991
  have hstable : (prefixWord ++ tailWord_7202991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7202991).length < 2 ^ (prefixWord ++ tailWord_7202991).sum := by decide
  have hdescent : baseEnd_7202991 < baseStart_7202991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7202991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203018 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_7203018 : Nat := 118140960795 + 7203018 * 2 ^ 59
def prefixEnd_7203018 : Nat := 4983230072969 + 3 ^ 40 * 7203018 * 2
def baseEnd_7203018 : Nat := 3698610396987204392648929

theorem tailTrace_7203018 : CollatzResearch.WordTrace tailWord_7203018 prefixEnd_7203018 3698610396987204392648929 := by
  unfold tailWord_7203018
  simp only [CollatzResearch.WordTrace]
  refine ⟨65678912354675859595018427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175143766279135625586715805 65678912354675859595018427)
  ·
    refine ⟨98518368532013789392527641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65678912354675859595018427 98518368532013789392527641)
    ·
      refine ⟨73888776399010342044395731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98518368532013789392527641 73888776399010342044395731)
      ·
        refine ⟨110833164598515513066593597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73888776399010342044395731 110833164598515513066593597)
        ·
          refine ⟨41562436724443317399972599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110833164598515513066593597 41562436724443317399972599)
          ·
            refine ⟨62343655086664976099958899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41562436724443317399972599 62343655086664976099958899)
            ·
              refine ⟨93515482629997464149938349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62343655086664976099958899 93515482629997464149938349)
              ·
                refine ⟨35068305986249049056226881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93515482629997464149938349 35068305986249049056226881)
                ·
                  refine ⟨26301229489686786792170161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35068305986249049056226881 26301229489686786792170161)
                  ·
                    refine ⟨19725922117265090094127621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26301229489686786792170161 19725922117265090094127621)
                    ·
                      refine ⟨3698610396987204392648929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19725922117265090094127621 3698610396987204392648929)
                      ·
                        rfl

theorem cell23_7203018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_7203018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203018 prefixEnd_7203018 := by exact prefixLift 7203018
  have htrace : WordTrace (prefixWord ++ tailWord_7203018) baseStart_7203018 baseEnd_7203018 := by
    simpa [prefixWord, tailWord_7203018, baseEnd_7203018] using wordTrace_append hprefix tailTrace_7203018
  have hstable : (prefixWord ++ tailWord_7203018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203018).length < 2 ^ (prefixWord ++ tailWord_7203018).sum := by decide
  have hdescent : baseEnd_7203018 < baseStart_7203018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203022 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_7203022 : Nat := 118140960795 + 7203022 * 2 ^ 59
def prefixEnd_7203022 : Nat := 4983230072969 + 3 ^ 40 * 7203022 * 2
def baseEnd_7203022 : Nat := 3698612450909822376998911

theorem tailTrace_7203022 : CollatzResearch.WordTrace tailWord_7203022 prefixEnd_7203022 3698612450909822376998911 := by
  unfold tailWord_7203022
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839474413836118382902415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175143863540459298042146213 32839474413836118382902415)
  ·
    refine ⟨49259211620754177574353623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32839474413836118382902415 49259211620754177574353623)
    ·
      refine ⟨73888817431131266361530435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49259211620754177574353623 73888817431131266361530435)
      ·
        refine ⟨110833226146696899542295653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73888817431131266361530435 110833226146696899542295653)
        ·
          refine ⟨20781229902505668664180435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110833226146696899542295653 20781229902505668664180435)
          ·
            refine ⟨31171844853758502996270653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20781229902505668664180435 31171844853758502996270653)
            ·
              refine ⟨11689441820159438623601495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31171844853758502996270653 11689441820159438623601495)
              ·
                refine ⟨17534162730239157935402243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11689441820159438623601495 17534162730239157935402243)
                ·
                  refine ⟨26301244095358736903103365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17534162730239157935402243 26301244095358736903103365)
                  ·
                    refine ⟨4931483267879763169331881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26301244095358736903103365 4931483267879763169331881)
                    ·
                      refine ⟨3698612450909822376998911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931483267879763169331881 3698612450909822376998911)
                      ·
                        rfl

theorem cell23_7203022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_7203022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203022 prefixEnd_7203022 := by exact prefixLift 7203022
  have htrace : WordTrace (prefixWord ++ tailWord_7203022) baseStart_7203022 baseEnd_7203022 := by
    simpa [prefixWord, tailWord_7203022, baseEnd_7203022] using wordTrace_append hprefix tailTrace_7203022
  have hstable : (prefixWord ++ tailWord_7203022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203022).length < 2 ^ (prefixWord ++ tailWord_7203022).sum := by decide
  have hdescent : baseEnd_7203022 < baseStart_7203022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203068 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_7203068 : Nat := 118140960795 + 7203068 * 2 ^ 59
def prefixEnd_7203068 : Nat := 4983230072969 + 3 ^ 40 * 7203068 * 2
def baseEnd_7203068 : Nat := 3698636071019929197023699

theorem tailTrace_7203068 : CollatzResearch.WordTrace tailWord_7203068 prefixEnd_7203068 3698636071019929197023699 := by
  unfold tailWord_7203068
  simp only [CollatzResearch.WordTrace]
  refine ⟨131358736534261148459696929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175144982045681531279595905 131358736534261148459696929)
  ·
    refine ⟨98519052400695861344772697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131358736534261148459696929 98519052400695861344772697)
    ·
      refine ⟨73889289300521896008579523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98519052400695861344772697 73889289300521896008579523)
      ·
        refine ⟨110833933950782844012869285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73889289300521896008579523 110833933950782844012869285)
        ·
          refine ⟨20781362615771783252412991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110833933950782844012869285 20781362615771783252412991)
          ·
            refine ⟨31172043923657674878619487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20781362615771783252412991 31172043923657674878619487)
            ·
              refine ⟨46758065885486512317929231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31172043923657674878619487 46758065885486512317929231)
              ·
                refine ⟨70137098828229768476893847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46758065885486512317929231 70137098828229768476893847)
                ·
                  refine ⟨105205648242344652715340771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70137098828229768476893847 105205648242344652715340771)
                  ·
                    refine ⟨157808472363516979073011157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105205648242344652715340771 157808472363516979073011157)
                    ·
                      refine ⟨3698636071019929197023699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157808472363516979073011157 3698636071019929197023699)
                      ·
                        rfl

theorem cell23_7203068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_7203068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203068 prefixEnd_7203068 := by exact prefixLift 7203068
  have htrace : WordTrace (prefixWord ++ tailWord_7203068) baseStart_7203068 baseEnd_7203068 := by
    simpa [prefixWord, tailWord_7203068, baseEnd_7203068] using wordTrace_append hprefix tailTrace_7203068
  have hstable : (prefixWord ++ tailWord_7203068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203068).length < 2 ^ (prefixWord ++ tailWord_7203068).sum := by decide
  have hdescent : baseEnd_7203068 < baseStart_7203068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203095 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_7203095 : Nat := 118140960795 + 7203095 * 2 ^ 59
def prefixEnd_7203095 : Nat := 4983230072969 + 3 ^ 40 * 7203095 * 2
def baseEnd_7203095 : Nat := 3698649934997600591386075

theorem tailTrace_7203095 : CollatzResearch.WordTrace tailWord_7203095 prefixEnd_7203095 3698649934997600591386075 := by
  unfold tailWord_7203095
  simp only [CollatzResearch.WordTrace]
  refine ⟨262718457839424480530626739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175145638559616320353751159 262718457839424480530626739)
  ·
    refine ⟨394077686759136720795940109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262718457839424480530626739 394077686759136720795940109)
    ·
      refine ⟨147779132534676270298477541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394077686759136720795940109 147779132534676270298477541)
      ·
        refine ⟨27708587350251800680964539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147779132534676270298477541 27708587350251800680964539)
        ·
          refine ⟨41562881025377701021446809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27708587350251800680964539 41562881025377701021446809)
          ·
            refine ⟨31172160769033275766085107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41562881025377701021446809 31172160769033275766085107)
            ·
              refine ⟨46758241153549913649127661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31172160769033275766085107 46758241153549913649127661)
              ·
                refine ⟨17534340432581217618422873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46758241153549913649127661 17534340432581217618422873)
                ·
                  refine ⟨13150755324435913213817155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17534340432581217618422873 13150755324435913213817155)
                  ·
                    refine ⟨19726132986653869820725733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13150755324435913213817155 19726132986653869820725733)
                    ·
                      refine ⟨3698649934997600591386075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19726132986653869820725733 3698649934997600591386075)
                      ·
                        rfl

theorem cell23_7203095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_7203095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203095 prefixEnd_7203095 := by exact prefixLift 7203095
  have htrace : WordTrace (prefixWord ++ tailWord_7203095) baseStart_7203095 baseEnd_7203095 := by
    simpa [prefixWord, tailWord_7203095, baseEnd_7203095] using wordTrace_append hprefix tailTrace_7203095
  have hstable : (prefixWord ++ tailWord_7203095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203095).length < 2 ^ (prefixWord ++ tailWord_7203095).sum := by decide
  have hdescent : baseEnd_7203095 < baseStart_7203095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203102 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7203102 : Nat := 118140960795 + 7203102 * 2 ^ 59
def prefixEnd_7203102 : Nat := 4983230072969 + 3 ^ 40 * 7203102 * 2
def baseEnd_7203102 : Nat := 3698653529362182063998543

theorem tailTrace_7203102 : CollatzResearch.WordTrace tailWord_7203102 prefixEnd_7203102 3698653529362182063998543 := by
  unfold tailWord_7203102
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839839143799890090766445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175145808766932747150754373 32839839143799890090766445)
  ·
    refine ⟨12314939678924958784037417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32839839143799890090766445 12314939678924958784037417)
    ·
      refine ⟨9236204759193719088028063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12314939678924958784037417 9236204759193719088028063)
      ·
        refine ⟨13854307138790578632042095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9236204759193719088028063 13854307138790578632042095)
        ·
          refine ⟨20781460708185867948063143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13854307138790578632042095 20781460708185867948063143)
          ·
            refine ⟨31172191062278801922094715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20781460708185867948063143 31172191062278801922094715)
            ·
              refine ⟨46758286593418202883142073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31172191062278801922094715 46758286593418202883142073)
              ·
                refine ⟨35068714945063652162356555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46758286593418202883142073 35068714945063652162356555)
                ·
                  refine ⟨52603072417595478243534833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35068714945063652162356555 52603072417595478243534833)
                  ·
                    refine ⟨39452304313196608682651125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52603072417595478243534833 39452304313196608682651125)
                    ·
                      refine ⟨3698653529362182063998543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39452304313196608682651125 3698653529362182063998543)
                      ·
                        rfl

theorem cell23_7203102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7203102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203102 prefixEnd_7203102 := by exact prefixLift 7203102
  have htrace : WordTrace (prefixWord ++ tailWord_7203102) baseStart_7203102 baseEnd_7203102 := by
    simpa [prefixWord, tailWord_7203102, baseEnd_7203102] using wordTrace_append hprefix tailTrace_7203102
  have hstable : (prefixWord ++ tailWord_7203102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203102).length < 2 ^ (prefixWord ++ tailWord_7203102).sum := by decide
  have hdescent : baseEnd_7203102 < baseStart_7203102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203172 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_7203172 : Nat := 118140960795 + 7203172 * 2 ^ 59
def prefixEnd_7203172 : Nat := 4983230072969 + 3 ^ 40 * 7203172 * 2
def baseEnd_7203172 : Nat := 3698689473007996790123221

theorem tailTrace_7203172 : CollatzResearch.WordTrace tailWord_7203172 prefixEnd_7203172 3698689473007996790123221 := by
  unfold tailWord_7203172
  simp only [CollatzResearch.WordTrace]
  refine ⟨131360633130072761340589885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175147510840097015120786513 131360633130072761340589885)
  ·
    refine ⟨49260237423777285502721207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131360633130072761340589885 49260237423777285502721207)
    ·
      refine ⟨73890356135665928254081811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49260237423777285502721207 73890356135665928254081811)
      ·
        refine ⟨110835534203498892381122717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73890356135665928254081811 110835534203498892381122717)
        ·
          refine ⟨41563325326312084642921019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110835534203498892381122717 41563325326312084642921019)
          ·
            refine ⟨62344987989468126964381529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41563325326312084642921019 62344987989468126964381529)
            ·
              refine ⟨46758740992101095223286147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62344987989468126964381529 46758740992101095223286147)
              ·
                refine ⟨70138111488151642834929221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46758740992101095223286147 70138111488151642834929221)
                ·
                  refine ⟨13150895904028433031549229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70138111488151642834929221 13150895904028433031549229)
                  ·
                    refine ⟨4931585964010662386830961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13150895904028433031549229 4931585964010662386830961)
                    ·
                      refine ⟨3698689473007996790123221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931585964010662386830961 3698689473007996790123221)
                      ·
                        rfl

theorem cell23_7203172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_7203172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203172 prefixEnd_7203172 := by exact prefixLift 7203172
  have htrace : WordTrace (prefixWord ++ tailWord_7203172) baseStart_7203172 baseEnd_7203172 := by
    simpa [prefixWord, tailWord_7203172, baseEnd_7203172] using wordTrace_append hprefix tailTrace_7203172
  have hstable : (prefixWord ++ tailWord_7203172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203172).length < 2 ^ (prefixWord ++ tailWord_7203172).sum := by decide
  have hdescent : baseEnd_7203172 < baseStart_7203172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203195 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 1, 6]
def baseStart_7203195 : Nat := 118140960795 + 7203195 * 2 ^ 59
def prefixEnd_7203195 : Nat := 4983230072969 + 3 ^ 40 * 7203195 * 2
def baseEnd_7203195 : Nat := 1232900427687683400045205

theorem tailTrace_7203195 : CollatzResearch.WordTrace tailWord_7203195 prefixEnd_7203195 1232900427687683400045205 := by
  unfold tailWord_7203195
  simp only [CollatzResearch.WordTrace]
  refine ⟨262722105139062197609267039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175148070092708131739511359 262722105139062197609267039)
  ·
    refine ⟨394083157708593296413900559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262722105139062197609267039 394083157708593296413900559)
    ·
      refine ⟨591124736562889944620850839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394083157708593296413900559 591124736562889944620850839)
      ·
        refine ⟨886687104844334916931276259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591124736562889944620850839 886687104844334916931276259)
        ·
          refine ⟨1330030657266502375396914389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886687104844334916931276259 1330030657266502375396914389)
          ·
            refine ⟨31172593529683649423365181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1330030657266502375396914389 31172593529683649423365181)
            ·
              refine ⟨11689722573631368533761943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31172593529683649423365181 11689722573631368533761943)
              ·
                refine ⟨17534583860447052800642915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11689722573631368533761943 17534583860447052800642915)
                ·
                  refine ⟨26301875790670579200964373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17534583860447052800642915 26301875790670579200964373)
                  ·
                    refine ⟨1232900427687683400045205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26301875790670579200964373 1232900427687683400045205)
                    ·
                      rfl

theorem cell23_7203195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 6].length) (baseStart_7203195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203195 prefixEnd_7203195 := by exact prefixLift 7203195
  have htrace : WordTrace (prefixWord ++ tailWord_7203195) baseStart_7203195 baseEnd_7203195 := by
    simpa [prefixWord, tailWord_7203195, baseEnd_7203195] using wordTrace_append hprefix tailTrace_7203195
  have hstable : (prefixWord ++ tailWord_7203195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203195).length < 2 ^ (prefixWord ++ tailWord_7203195).sum := by decide
  have hdescent : baseEnd_7203195 < baseStart_7203195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203230 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7203230 : Nat := 118140960795 + 7203230 * 2 ^ 59
def prefixEnd_7203230 : Nat := 4983230072969 + 3 ^ 40 * 7203230 * 2
def baseEnd_7203230 : Nat := 3698719254885957563197955

theorem tailTrace_7203230 : CollatzResearch.WordTrace tailWord_7203230 prefixEnd_7203230 3698719254885957563197955 := by
  unfold tailWord_7203230
  simp only [CollatzResearch.WordTrace]
  refine ⟨32840422711741924823348893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175148921129290265724527429 32840422711741924823348893)
  ·
    refine ⟨12315158516903221808755835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32840422711741924823348893 12315158516903221808755835)
    ·
      refine ⟨18472737775354832713133753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315158516903221808755835 18472737775354832713133753)
      ·
        refine ⟨13854553331516124534850315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18472737775354832713133753 13854553331516124534850315)
        ·
          refine ⟨20781829997274186802275473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13854553331516124534850315 20781829997274186802275473)
          ·
            refine ⟨15586372497955640101706605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20781829997274186802275473 15586372497955640101706605)
            ·
              refine ⟨5844889686733365038139977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15586372497955640101706605 5844889686733365038139977)
              ·
                refine ⟨4383667265050023778604983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844889686733365038139977 4383667265050023778604983)
                ·
                  refine ⟨6575500897575035667907475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383667265050023778604983 6575500897575035667907475)
                  ·
                    refine ⟨9863251346362553501861213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6575500897575035667907475 9863251346362553501861213)
                    ·
                      refine ⟨3698719254885957563197955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9863251346362553501861213 3698719254885957563197955)
                      ·
                        rfl

theorem cell23_7203230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7203230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203230 prefixEnd_7203230 := by exact prefixLift 7203230
  have htrace : WordTrace (prefixWord ++ tailWord_7203230) baseStart_7203230 baseEnd_7203230 := by
    simpa [prefixWord, tailWord_7203230, baseEnd_7203230] using wordTrace_append hprefix tailTrace_7203230
  have hstable : (prefixWord ++ tailWord_7203230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203230).length < 2 ^ (prefixWord ++ tailWord_7203230).sum := by decide
  have hdescent : baseEnd_7203230 < baseStart_7203230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203236 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_7203236 : Nat := 118140960795 + 7203236 * 2 ^ 59
def prefixEnd_7203236 : Nat := 4983230072969 + 3 ^ 40 * 7203236 * 2
def baseEnd_7203236 : Nat := 3698722335769884539722927

theorem tailTrace_7203236 : CollatzResearch.WordTrace tailWord_7203236 prefixEnd_7203236 3698722335769884539722927 := by
  unfold tailWord_7203236
  simp only [CollatzResearch.WordTrace]
  refine ⟨131361800265956830805754781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175149067021275774407673041 131361800265956830805754781)
  ·
    refine ⟨49260675099733811552158043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131361800265956830805754781 49260675099733811552158043)
    ·
      refine ⟨73891012649600717328237065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49260675099733811552158043 73891012649600717328237065)
      ·
        refine ⟨55418259487200537996177799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73891012649600717328237065 55418259487200537996177799)
        ·
          refine ⟨83127389230800806994266699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55418259487200537996177799 83127389230800806994266699)
          ·
            refine ⟨124691083846201210491400049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83127389230800806994266699 124691083846201210491400049)
            ·
              refine ⟨93518312884650907868550037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124691083846201210491400049 93518312884650907868550037)
              ·
                refine ⟨4383670916468011306338283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93518312884650907868550037 4383670916468011306338283)
                ·
                  refine ⟨6575506374702016959507425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383670916468011306338283 6575506374702016959507425)
                  ·
                    refine ⟨4931629781026512719630569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575506374702016959507425 4931629781026512719630569)
                    ·
                      refine ⟨3698722335769884539722927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931629781026512719630569 3698722335769884539722927)
                      ·
                        rfl

theorem cell23_7203236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_7203236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203236 prefixEnd_7203236 := by exact prefixLift 7203236
  have htrace : WordTrace (prefixWord ++ tailWord_7203236) baseStart_7203236 baseEnd_7203236 := by
    simpa [prefixWord, tailWord_7203236, baseEnd_7203236] using wordTrace_append hprefix tailTrace_7203236
  have hstable : (prefixWord ++ tailWord_7203236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203236).length < 2 ^ (prefixWord ++ tailWord_7203236).sum := by decide
  have hdescent : baseEnd_7203236 < baseStart_7203236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203315 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 7]
def baseStart_7203315 : Nat := 118140960795 + 7203315 * 2 ^ 59
def prefixEnd_7203315 : Nat := 4983230072969 + 3 ^ 40 * 7203315 * 2
def baseEnd_7203315 : Nat := 410973655637954414515007

theorem tailTrace_7203315 : CollatzResearch.WordTrace tailWord_7203315 prefixEnd_7203315 410973655637954414515007 := by
  unfold tailWord_7203315
  simp only [CollatzResearch.WordTrace]
  refine ⟨262726481898627458103635399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175150987932418305402423599 262726481898627458103635399)
  ·
    refine ⟨394089722847941187155453099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262726481898627458103635399 394089722847941187155453099)
    ·
      refine ⟨591134584271911780733179649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394089722847941187155453099 591134584271911780733179649)
      ·
        refine ⟨443350938203933835549884737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591134584271911780733179649 443350938203933835549884737)
        ·
          refine ⟨332513203652950376662413553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443350938203933835549884737 332513203652950376662413553)
          ·
            refine ⟨249384902739712782496810165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332513203652950376662413553 249384902739712782496810165)
            ·
              refine ⟨23379834631848073359075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249384902739712782496810165 23379834631848073359075953)
              ·
                refine ⟨17534875973886055019306965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23379834631848073359075953 17534875973886055019306965)
                ·
                  refine ⟨410973655637954414515007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17534875973886055019306965 410973655637954414515007)
                  ·
                    rfl

theorem cell23_7203315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 7].length) (baseStart_7203315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203315 prefixEnd_7203315 := by exact prefixLift 7203315
  have htrace : WordTrace (prefixWord ++ tailWord_7203315) baseStart_7203315 baseEnd_7203315 := by
    simpa [prefixWord, tailWord_7203315, baseEnd_7203315] using wordTrace_append hprefix tailTrace_7203315
  have hstable : (prefixWord ++ tailWord_7203315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203315).length < 2 ^ (prefixWord ++ tailWord_7203315).sum := by decide
  have hdescent : baseEnd_7203315 < baseStart_7203315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203360 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7203360 : Nat := 118140960795 + 7203360 * 2 ^ 59
def prefixEnd_7203360 : Nat := 4983230072969 + 3 ^ 40 * 7203360 * 2
def baseEnd_7203360 : Nat := 3698786007371042054572357

theorem tailTrace_7203360 : CollatzResearch.WordTrace tailWord_7203360 prefixEnd_7203360 3698786007371042054572357 := by
  unfold tailWord_7203360
  simp only [CollatzResearch.WordTrace]
  refine ⟨131364061591732215394511767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175152082122309620526015689 131364061591732215394511767)
  ·
    refine ⟨197046092387598323091767651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131364061591732215394511767 197046092387598323091767651)
    ·
      refine ⟨295569138581397484637651477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197046092387598323091767651 295569138581397484637651477)
      ·
        refine ⟨13854803371003007092389913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 295569138581397484637651477 13854803371003007092389913)
        ·
          refine ⟨10391102528252255319292435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13854803371003007092389913 10391102528252255319292435)
          ·
            refine ⟨15586653792378382978938653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10391102528252255319292435 15586653792378382978938653)
            ·
              refine ⟨5844995172141893617101995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15586653792378382978938653 5844995172141893617101995)
              ·
                refine ⟨8767492758212840425652993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5844995172141893617101995 8767492758212840425652993)
                ·
                  refine ⟨6575619568659630319239745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8767492758212840425652993 6575619568659630319239745)
                  ·
                    refine ⟨4931714676494722739429809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575619568659630319239745 4931714676494722739429809)
                    ·
                      refine ⟨3698786007371042054572357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931714676494722739429809 3698786007371042054572357)
                      ·
                        rfl

theorem cell23_7203360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7203360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203360 prefixEnd_7203360 := by exact prefixLift 7203360
  have htrace : WordTrace (prefixWord ++ tailWord_7203360) baseStart_7203360 baseEnd_7203360 := by
    simpa [prefixWord, tailWord_7203360, baseEnd_7203360] using wordTrace_append hprefix tailTrace_7203360
  have hstable : (prefixWord ++ tailWord_7203360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203360).length < 2 ^ (prefixWord ++ tailWord_7203360).sum := by decide
  have hdescent : baseEnd_7203360 < baseStart_7203360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203392 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_7203392 : Nat := 118140960795 + 7203392 * 2 ^ 59
def prefixEnd_7203392 : Nat := 4983230072969 + 3 ^ 40 * 7203392 * 2
def baseEnd_7203392 : Nat := 1232934146250661976457403

theorem tailTrace_7203392 : CollatzResearch.WordTrace tailWord_7203392 prefixEnd_7203392 1232934146250661976457403 := by
  unfold tailWord_7203392
  simp only [CollatzResearch.WordTrace]
  refine ⟨131364645159674250127094215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175152860212899000169458953 131364645159674250127094215)
  ·
    refine ⟨197046967739511375190641323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131364645159674250127094215 197046967739511375190641323)
    ·
      refine ⟨295570451609267062785961985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197046967739511375190641323 295570451609267062785961985)
      ·
        refine ⟨221677838706950297089471489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295570451609267062785961985 221677838706950297089471489)
        ·
          refine ⟨166258379030212722817103617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221677838706950297089471489 166258379030212722817103617)
          ·
            refine ⟨124693784272659542112827713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166258379030212722817103617 124693784272659542112827713)
            ·
              refine ⟨93520338204494656584620785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124693784272659542112827713 93520338204494656584620785)
              ·
                refine ⟨70140253653370992438465589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93520338204494656584620785 70140253653370992438465589)
                ·
                  refine ⟨6575648780003530541106149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70140253653370992438465589 6575648780003530541106149)
                  ·
                    refine ⟨1232934146250661976457403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575648780003530541106149 1232934146250661976457403)
                    ·
                      rfl

theorem cell23_7203392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_7203392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203392 prefixEnd_7203392 := by exact prefixLift 7203392
  have htrace : WordTrace (prefixWord ++ tailWord_7203392) baseStart_7203392 baseEnd_7203392 := by
    simpa [prefixWord, tailWord_7203392, baseEnd_7203392] using wordTrace_append hprefix tailTrace_7203392
  have hstable : (prefixWord ++ tailWord_7203392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203392).length < 2 ^ (prefixWord ++ tailWord_7203392).sum := by decide
  have hdescent : baseEnd_7203392 < baseStart_7203392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203395 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_7203395 : Nat := 118140960795 + 7203395 * 2 ^ 59
def prefixEnd_7203395 : Nat := 4983230072969 + 3 ^ 40 * 7203395 * 2
def baseEnd_7203395 : Nat := 3698803979193949417634695

theorem tailTrace_7203395 : CollatzResearch.WordTrace tailWord_7203395 prefixEnd_7203395 3698803979193949417634695 := by
  unfold tailWord_7203395
  simp only [CollatzResearch.WordTrace]
  refine ⟨262729399738337631766547639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175152933158891754511031759 262729399738337631766547639)
  ·
    refine ⟨394094099607506447649821459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262729399738337631766547639 394094099607506447649821459)
    ·
      refine ⟨591141149411259671474732189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394094099607506447649821459 591141149411259671474732189)
      ·
        refine ⟨221677931029222376803024571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591141149411259671474732189 221677931029222376803024571)
        ·
          refine ⟨332516896543833565204536857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221677931029222376803024571 332516896543833565204536857)
          ·
            refine ⟨249387672407875173903402643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332516896543833565204536857 249387672407875173903402643)
            ·
              refine ⟨374081508611812760855103965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249387672407875173903402643 374081508611812760855103965)
              ·
                refine ⟨140280565729429785320663987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374081508611812760855103965 140280565729429785320663987)
                ·
                  refine ⟨210420848594144677980995981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140280565729429785320663987 210420848594144677980995981)
                  ·
                    refine ⟨78907818222804254242873493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210420848594144677980995981 78907818222804254242873493)
                    ·
                      refine ⟨3698803979193949417634695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78907818222804254242873493 3698803979193949417634695)
                      ·
                        rfl

theorem cell23_7203395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_7203395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203395 prefixEnd_7203395 := by exact prefixLift 7203395
  have htrace : WordTrace (prefixWord ++ tailWord_7203395) baseStart_7203395 baseEnd_7203395 := by
    simpa [prefixWord, tailWord_7203395, baseEnd_7203395] using wordTrace_append hprefix tailTrace_7203395
  have hstable : (prefixWord ++ tailWord_7203395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203395).length < 2 ^ (prefixWord ++ tailWord_7203395).sum := by decide
  have hdescent : baseEnd_7203395 < baseStart_7203395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203399 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_7203399 : Nat := 118140960795 + 7203399 * 2 ^ 59
def prefixEnd_7203399 : Nat := 4983230072969 + 3 ^ 40 * 7203399 * 2
def baseEnd_7203399 : Nat := 3698806033116567401984677

theorem tailTrace_7203399 : CollatzResearch.WordTrace tailWord_7203399 prefixEnd_7203399 3698806033116567401984677 := by
  unfold tailWord_7203399
  simp only [CollatzResearch.WordTrace]
  refine ⟨262729545630323140449693251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175153030420215426966462167 262729545630323140449693251)
  ·
    refine ⟨394094318445484710674539877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262729545630323140449693251 394094318445484710674539877)
    ·
      refine ⟨73892684708528383251476227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394094318445484710674539877 73892684708528383251476227)
      ·
        refine ⟨110839027062792574877214341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73892684708528383251476227 110839027062792574877214341)
        ·
          refine ⟨20782317574273607789477689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110839027062792574877214341 20782317574273607789477689)
          ·
            refine ⟨15586738180705205842108267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20782317574273607789477689 15586738180705205842108267)
            ·
              refine ⟨23380107271057808763162401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15586738180705205842108267 23380107271057808763162401)
              ·
                refine ⟨17535080453293356572371801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23380107271057808763162401 17535080453293356572371801)
                ·
                  refine ⟨13151310339970017429278851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17535080453293356572371801 13151310339970017429278851)
                  ·
                    refine ⟨19726965509955026143918277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13151310339970017429278851 19726965509955026143918277)
                    ·
                      refine ⟨3698806033116567401984677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19726965509955026143918277 3698806033116567401984677)
                      ·
                        rfl

theorem cell23_7203399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_7203399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203399 prefixEnd_7203399 := by exact prefixLift 7203399
  have htrace : WordTrace (prefixWord ++ tailWord_7203399) baseStart_7203399 baseEnd_7203399 := by
    simpa [prefixWord, tailWord_7203399, baseEnd_7203399] using wordTrace_append hprefix tailTrace_7203399
  have hstable : (prefixWord ++ tailWord_7203399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203399).length < 2 ^ (prefixWord ++ tailWord_7203399).sum := by decide
  have hdescent : baseEnd_7203399 < baseStart_7203399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203409 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_7203409 : Nat := 118140960795 + 7203409 * 2 ^ 59
def prefixEnd_7203409 : Nat := 4983230072969 + 3 ^ 40 * 7203409 * 2
def baseEnd_7203409 : Nat := 1232937055974370787619877

theorem tailTrace_7203409 : CollatzResearch.WordTrace tailWord_7203409 prefixEnd_7203409 1232937055974370787619877 := by
  unfold tailWord_7203409
  simp only [CollatzResearch.WordTrace]
  refine ⟨262729910360286912157557281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175153273573524608105038187 262729910360286912157557281)
  ·
    refine ⟨197047432770215184118167961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262729910360286912157557281 197047432770215184118167961)
    ·
      refine ⟨147785574577661388088625971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197047432770215184118167961 147785574577661388088625971)
      ·
        refine ⟨221678361866492082132938957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147785574577661388088625971 221678361866492082132938957)
        ·
          refine ⟨83129385699934530799852109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221678361866492082132938957 83129385699934530799852109)
          ·
            refine ⟨31173519637475449049944541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83129385699934530799852109 31173519637475449049944541)
            ·
              refine ⟨11690069864053293393729203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31173519637475449049944541 11690069864053293393729203)
              ·
                refine ⟨17535104796079940090593805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11690069864053293393729203 17535104796079940090593805)
                ·
                  refine ⟨6575664298529977533972677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17535104796079940090593805 6575664298529977533972677)
                  ·
                    refine ⟨1232937055974370787619877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575664298529977533972677 1232937055974370787619877)
                    ·
                      rfl

theorem cell23_7203409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_7203409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203409 prefixEnd_7203409 := by exact prefixLift 7203409
  have htrace : WordTrace (prefixWord ++ tailWord_7203409) baseStart_7203409 baseEnd_7203409 := by
    simpa [prefixWord, tailWord_7203409, baseEnd_7203409] using wordTrace_append hprefix tailTrace_7203409
  have hstable : (prefixWord ++ tailWord_7203409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203409).length < 2 ^ (prefixWord ++ tailWord_7203409).sum := by decide
  have hdescent : baseEnd_7203409 < baseStart_7203409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203460 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_7203460 : Nat := 118140960795 + 7203460 * 2 ^ 59
def prefixEnd_7203460 : Nat := 4983230072969 + 3 ^ 40 * 7203460 * 2
def baseEnd_7203460 : Nat := 1232945785145497221107299

theorem tailTrace_7203460 : CollatzResearch.WordTrace tailWord_7203460 prefixEnd_7203460 1232945785145497221107299 := by
  unfold tailWord_7203460
  simp only [CollatzResearch.WordTrace]
  refine ⟨131365885241551073933831917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175154513655401431911775889 131365885241551073933831917)
  ·
    refine ⟨49262206965581652725186969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131365885241551073933831917 49262206965581652725186969)
    ·
      refine ⟨36946655224186239543890227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49262206965581652725186969 36946655224186239543890227)
      ·
        refine ⟨55419982836279359315835341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36946655224186239543890227 55419982836279359315835341)
        ·
          refine ⟨20782493563604759743438253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55419982836279359315835341 20782493563604759743438253)
          ·
            refine ⟨7793435086351784903789345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20782493563604759743438253 7793435086351784903789345)
            ·
              refine ⟨5845076314763838677842009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7793435086351784903789345 5845076314763838677842009)
              ·
                refine ⟨4383807236072879008381507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845076314763838677842009 4383807236072879008381507)
                ·
                  refine ⟨6575710854109318512572261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383807236072879008381507 6575710854109318512572261)
                  ·
                    refine ⟨1232945785145497221107299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575710854109318512572261 1232945785145497221107299)
                    ·
                      rfl

theorem cell23_7203460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_7203460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203460 prefixEnd_7203460 := by exact prefixLift 7203460
  have htrace : WordTrace (prefixWord ++ tailWord_7203460) baseStart_7203460 baseEnd_7203460 := by
    simpa [prefixWord, tailWord_7203460, baseEnd_7203460] using wordTrace_append hprefix tailTrace_7203460
  have hstable : (prefixWord ++ tailWord_7203460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203460).length < 2 ^ (prefixWord ++ tailWord_7203460).sum := by decide
  have hdescent : baseEnd_7203460 < baseStart_7203460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203486 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_7203486 : Nat := 118140960795 + 7203486 * 2 ^ 59
def prefixEnd_7203486 : Nat := 4983230072969 + 3 ^ 40 * 7203486 * 2
def baseEnd_7203486 : Nat := 1232950235311169520532259

theorem tailTrace_7203486 : CollatzResearch.WordTrace tailWord_7203486 prefixEnd_7203486 1232950235311169520532259 := by
  unfold tailWord_7203486
  simp only [CollatzResearch.WordTrace]
  refine ⟨32841589847625994288513789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175155145854005302872073541 32841589847625994288513789)
  ·
    refine ⟨12315596192859747858192671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32841589847625994288513789 12315596192859747858192671)
    ·
      refine ⟨18473394289289621787289007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315596192859747858192671 18473394289289621787289007)
      ·
        refine ⟨27710091433934432680933511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18473394289289621787289007 27710091433934432680933511)
        ·
          refine ⟨41565137150901649021400267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27710091433934432680933511 41565137150901649021400267)
          ·
            refine ⟨62347705726352473532100401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41565137150901649021400267 62347705726352473532100401)
            ·
              refine ⟨46760779294764355149075301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62347705726352473532100401 46760779294764355149075301)
              ·
                refine ⟨8767646117768316590451619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46760779294764355149075301 8767646117768316590451619)
                ·
                  refine ⟨13151469176652474885677429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8767646117768316590451619 13151469176652474885677429)
                  ·
                    refine ⟨1232950235311169520532259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13151469176652474885677429 1232950235311169520532259)
                    ·
                      rfl

theorem cell23_7203486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_7203486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203486 prefixEnd_7203486 := by exact prefixLift 7203486
  have htrace : WordTrace (prefixWord ++ tailWord_7203486) baseStart_7203486 baseEnd_7203486 := by
    simpa [prefixWord, tailWord_7203486, baseEnd_7203486] using wordTrace_append hprefix tailTrace_7203486
  have hstable : (prefixWord ++ tailWord_7203486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203486).length < 2 ^ (prefixWord ++ tailWord_7203486).sum := by decide
  have hdescent : baseEnd_7203486 < baseStart_7203486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203506 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_7203506 : Nat := 118140960795 + 7203506 * 2 ^ 59
def prefixEnd_7203506 : Nat := 4983230072969 + 3 ^ 40 * 7203506 * 2
def baseEnd_7203506 : Nat := 3698860975546598483346685

theorem tailTrace_7203506 : CollatzResearch.WordTrace tailWord_7203506 prefixEnd_7203506 3698860975546598483346685 := by
  unfold tailWord_7203506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65683362060233874430959593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175155632160623665149225581 65683362060233874430959593)
  ·
    refine ⟨49262521545175405823219695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65683362060233874430959593 49262521545175405823219695)
    ·
      refine ⟨73893782317763108734829543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49262521545175405823219695 73893782317763108734829543)
      ·
        refine ⟨110840673476644663102244315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73893782317763108734829543 110840673476644663102244315)
        ·
          refine ⟨166261010214966994653366473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110840673476644663102244315 166261010214966994653366473)
          ·
            refine ⟨124695757661225245990024855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166261010214966994653366473 124695757661225245990024855)
            ·
              refine ⟨187043636491837868985037283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124695757661225245990024855 187043636491837868985037283)
              ·
                refine ⟨280565454737756803477555925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187043636491837868985037283 280565454737756803477555925)
                ·
                  refine ⟨6575752845416175081505217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 280565454737756803477555925 6575752845416175081505217)
                  ·
                    refine ⟨4931814634062131311128913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575752845416175081505217 4931814634062131311128913)
                    ·
                      refine ⟨3698860975546598483346685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931814634062131311128913 3698860975546598483346685)
                      ·
                        rfl

theorem cell23_7203506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_7203506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203506 prefixEnd_7203506 := by exact prefixLift 7203506
  have htrace : WordTrace (prefixWord ++ tailWord_7203506) baseStart_7203506 baseEnd_7203506 := by
    simpa [prefixWord, tailWord_7203506, baseEnd_7203506] using wordTrace_append hprefix tailTrace_7203506
  have hstable : (prefixWord ++ tailWord_7203506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203506).length < 2 ^ (prefixWord ++ tailWord_7203506).sum := by decide
  have hdescent : baseEnd_7203506 < baseStart_7203506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203556 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_7203556 : Nat := 118140960795 + 7203556 * 2 ^ 59
def prefixEnd_7203556 : Nat := 4983230072969 + 3 ^ 40 * 7203556 * 2
def baseEnd_7203556 : Nat := 3698886649579323287721455

theorem tailTrace_7203556 : CollatzResearch.WordTrace tailWord_7203556 prefixEnd_7203556 3698886649579323287721455 := by
  unfold tailWord_7203556
  simp only [CollatzResearch.WordTrace]
  refine ⟨131367635945377178131579261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175156847927169570842105681 131367635945377178131579261)
  ·
    refine ⟨49262863479516441799342223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131367635945377178131579261 49262863479516441799342223)
    ·
      refine ⟨73894295219274662699013335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49262863479516441799342223 73894295219274662699013335)
      ·
        refine ⟨110841442828911994048520003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73894295219274662699013335 110841442828911994048520003)
        ·
          refine ⟨166262164243367991072780005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110841442828911994048520003 166262164243367991072780005)
          ·
            refine ⟨31174155795631498326146251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166262164243367991072780005 31174155795631498326146251)
            ·
              refine ⟨46761233693447247489219377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31174155795631498326146251 46761233693447247489219377)
              ·
                refine ⟨35070925270085435616914533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46761233693447247489219377 35070925270085435616914533)
                ·
                  refine ⟨6575798488141019178171475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35070925270085435616914533 6575798488141019178171475)
                  ·
                    refine ⟨9863697732211528767257213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6575798488141019178171475 9863697732211528767257213)
                    ·
                      refine ⟨3698886649579323287721455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9863697732211528767257213 3698886649579323287721455)
                      ·
                        rfl

theorem cell23_7203556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_7203556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203556 prefixEnd_7203556 := by exact prefixLift 7203556
  have htrace : WordTrace (prefixWord ++ tailWord_7203556) baseStart_7203556 baseEnd_7203556 := by
    simpa [prefixWord, tailWord_7203556, baseEnd_7203556] using wordTrace_append hprefix tailTrace_7203556
  have hstable : (prefixWord ++ tailWord_7203556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203556).length < 2 ^ (prefixWord ++ tailWord_7203556).sum := by decide
  have hdescent : baseEnd_7203556 < baseStart_7203556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203557 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7203557 : Nat := 118140960795 + 7203557 * 2 ^ 59
def prefixEnd_7203557 : Nat := 4983230072969 + 3 ^ 40 * 7203557 * 2
def baseEnd_7203557 : Nat := 3698887163059977783808951

theorem tailTrace_7203557 : CollatzResearch.WordTrace tailWord_7203557 prefixEnd_7203557 3698887163059977783808951 := by
  unfold tailWord_7203557
  simp only [CollatzResearch.WordTrace]
  refine ⟨262735308363750733433944925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175156872242500488955963283 262735308363750733433944925)
  ·
    refine ⟨98525740636406525037729347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262735308363750733433944925 98525740636406525037729347)
    ·
      refine ⟨147788610954609787556594021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98525740636406525037729347 147788610954609787556594021)
      ·
        refine ⟨27710364553989335166861379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147788610954609787556594021 27710364553989335166861379)
        ·
          refine ⟨41565546830984002750292069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27710364553989335166861379 41565546830984002750292069)
          ·
            refine ⟨7793540030809500515679763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41565546830984002750292069 7793540030809500515679763)
            ·
              refine ⟨11690310046214250773519645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793540030809500515679763 11690310046214250773519645)
              ·
                refine ⟨4383866267330344040069867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11690310046214250773519645 4383866267330344040069867)
                ·
                  refine ⟨6575799400995516060104801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383866267330344040069867 6575799400995516060104801)
                  ·
                    refine ⟨4931849550746637045078601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575799400995516060104801 4931849550746637045078601)
                    ·
                      refine ⟨3698887163059977783808951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931849550746637045078601 3698887163059977783808951)
                      ·
                        rfl

theorem cell23_7203557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7203557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203557 prefixEnd_7203557 := by exact prefixLift 7203557
  have htrace : WordTrace (prefixWord ++ tailWord_7203557) baseStart_7203557 baseEnd_7203557 := by
    simpa [prefixWord, tailWord_7203557, baseEnd_7203557] using wordTrace_append hprefix tailTrace_7203557
  have hstable : (prefixWord ++ tailWord_7203557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203557).length < 2 ^ (prefixWord ++ tailWord_7203557).sum := by decide
  have hdescent : baseEnd_7203557 < baseStart_7203557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203596 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_7203596 : Nat := 118140960795 + 7203596 * 2 ^ 59
def prefixEnd_7203596 : Nat := 4983230072969 + 3 ^ 40 * 7203596 * 2
def baseEnd_7203596 : Nat := 3698907188805503131221271

theorem tailTrace_7203596 : CollatzResearch.WordTrace tailWord_7203596 prefixEnd_7203596 3698907188805503131221271 := by
  unfold tailWord_7203596
  simp only [CollatzResearch.WordTrace]
  refine ⟨131368365405304721547307321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175157820540406295396409761 131368365405304721547307321)
  ·
    refine ⟨98526274053978541160480491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131368365405304721547307321 98526274053978541160480491)
    ·
      refine ⟨147789411080967811740720737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98526274053978541160480491 147789411080967811740720737)
      ·
        refine ⟨110842058310725858805540553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147789411080967811740720737 110842058310725858805540553)
        ·
          refine ⟨83131543733044394104155415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110842058310725858805540553 83131543733044394104155415)
          ·
            refine ⟨124697315599566591156233123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83131543733044394104155415 124697315599566591156233123)
            ·
              refine ⟨187045973399349886734349685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124697315599566591156233123 187045973399349886734349685)
              ·
                refine ⟨17535560006189051881345283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187045973399349886734349685 17535560006189051881345283)
                ·
                  refine ⟨26303340009283577822017925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17535560006189051881345283 26303340009283577822017925)
                  ·
                    refine ⟨4931876251740670841628361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26303340009283577822017925 4931876251740670841628361)
                    ·
                      refine ⟨3698907188805503131221271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931876251740670841628361 3698907188805503131221271)
                      ·
                        rfl

theorem cell23_7203596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_7203596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203596 prefixEnd_7203596 := by exact prefixLift 7203596
  have htrace : WordTrace (prefixWord ++ tailWord_7203596) baseStart_7203596 baseEnd_7203596 := by
    simpa [prefixWord, tailWord_7203596, baseEnd_7203596] using wordTrace_append hprefix tailTrace_7203596
  have hstable : (prefixWord ++ tailWord_7203596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203596).length < 2 ^ (prefixWord ++ tailWord_7203596).sum := by decide
  have hdescent : baseEnd_7203596 < baseStart_7203596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203656 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_7203656 : Nat := 118140960795 + 7203656 * 2 ^ 59
def prefixEnd_7203656 : Nat := 4983230072969 + 3 ^ 40 * 7203656 * 2
def baseEnd_7203656 : Nat := 3698937997644772896470995

theorem tailTrace_7203656 : CollatzResearch.WordTrace tailWord_7203656 prefixEnd_7203656 3698937997644772896470995 := by
  unfold tailWord_7203656
  simp only [CollatzResearch.WordTrace]
  refine ⟨131369459595196036670899411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175159279460261382227865881 131369459595196036670899411)
  ·
    refine ⟨197054189392794055006349117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131369459595196036670899411 197054189392794055006349117)
    ·
      refine ⟨73895321022297770627380919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197054189392794055006349117 73895321022297770627380919)
      ·
        refine ⟨110842981533446655941071379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73895321022297770627380919 110842981533446655941071379)
        ·
          refine ⟨166264472300169983911607069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110842981533446655941071379 166264472300169983911607069)
          ·
            refine ⟨62349177112563743966852651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166264472300169983911607069 62349177112563743966852651)
            ·
              refine ⟨93523765668845615950278977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62349177112563743966852651 93523765668845615950278977)
              ·
                refine ⟨70142824251634211962709233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93523765668845615950278977 70142824251634211962709233)
                ·
                  refine ⟨52607118188725658972031925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70142824251634211962709233 52607118188725658972031925)
                  ·
                    refine ⟨4931917330193030528627993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52607118188725658972031925 4931917330193030528627993)
                    ·
                      refine ⟨3698937997644772896470995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4931917330193030528627993 3698937997644772896470995)
                      ·
                        rfl

theorem cell23_7203656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_7203656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203656 prefixEnd_7203656 := by exact prefixLift 7203656
  have htrace : WordTrace (prefixWord ++ tailWord_7203656) baseStart_7203656 baseEnd_7203656 := by
    simpa [prefixWord, tailWord_7203656, baseEnd_7203656] using wordTrace_append hprefix tailTrace_7203656
  have hstable : (prefixWord ++ tailWord_7203656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203656).length < 2 ^ (prefixWord ++ tailWord_7203656).sum := by decide
  have hdescent : baseEnd_7203656 < baseStart_7203656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203696 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_7203696 : Nat := 118140960795 + 7203696 * 2 ^ 59
def prefixEnd_7203696 : Nat := 4983230072969 + 3 ^ 40 * 7203696 * 2
def baseEnd_7203696 : Nat := 1232986178956984246656937

theorem tailTrace_7203696 : CollatzResearch.WordTrace tailWord_7203696 prefixEnd_7203696 1232986178956984246656937 := by
  unfold tailWord_7203696
  simp only [CollatzResearch.WordTrace]
  refine ⟨131370189055123580086627471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175160252073498106782169961 131370189055123580086627471)
  ·
    refine ⟨197055283582685370129941207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131370189055123580086627471 197055283582685370129941207)
    ·
      refine ⟨295582925374028055194911811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197055283582685370129941207 295582925374028055194911811)
      ·
        refine ⟨443374388061042082792367717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295582925374028055194911811 443374388061042082792367717)
        ·
          refine ⟨83132697761445390523568947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443374388061042082792367717 83132697761445390523568947)
          ·
            refine ⟨124699046642168085785353421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83132697761445390523568947 124699046642168085785353421)
            ·
              refine ⟨46762142490813032169507533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124699046642168085785353421 46762142490813032169507533)
              ·
                refine ⟨17535803434054887063565325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46762142490813032169507533 17535803434054887063565325)
                ·
                  refine ⟨6575926287770582648836997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17535803434054887063565325 6575926287770582648836997)
                  ·
                    refine ⟨1232986178956984246656937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6575926287770582648836997 1232986178956984246656937)
                    ·
                      rfl

theorem cell23_7203696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_7203696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203696 prefixEnd_7203696 := by exact prefixLift 7203696
  have htrace : WordTrace (prefixWord ++ tailWord_7203696) baseStart_7203696 baseEnd_7203696 := by
    simpa [prefixWord, tailWord_7203696, baseEnd_7203696] using wordTrace_append hprefix tailTrace_7203696
  have hstable : (prefixWord ++ tailWord_7203696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203696).length < 2 ^ (prefixWord ++ tailWord_7203696).sum := by decide
  have hdescent : baseEnd_7203696 < baseStart_7203696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203740 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7203740 : Nat := 118140960795 + 7203740 * 2 ^ 59
def prefixEnd_7203740 : Nat := 4983230072969 + 3 ^ 40 * 7203740 * 2
def baseEnd_7203740 : Nat := 3698981130019750567820609

theorem tailTrace_7203740 : CollatzResearch.WordTrace tailWord_7203740 prefixEnd_7203740 3698981130019750567820609 := by
  unfold tailWord_7203740
  simp only [CollatzResearch.WordTrace]
  refine ⟨131370991461043877843928337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175161321948058503791904449 131370991461043877843928337)
  ·
    refine ⟨98528243595782908382946253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131370991461043877843928337 98528243595782908382946253)
    ·
      refine ⟨36948091348418590643604845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98528243595782908382946253 36948091348418590643604845)
      ·
        refine ⟨13855534255656971491351817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36948091348418590643604845 13855534255656971491351817)
        ·
          refine ⟨10391650691742728618513863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13855534255656971491351817 10391650691742728618513863)
          ·
            refine ⟨15587476037614092927770795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10391650691742728618513863 15587476037614092927770795)
            ·
              refine ⟨23381214056421139391656193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15587476037614092927770795 23381214056421139391656193)
              ·
                refine ⟨17535910542315854543742145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23381214056421139391656193 17535910542315854543742145)
                ·
                  refine ⟨13151932906736890907806609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17535910542315854543742145 13151932906736890907806609)
                  ·
                    refine ⟨9863949680052668180854957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13151932906736890907806609 9863949680052668180854957)
                    ·
                      refine ⟨3698981130019750567820609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9863949680052668180854957 3698981130019750567820609)
                      ·
                        rfl

theorem cell23_7203740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7203740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203740 prefixEnd_7203740 := by exact prefixLift 7203740
  have htrace : WordTrace (prefixWord ++ tailWord_7203740) baseStart_7203740 baseEnd_7203740 := by
    simpa [prefixWord, tailWord_7203740, baseEnd_7203740] using wordTrace_append hprefix tailTrace_7203740
  have hstable : (prefixWord ++ tailWord_7203740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203740).length < 2 ^ (prefixWord ++ tailWord_7203740).sum := by decide
  have hdescent : baseEnd_7203740 < baseStart_7203740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203749 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_7203749 : Nat := 118140960795 + 7203749 * 2 ^ 59
def prefixEnd_7203749 : Nat := 4983230072969 + 3 ^ 40 * 7203749 * 2
def baseEnd_7203749 : Nat := 3698985751345641032608067

theorem tailTrace_7203749 : CollatzResearch.WordTrace tailWord_7203749 prefixEnd_7203749 3698985751345641032608067 := by
  unfold tailWord_7203749
  simp only [CollatzResearch.WordTrace]
  refine ⟨262742311179055150224934301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175161540786036766816622867 262742311179055150224934301)
  ·
    refine ⟨98528366692145681334350363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262742311179055150224934301 98528366692145681334350363)
    ·
      refine ⟨147792550038218522001525545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98528366692145681334350363 147792550038218522001525545)
      ·
        refine ⟨110844412528663891501144159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147792550038218522001525545 110844412528663891501144159)
        ·
          refine ⟨166266618792995837251716239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110844412528663891501144159 166266618792995837251716239)
          ·
            refine ⟨249399928189493755877574359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166266618792995837251716239 249399928189493755877574359)
            ·
              refine ⟨374099892284240633816361539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249399928189493755877574359 374099892284240633816361539)
              ·
                refine ⟨561149838426360950724542309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374099892284240633816361539 561149838426360950724542309)
                ·
                  refine ⟨105215594704942678260851683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561149838426360950724542309 105215594704942678260851683)
                  ·
                    refine ⟨157823392057414017391277525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105215594704942678260851683 157823392057414017391277525)
                    ·
                      refine ⟨3698985751345641032608067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157823392057414017391277525 3698985751345641032608067)
                      ·
                        rfl

theorem cell23_7203749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_7203749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203749 prefixEnd_7203749 := by exact prefixLift 7203749
  have htrace : WordTrace (prefixWord ++ tailWord_7203749) baseStart_7203749 baseEnd_7203749 := by
    simpa [prefixWord, tailWord_7203749, baseEnd_7203749] using wordTrace_append hprefix tailTrace_7203749
  have hstable : (prefixWord ++ tailWord_7203749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203749).length < 2 ^ (prefixWord ++ tailWord_7203749).sum := by decide
  have hdescent : baseEnd_7203749 < baseStart_7203749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203773 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_7203773 : Nat := 118140960795 + 7203773 * 2 ^ 59
def prefixEnd_7203773 : Nat := 4983230072969 + 3 ^ 40 * 7203773 * 2
def baseEnd_7203773 : Nat := 1232999358293782979569319

theorem tailTrace_7203773 : CollatzResearch.WordTrace tailWord_7203773 prefixEnd_7203773 1232999358293782979569319 := by
  unfold tailWord_7203773
  simp only [CollatzResearch.WordTrace]
  refine ⟨262743186530968202323807973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175162124353978801549205315 262743186530968202323807973)
  ·
    refine ⟨49264347474556537935713995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262743186530968202323807973 49264347474556537935713995)
    ·
      refine ⟨73896521211834806903570993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49264347474556537935713995 73896521211834806903570993)
      ·
        refine ⟨55422390908876105177678245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73896521211834806903570993 55422390908876105177678245)
        ·
          refine ⟨10391698295414269720814671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55422390908876105177678245 10391698295414269720814671)
          ·
            refine ⟨15587547443121404581222007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10391698295414269720814671 15587547443121404581222007)
            ·
              refine ⟨23381321164682106871833011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15587547443121404581222007 23381321164682106871833011)
              ·
                refine ⟨35071981747023160307749517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23381321164682106871833011 35071981747023160307749517)
                ·
                  refine ⟨13151993155133685115406069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35071981747023160307749517 13151993155133685115406069)
                  ·
                    refine ⟨1232999358293782979569319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13151993155133685115406069 1232999358293782979569319)
                    ·
                      rfl

theorem cell23_7203773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_7203773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203773 prefixEnd_7203773 := by exact prefixLift 7203773
  have htrace : WordTrace (prefixWord ++ tailWord_7203773) baseStart_7203773 baseEnd_7203773 := by
    simpa [prefixWord, tailWord_7203773, baseEnd_7203773] using wordTrace_append hprefix tailTrace_7203773
  have hstable : (prefixWord ++ tailWord_7203773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203773).length < 2 ^ (prefixWord ++ tailWord_7203773).sum := by decide
  have hdescent : baseEnd_7203773 < baseStart_7203773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203790 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_7203790 : Nat := 118140960795 + 7203790 * 2 ^ 59
def prefixEnd_7203790 : Nat := 4983230072969 + 3 ^ 40 * 7203790 * 2
def baseEnd_7203790 : Nat := 1233002268017491790731793

theorem tailTrace_7203790 : CollatzResearch.WordTrace tailWord_7203790 prefixEnd_7203790 1233002268017491790731793 := by
  unfold tailWord_7203790
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842975821488326778397103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175162537714604409484784549 32842975821488326778397103)
  ·
    refine ⟨49264463732232490167595655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32842975821488326778397103 49264463732232490167595655)
    ·
      refine ⟨73896695598348735251393483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49264463732232490167595655 73896695598348735251393483)
      ·
        refine ⟨110845043397523102877090225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73896695598348735251393483 110845043397523102877090225)
        ·
          refine ⟨83133782548142327157817669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110845043397523102877090225 83133782548142327157817669)
          ·
            refine ⟨15587584227776686342090813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83133782548142327157817669 15587584227776686342090813)
            ·
              refine ⟨5845344085416257378284055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15587584227776686342090813 5845344085416257378284055)
              ·
                refine ⟨8768016128124386067426083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845344085416257378284055 8768016128124386067426083)
                ·
                  refine ⟨13152024192186579101139125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768016128124386067426083 13152024192186579101139125)
                  ·
                    refine ⟨1233002268017491790731793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13152024192186579101139125 1233002268017491790731793)
                    ·
                      rfl

theorem cell23_7203790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_7203790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203790 prefixEnd_7203790 := by exact prefixLift 7203790
  have htrace : WordTrace (prefixWord ++ tailWord_7203790) baseStart_7203790 baseEnd_7203790 := by
    simpa [prefixWord, tailWord_7203790, baseEnd_7203790] using wordTrace_append hprefix tailTrace_7203790
  have hstable : (prefixWord ++ tailWord_7203790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203790).length < 2 ^ (prefixWord ++ tailWord_7203790).sum := by decide
  have hdescent : baseEnd_7203790 < baseStart_7203790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203810 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7203810 : Nat := 118140960795 + 7203810 * 2 ^ 59
def prefixEnd_7203810 : Nat := 4983230072969 + 3 ^ 40 * 7203810 * 2
def baseEnd_7203810 : Nat := 3699017073665565293945287

theorem tailTrace_7203810 : CollatzResearch.WordTrace tailWord_7203810 prefixEnd_7203810 3699017073665565293945287 := by
  unfold tailWord_7203810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65686134007958539410726221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175163024021222771761936589 65686134007958539410726221)
  ·
    refine ⟨24632300252984452279022333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65686134007958539410726221 24632300252984452279022333)
    ·
      refine ⟨9237112594869169604633375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24632300252984452279022333 9237112594869169604633375)
      ·
        refine ⟨13855668892303754406950063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237112594869169604633375 13855668892303754406950063)
        ·
          refine ⟨20783503338455631610425095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855668892303754406950063 20783503338455631610425095)
          ·
            refine ⟨31175255007683447415637643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20783503338455631610425095 31175255007683447415637643)
            ·
              refine ⟨46762882511525171123456465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31175255007683447415637643 46762882511525171123456465)
              ·
                refine ⟨35072161883643878342592349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46762882511525171123456465 35072161883643878342592349)
                ·
                  refine ⟨13152060706366454378472131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35072161883643878342592349 13152060706366454378472131)
                  ·
                    refine ⟨19728091059549681567708197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13152060706366454378472131 19728091059549681567708197)
                    ·
                      refine ⟨3699017073665565293945287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19728091059549681567708197 3699017073665565293945287)
                      ·
                        rfl

theorem cell23_7203810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7203810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203810 prefixEnd_7203810 := by exact prefixLift 7203810
  have htrace : WordTrace (prefixWord ++ tailWord_7203810) baseStart_7203810 baseEnd_7203810 := by
    simpa [prefixWord, tailWord_7203810, baseEnd_7203810] using wordTrace_append hprefix tailTrace_7203810
  have hstable : (prefixWord ++ tailWord_7203810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203810).length < 2 ^ (prefixWord ++ tailWord_7203810).sum := by decide
  have hdescent : baseEnd_7203810 < baseStart_7203810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203816 : List Nat := [2, 1, 4, 1, 1, 1, 5, 8]
def baseStart_7203816 : Nat := 118140960795 + 7203816 * 2 ^ 59
def prefixEnd_7203816 : Nat := 4983230072969 + 3 ^ 40 * 7203816 * 2
def baseEnd_7203816 : Nat := 137000746464796010017417

theorem tailTrace_7203816 : CollatzResearch.WordTrace tailWord_7203816 prefixEnd_7203816 137000746464796010017417 := by
  unfold tailWord_7203816
  simp only [CollatzResearch.WordTrace]
  refine ⟨131372377434906210333811651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175163169913208280445082201 131372377434906210333811651)
  ·
    refine ⟨197058566152359315500717477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131372377434906210333811651 197058566152359315500717477)
    ·
      refine ⟨36948481153567371656384527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197058566152359315500717477 36948481153567371656384527)
      ·
        refine ⟨55422721730351057484576791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36948481153567371656384527 55422721730351057484576791)
        ·
          refine ⟨83134082595526586226865187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55422721730351057484576791 83134082595526586226865187)
          ·
            refine ⟨124701123893289879340297781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83134082595526586226865187 124701123893289879340297781)
            ·
              refine ⟨11690730364995926188152917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124701123893289879340297781 11690730364995926188152917)
              ·
                refine ⟨137000746464796010017417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11690730364995926188152917 137000746464796010017417)
                ·
                  rfl

theorem cell23_7203816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 8].length) (baseStart_7203816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203816 prefixEnd_7203816 := by exact prefixLift 7203816
  have htrace : WordTrace (prefixWord ++ tailWord_7203816) baseStart_7203816 baseEnd_7203816 := by
    simpa [prefixWord, tailWord_7203816, baseEnd_7203816] using wordTrace_append hprefix tailTrace_7203816
  have hstable : (prefixWord ++ tailWord_7203816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203816).length < 2 ^ (prefixWord ++ tailWord_7203816).sum := by decide
  have hdescent : baseEnd_7203816 < baseStart_7203816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203823 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_7203823 : Nat := 118140960795 + 7203823 * 2 ^ 59
def prefixEnd_7203823 : Nat := 4983230072969 + 3 ^ 40 * 7203823 * 2
def baseEnd_7203823 : Nat := 3699023748914073743082727

theorem tailTrace_7203823 : CollatzResearch.WordTrace tailWord_7203823 prefixEnd_7203823 3699023748914073743082727 := by
  unfold tailWord_7203823
  simp only [CollatzResearch.WordTrace]
  refine ⟨262745010180787060863128123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175163340120524707242085415 262745010180787060863128123)
  ·
    refine ⟨394117515271180591294692185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262745010180787060863128123 394117515271180591294692185)
    ·
      refine ⟨295588136453385443471019139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394117515271180591294692185 295588136453385443471019139)
      ·
        refine ⟨443382204680078165206528709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295588136453385443471019139 443382204680078165206528709)
        ·
          refine ⟨83134163377514655976224133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443382204680078165206528709 83134163377514655976224133)
          ·
            refine ⟨15587655633283997995542025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83134163377514655976224133 15587655633283997995542025)
            ·
              refine ⟨11690741724962998496656519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15587655633283997995542025 11690741724962998496656519)
              ·
                refine ⟨17536112587444497744984779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11690741724962998496656519 17536112587444497744984779)
                ·
                  refine ⟨26304168881166746617477169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17536112587444497744984779 26304168881166746617477169)
                  ·
                    refine ⟨19728126660875059963107877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26304168881166746617477169 19728126660875059963107877)
                    ·
                      refine ⟨3699023748914073743082727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19728126660875059963107877 3699023748914073743082727)
                      ·
                        rfl

theorem cell23_7203823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_7203823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203823 prefixEnd_7203823 := by exact prefixLift 7203823
  have htrace : WordTrace (prefixWord ++ tailWord_7203823) baseStart_7203823 baseEnd_7203823 := by
    simpa [prefixWord, tailWord_7203823, baseEnd_7203823] using wordTrace_append hprefix tailTrace_7203823
  have hstable : (prefixWord ++ tailWord_7203823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203823).length < 2 ^ (prefixWord ++ tailWord_7203823).sum := by decide
  have hdescent : baseEnd_7203823 < baseStart_7203823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203830 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7203830 : Nat := 118140960795 + 7203830 * 2 ^ 59
def prefixEnd_7203830 : Nat := 4983230072969 + 3 ^ 40 * 7203830 * 2
def baseEnd_7203830 : Nat := 3699027343278655215695195

theorem tailTrace_7203830 : CollatzResearch.WordTrace tailWord_7203830 prefixEnd_7203830 3699027343278655215695195 := by
  unfold tailWord_7203830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421579093235106316164559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175163510327841134039088629 16421579093235106316164559)
  ·
    refine ⟨24632368639852659474246839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16421579093235106316164559 24632368639852659474246839)
    ·
      refine ⟨36948552959778989211370259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24632368639852659474246839 36948552959778989211370259)
      ·
        refine ⟨55422829439668483817055389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36948552959778989211370259 55422829439668483817055389)
        ·
          refine ⟨20783561039875681431395771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55422829439668483817055389 20783561039875681431395771)
          ·
            refine ⟨31175341559813522147093657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20783561039875681431395771 31175341559813522147093657)
            ·
              refine ⟨23381506169860141610320243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31175341559813522147093657 23381506169860141610320243)
              ·
                refine ⟨35072259254790212415480365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23381506169860141610320243 35072259254790212415480365)
                ·
                  refine ⟨13152097220546329655805137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35072259254790212415480365 13152097220546329655805137)
                  ·
                    refine ⟨9864072915409747241853853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13152097220546329655805137 9864072915409747241853853)
                    ·
                      refine ⟨3699027343278655215695195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9864072915409747241853853 3699027343278655215695195)
                      ·
                        rfl

theorem cell23_7203830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7203830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203830 prefixEnd_7203830 := by exact prefixLift 7203830
  have htrace : WordTrace (prefixWord ++ tailWord_7203830) baseStart_7203830 baseEnd_7203830 := by
    simpa [prefixWord, tailWord_7203830, baseEnd_7203830] using wordTrace_append hprefix tailTrace_7203830
  have hstable : (prefixWord ++ tailWord_7203830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203830).length < 2 ^ (prefixWord ++ tailWord_7203830).sum := by decide
  have hdescent : baseEnd_7203830 < baseStart_7203830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203877 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_7203877 : Nat := 118140960795 + 7203877 * 2 ^ 59
def prefixEnd_7203877 : Nat := 4983230072969 + 3 ^ 40 * 7203877 * 2
def baseEnd_7203877 : Nat := 3699051476869416531807479

theorem tailTrace_7203877 : CollatzResearch.WordTrace tailWord_7203877 prefixEnd_7203877 3699051476869416531807479 := by
  unfold tailWord_7203877
  simp only [CollatzResearch.WordTrace]
  refine ⟨262746979722591428085593885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175164653148394285390395923 262746979722591428085593885)
  ·
    refine ⟨98530117395971785532097707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262746979722591428085593885 98530117395971785532097707)
    ·
      refine ⟨147795176093957678298146561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98530117395971785532097707 147795176093957678298146561)
      ·
        refine ⟨110846382070468258723609921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147795176093957678298146561 110846382070468258723609921)
        ·
          refine ⟨83134786552851194042707441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110846382070468258723609921 83134786552851194042707441)
          ·
            refine ⟨62351089914638395532030581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83134786552851194042707441 62351089914638395532030581)
            ·
              refine ⟨5845414679497349581127867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62351089914638395532030581 5845414679497349581127867)
              ·
                refine ⟨8768122019246024371691801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845414679497349581127867 8768122019246024371691801)
                ·
                  refine ⟨6576091514434518278768851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768122019246024371691801 6576091514434518278768851)
                  ·
                    refine ⟨9864137271651777418153277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6576091514434518278768851 9864137271651777418153277)
                    ·
                      refine ⟨3699051476869416531807479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9864137271651777418153277 3699051476869416531807479)
                      ·
                        rfl

theorem cell23_7203877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_7203877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203877 prefixEnd_7203877 := by exact prefixLift 7203877
  have htrace : WordTrace (prefixWord ++ tailWord_7203877) baseStart_7203877 baseEnd_7203877 := by
    simpa [prefixWord, tailWord_7203877, baseEnd_7203877] using wordTrace_append hprefix tailTrace_7203877
  have hstable : (prefixWord ++ tailWord_7203877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203877).length < 2 ^ (prefixWord ++ tailWord_7203877).sum := by decide
  have hdescent : baseEnd_7203877 < baseStart_7203877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7203916 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7203916 : Nat := 118140960795 + 7203916 * 2 ^ 59
def prefixEnd_7203916 : Nat := 4983230072969 + 3 ^ 40 * 7203916 * 2
def baseEnd_7203916 : Nat := 3699071502614941879219799

theorem tailTrace_7203916 : CollatzResearch.WordTrace tailWord_7203916 prefixEnd_7203916 3699071502614941879219799 := by
  unfold tailWord_7203916
  simp only [CollatzResearch.WordTrace]
  refine ⟨131374201084725068873131801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175165601446300091830842401 131374201084725068873131801)
  ·
    refine ⟨98530650813543801654848851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131374201084725068873131801 98530650813543801654848851)
    ·
      refine ⟨147795976220315702482273277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98530650813543801654848851 147795976220315702482273277)
      ·
        refine ⟨55423491082618388430852479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147795976220315702482273277 55423491082618388430852479)
        ·
          refine ⟨83135236623927582646278719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55423491082618388430852479 83135236623927582646278719)
          ·
            refine ⟨124702854935891373969418079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83135236623927582646278719 124702854935891373969418079)
            ·
              refine ⟨187054282403837060954127119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124702854935891373969418079 187054282403837060954127119)
              ·
                refine ⟨280581423605755591431190679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187054282403837060954127119 280581423605755591431190679)
                ·
                  refine ⟨420872135408633387146786019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280581423605755591431190679 420872135408633387146786019)
                  ·
                    refine ⟨631308203112950080720179029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 420872135408633387146786019 631308203112950080720179029)
                    ·
                      refine ⟨3699071502614941879219799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 631308203112950080720179029 3699071502614941879219799)
                      ·
                        rfl

theorem cell23_7203916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7203916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7203916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7203916 prefixEnd_7203916 := by exact prefixLift 7203916
  have htrace : WordTrace (prefixWord ++ tailWord_7203916) baseStart_7203916 baseEnd_7203916 := by
    simpa [prefixWord, tailWord_7203916, baseEnd_7203916] using wordTrace_append hprefix tailTrace_7203916
  have hstable : (prefixWord ++ tailWord_7203916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7203916).length < 2 ^ (prefixWord ++ tailWord_7203916).sum := by decide
  have hdescent : baseEnd_7203916 < baseStart_7203916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7203916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204000 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_7204000 : Nat := 118140960795 + 7204000 * 2 ^ 59
def prefixEnd_7204000 : Nat := 4983230072969 + 3 ^ 40 * 7204000 * 2
def baseEnd_7204000 : Nat := 1233038211663306516856471

theorem tailTrace_7204000 : CollatzResearch.WordTrace tailWord_7204000 prefixEnd_7204000 1233038211663306516856471 := by
  unfold tailWord_7204000
  simp only [CollatzResearch.WordTrace]
  refine ⟨131375732950572910046160727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175167643934097213394880969 131375732950572910046160727)
  ·
    refine ⟨197063599425859365069241091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131375732950572910046160727 197063599425859365069241091)
    ·
      refine ⟨295595399138789047603861637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197063599425859365069241091 295595399138789047603861637)
      ·
        refine ⟨55424137338522946425724057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295595399138789047603861637 55424137338522946425724057)
        ·
          refine ⟨41568103003892209819293043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55424137338522946425724057 41568103003892209819293043)
          ·
            refine ⟨62352154505838314728939565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41568103003892209819293043 62352154505838314728939565)
            ·
              refine ⟨23382057939689368023352337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62352154505838314728939565 23382057939689368023352337)
              ·
                refine ⟨17536543454767026017514253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23382057939689368023352337 17536543454767026017514253)
                ·
                  refine ⟨6576203795537634756567845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17536543454767026017514253 6576203795537634756567845)
                  ·
                    refine ⟨1233038211663306516856471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576203795537634756567845 1233038211663306516856471)
                    ·
                      rfl

theorem cell23_7204000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_7204000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204000 prefixEnd_7204000 := by exact prefixLift 7204000
  have htrace : WordTrace (prefixWord ++ tailWord_7204000) baseStart_7204000 baseEnd_7204000 := by
    simpa [prefixWord, tailWord_7204000, baseEnd_7204000] using wordTrace_append hprefix tailTrace_7204000
  have hstable : (prefixWord ++ tailWord_7204000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204000).length < 2 ^ (prefixWord ++ tailWord_7204000).sum := by decide
  have hdescent : baseEnd_7204000 < baseStart_7204000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204007 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_7204007 : Nat := 118140960795 + 7204007 * 2 ^ 59
def prefixEnd_7204007 : Nat := 4983230072969 + 3 ^ 40 * 7204007 * 2
def baseEnd_7204007 : Nat := 3699118229354501023181881

theorem tailTrace_7204007 : CollatzResearch.WordTrace tailWord_7204007 prefixEnd_7204007 3699118229354501023181881 := by
  unfold tailWord_7204007
  simp only [CollatzResearch.WordTrace]
  refine ⟨262751721212120460287826275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175167814141413640191884183 262751721212120460287826275)
  ·
    refine ⟨394127581818180690431739413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262751721212120460287826275 394127581818180690431739413)
    ·
      refine ⟨18474730397727219863987785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 394127581818180690431739413 18474730397727219863987785)
      ·
        refine ⟨13856047798295414897990839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18474730397727219863987785 13856047798295414897990839)
        ·
          refine ⟨20784071697443122346986259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856047798295414897990839 20784071697443122346986259)
          ·
            refine ⟨31176107546164683520479389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784071697443122346986259 31176107546164683520479389)
            ·
              refine ⟨11691040329811756320179771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31176107546164683520479389 11691040329811756320179771)
              ·
                refine ⟨17536560494717634480269657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11691040329811756320179771 17536560494717634480269657)
                ·
                  refine ⟨13152420371038225860202243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17536560494717634480269657 13152420371038225860202243)
                  ·
                    refine ⟨19728630556557338790303365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13152420371038225860202243 19728630556557338790303365)
                    ·
                      refine ⟨3699118229354501023181881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19728630556557338790303365 3699118229354501023181881)
                      ·
                        rfl

theorem cell23_7204007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_7204007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204007 prefixEnd_7204007 := by exact prefixLift 7204007
  have htrace : WordTrace (prefixWord ++ tailWord_7204007) baseStart_7204007 baseEnd_7204007 := by
    simpa [prefixWord, tailWord_7204007, baseEnd_7204007] using wordTrace_append hprefix tailTrace_7204007
  have hstable : (prefixWord ++ tailWord_7204007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204007).length < 2 ^ (prefixWord ++ tailWord_7204007).sum := by decide
  have hdescent : baseEnd_7204007 < baseStart_7204007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204030 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_7204030 : Nat := 118140960795 + 7204030 * 2 ^ 59
def prefixEnd_7204030 : Nat := 4983230072969 + 3 ^ 40 * 7204030 * 2
def baseEnd_7204030 : Nat := 411014448823283825910475

theorem tailTrace_7204030 : CollatzResearch.WordTrace tailWord_7204030 prefixEnd_7204030 411014448823283825910475 := by
  unfold tailWord_7204030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32844070011379641901989193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175168373394024756810609029 32844070011379641901989193)
  ·
    refine ⟨24633052508534731426491895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32844070011379641901989193 24633052508534731426491895)
    ·
      refine ⟨36949578762802097139737843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24633052508534731426491895 36949578762802097139737843)
      ·
        refine ⟨55424368144203145709606765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36949578762802097139737843 55424368144203145709606765)
        ·
          refine ⟨20784138054076179641102537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55424368144203145709606765 20784138054076179641102537)
          ·
            refine ⟨15588103540557134730826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20784138054076179641102537 15588103540557134730826903)
            ·
              refine ⟨23382155310835702096240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15588103540557134730826903 23382155310835702096240355)
              ·
                refine ⟨35073232966253553144360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23382155310835702096240355 35073232966253553144360533)
                ·
                  refine ⟨411014448823283825910475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35073232966253553144360533 411014448823283825910475)
                  ·
                    rfl

theorem cell23_7204030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_7204030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204030 prefixEnd_7204030 := by exact prefixLift 7204030
  have htrace : WordTrace (prefixWord ++ tailWord_7204030) baseStart_7204030 baseEnd_7204030 := by
    simpa [prefixWord, tailWord_7204030, baseEnd_7204030] using wordTrace_append hprefix tailTrace_7204030
  have hstable : (prefixWord ++ tailWord_7204030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204030).length < 2 ^ (prefixWord ++ tailWord_7204030).sum := by decide
  have hdescent : baseEnd_7204030 < baseStart_7204030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204043 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 3, 5]
def baseStart_7204043 : Nat := 118140960795 + 7204043 * 2 ^ 59
def prefixEnd_7204043 : Nat := 4983230072969 + 3 ^ 40 * 7204043 * 2
def baseEnd_7204043 : Nat := 1233045571552687627443905

theorem tailTrace_7204043 : CollatzResearch.WordTrace tailWord_7204043 prefixEnd_7204043 1233045571552687627443905 := by
  unfold tailWord_7204043
  simp only [CollatzResearch.WordTrace]
  refine ⟨262753034239990038436136783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175168689493326692290757855 262753034239990038436136783)
  ·
    refine ⟨394129551359985057654205175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262753034239990038436136783 394129551359985057654205175)
    ·
      refine ⟨591194327039977586481307763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394129551359985057654205175 591194327039977586481307763)
      ·
        refine ⟨886791490559966379721961645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591194327039977586481307763 886791490559966379721961645)
        ·
          refine ⟨332546808959987392395735617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 886791490559966379721961645 332546808959987392395735617)
          ·
            refine ⟨249410106719990544296801713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332546808959987392395735617 249410106719990544296801713)
            ·
              refine ⟨187057580039992908222601285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249410106719990544296801713 187057580039992908222601285)
              ·
                refine ⟨35073296257498670291737741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187057580039992908222601285 35073296257498670291737741)
                ·
                  refine ⟨13152486096562001359401653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35073296257498670291737741 13152486096562001359401653)
                  ·
                    refine ⟨1233045571552687627443905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13152486096562001359401653 1233045571552687627443905)
                    ·
                      rfl

theorem cell23_7204043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 5].length) (baseStart_7204043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204043 prefixEnd_7204043 := by exact prefixLift 7204043
  have htrace : WordTrace (prefixWord ++ tailWord_7204043) baseStart_7204043 baseEnd_7204043 := by
    simpa [prefixWord, tailWord_7204043, baseEnd_7204043] using wordTrace_append hprefix tailTrace_7204043
  have hstable : (prefixWord ++ tailWord_7204043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204043).length < 2 ^ (prefixWord ++ tailWord_7204043).sum := by decide
  have hdescent : baseEnd_7204043 < baseStart_7204043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204077 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_7204077 : Nat := 118140960795 + 7204077 * 2 ^ 59
def prefixEnd_7204077 : Nat := 4983230072969 + 3 ^ 40 * 7204077 * 2
def baseEnd_7204077 : Nat := 1233051391000105249768853

theorem tailTrace_7204077 : CollatzResearch.WordTrace tailWord_7204077 prefixEnd_7204077 1233051391000105249768853 := by
  unfold tailWord_7204077
  simp only [CollatzResearch.WordTrace]
  refine ⟨262754274321866862242874485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175169516214577908161916323 262754274321866862242874485)
  ·
    refine ⟨24633213217675018335269483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262754274321866862242874485 24633213217675018335269483)
    ·
      refine ⟨36949819826512527502904225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24633213217675018335269483 36949819826512527502904225)
      ·
        refine ⟨27712364869884395627178169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36949819826512527502904225 27712364869884395627178169)
        ·
          refine ⟨20784273652413296720383627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27712364869884395627178169 20784273652413296720383627)
          ·
            refine ⟨31176410478619945080575441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784273652413296720383627 31176410478619945080575441)
            ·
              refine ⟨23382307858964958810431581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31176410478619945080575441 23382307858964958810431581)
              ·
                refine ⟨8768365447111859553911843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23382307858964958810431581 8768365447111859553911843)
                ·
                  refine ⟨13152548170667789330867765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768365447111859553911843 13152548170667789330867765)
                  ·
                    refine ⟨1233051391000105249768853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13152548170667789330867765 1233051391000105249768853)
                    ·
                      rfl

theorem cell23_7204077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_7204077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204077 prefixEnd_7204077 := by exact prefixLift 7204077
  have htrace : WordTrace (prefixWord ++ tailWord_7204077) baseStart_7204077 baseEnd_7204077 := by
    simpa [prefixWord, tailWord_7204077, baseEnd_7204077] using wordTrace_append hprefix tailTrace_7204077
  have hstable : (prefixWord ++ tailWord_7204077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204077).length < 2 ^ (prefixWord ++ tailWord_7204077).sum := by decide
  have hdescent : baseEnd_7204077 < baseStart_7204077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204090 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_7204090 : Nat := 118140960795 + 7204090 * 2 ^ 59
def prefixEnd_7204090 : Nat := 4983230072969 + 3 ^ 40 * 7204090 * 2
def baseEnd_7204090 : Nat := 1233053616082941399481333

theorem tailTrace_7204090 : CollatzResearch.WordTrace tailWord_7204090 prefixEnd_7204090 1233053616082941399481333 := by
  unfold tailWord_7204090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65688687117704941365774431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175169832313879843642065149 65688687117704941365774431)
  ·
    refine ⟨98533030676557412048661647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65688687117704941365774431 98533030676557412048661647)
    ·
      refine ⟨147799546014836118072992471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98533030676557412048661647 147799546014836118072992471)
      ·
        refine ⟨221699319022254177109488707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147799546014836118072992471 221699319022254177109488707)
        ·
          refine ⟨332548978533381265664233061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221699319022254177109488707 332548978533381265664233061)
          ·
            refine ⟨62352933475008987312043699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332548978533381265664233061 62352933475008987312043699)
            ·
              refine ⟨93529400212513480968065549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62352933475008987312043699 93529400212513480968065549)
              ·
                refine ⟨35073525079692555363024581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93529400212513480968065549 35073525079692555363024581)
                ·
                  refine ⟨6576285952442354130567109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35073525079692555363024581 6576285952442354130567109)
                  ·
                    refine ⟨1233053616082941399481333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576285952442354130567109 1233053616082941399481333)
                    ·
                      rfl

theorem cell23_7204090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_7204090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204090 prefixEnd_7204090 := by exact prefixLift 7204090
  have htrace : WordTrace (prefixWord ++ tailWord_7204090) baseStart_7204090 baseEnd_7204090 := by
    simpa [prefixWord, tailWord_7204090, baseEnd_7204090] using wordTrace_append hprefix tailTrace_7204090
  have hstable : (prefixWord ++ tailWord_7204090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204090).length < 2 ^ (prefixWord ++ tailWord_7204090).sum := by decide
  have hdescent : baseEnd_7204090 < baseStart_7204090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204107 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 2, 4]
def baseStart_7204107 : Nat := 118140960795 + 7204107 * 2 ^ 59
def prefixEnd_7204107 : Nat := 4983230072969 + 3 ^ 40 * 7204107 * 2
def baseEnd_7204107 : Nat := 1233056525806650210643807

theorem tailTrace_7204107 : CollatzResearch.WordTrace tailWord_7204107 prefixEnd_7204107 1233056525806650210643807 := by
  unfold tailWord_7204107
  simp only [CollatzResearch.WordTrace]
  refine ⟨262755368511758177366466575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175170245674505451577644383 262755368511758177366466575)
  ·
    refine ⟨394133052767637266049699863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262755368511758177366466575 394133052767637266049699863)
    ·
      refine ⟨591199579151455899074549795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394133052767637266049699863 591199579151455899074549795)
      ·
        refine ⟨886799368727183848611824693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591199579151455899074549795 886799368727183848611824693)
        ·
          refine ⟨83137440818173485807358565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 886799368727183848611824693 83137440818173485807358565)
          ·
            refine ⟨15588270153407528588879731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83137440818173485807358565 15588270153407528588879731)
            ·
              refine ⟨23382405230111292883319597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15588270153407528588879731 23382405230111292883319597)
              ·
                refine ⟨8768401961291734831244849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23382405230111292883319597 8768401961291734831244849)
                ·
                  refine ⟨6576301470968801123433637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768401961291734831244849 6576301470968801123433637)
                  ·
                    refine ⟨1233056525806650210643807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576301470968801123433637 1233056525806650210643807)
                    ·
                      rfl

theorem cell23_7204107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 4].length) (baseStart_7204107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204107 prefixEnd_7204107 := by exact prefixLift 7204107
  have htrace : WordTrace (prefixWord ++ tailWord_7204107) baseStart_7204107 baseEnd_7204107 := by
    simpa [prefixWord, tailWord_7204107, baseEnd_7204107] using wordTrace_append hprefix tailTrace_7204107
  have hstable : (prefixWord ++ tailWord_7204107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204107).length < 2 ^ (prefixWord ++ tailWord_7204107).sum := by decide
  have hdescent : baseEnd_7204107 < baseStart_7204107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204110 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7204110 : Nat := 118140960795 + 7204110 * 2 ^ 59
def prefixEnd_7204110 : Nat := 4983230072969 + 3 ^ 40 * 7204110 * 2
def baseEnd_7204110 : Nat := 3699171117861914120193907

theorem tailTrace_7204110 : CollatzResearch.WordTrace tailWord_7204110 prefixEnd_7204110 3699171117861914120193907 := by
  unfold tailWord_7204110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32844434741343413609853223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175170318620498205919217189 32844434741343413609853223)
  ·
    refine ⟨49266652112015120414779835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32844434741343413609853223 49266652112015120414779835)
    ·
      refine ⟨73899978168022680622169753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49266652112015120414779835 73899978168022680622169753)
      ·
        refine ⟨55424983626017010466627315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73899978168022680622169753 55424983626017010466627315)
        ·
          refine ⟨83137475439025515699940973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55424983626017010466627315 83137475439025515699940973)
          ·
            refine ⟨31176553289634568387477865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83137475439025515699940973 31176553289634568387477865)
            ·
              refine ⟨23382414967225926290608399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31176553289634568387477865 23382414967225926290608399)
              ·
                refine ⟨35073622450838889435912599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23382414967225926290608399 35073622450838889435912599)
                ·
                  refine ⟨52610433676258334153868899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35073622450838889435912599 52610433676258334153868899)
                  ·
                    refine ⟨78915650514387501230803349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52610433676258334153868899 78915650514387501230803349)
                    ·
                      refine ⟨3699171117861914120193907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78915650514387501230803349 3699171117861914120193907)
                      ·
                        rfl

theorem cell23_7204110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7204110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204110 prefixEnd_7204110 := by exact prefixLift 7204110
  have htrace : WordTrace (prefixWord ++ tailWord_7204110) baseStart_7204110 baseEnd_7204110 := by
    simpa [prefixWord, tailWord_7204110, baseEnd_7204110] using wordTrace_append hprefix tailTrace_7204110
  have hstable : (prefixWord ++ tailWord_7204110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204110).length < 2 ^ (prefixWord ++ tailWord_7204110).sum := by decide
  have hdescent : baseEnd_7204110 < baseStart_7204110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204127 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_7204127 : Nat := 118140960795 + 7204127 * 2 ^ 59
def prefixEnd_7204127 : Nat := 4983230072969 + 3 ^ 40 * 7204127 * 2
def baseEnd_7204127 : Nat := 3699179847033040553681329

theorem tailTrace_7204127 : CollatzResearch.WordTrace tailWord_7204127 prefixEnd_7204127 3699179847033040553681329 := by
  unfold tailWord_7204127
  simp only [CollatzResearch.WordTrace]
  refine ⟨262756097971685720782194635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175170731981123813854796423 262756097971685720782194635)
  ·
    refine ⟨394134146957528581173291953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262756097971685720782194635 394134146957528581173291953)
    ·
      refine ⟨295600610218146435879968965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394134146957528581173291953 295600610218146435879968965)
      ·
        refine ⟨55425114415902456727494181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295600610218146435879968965 55425114415902456727494181)
        ·
          refine ⟨10392208952981710636405159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55425114415902456727494181 10392208952981710636405159)
          ·
            refine ⟨15588313429472565954607739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10392208952981710636405159 15588313429472565954607739)
            ·
              refine ⟨23382470144208848931911609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15588313429472565954607739 23382470144208848931911609)
              ·
                refine ⟨17536852608156636698933707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23382470144208848931911609 17536852608156636698933707)
                ·
                  refine ⟨26305278912234955048400561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17536852608156636698933707 26305278912234955048400561)
                  ·
                    refine ⟨19728959184176216286300421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26305278912234955048400561 19728959184176216286300421)
                    ·
                      refine ⟨3699179847033040553681329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19728959184176216286300421 3699179847033040553681329)
                      ·
                        rfl

theorem cell23_7204127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_7204127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204127 prefixEnd_7204127 := by exact prefixLift 7204127
  have htrace : WordTrace (prefixWord ++ tailWord_7204127) baseStart_7204127 baseEnd_7204127 := by
    simpa [prefixWord, tailWord_7204127, baseEnd_7204127] using wordTrace_append hprefix tailTrace_7204127
  have hstable : (prefixWord ++ tailWord_7204127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204127).length < 2 ^ (prefixWord ++ tailWord_7204127).sum := by decide
  have hdescent : baseEnd_7204127 < baseStart_7204127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204141 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7204141 : Nat := 118140960795 + 7204141 * 2 ^ 59
def prefixEnd_7204141 : Nat := 4983230072969 + 3 ^ 40 * 7204141 * 2
def baseEnd_7204141 : Nat := 1233062345254067832968755

theorem tailTrace_7204141 : CollatzResearch.WordTrace tailWord_7204141 prefixEnd_7204141 1233062345254067832968755 := by
  unfold tailWord_7204141
  simp only [CollatzResearch.WordTrace]
  refine ⟨262756608593635001173204277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175171072395756667448802851 262756608593635001173204277)
  ·
    refine ⟨24633432055653281359987901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262756608593635001173204277 24633432055653281359987901)
    ·
      refine ⟨9237537020869980509995463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24633432055653281359987901 9237537020869980509995463)
      ·
        refine ⟨13856305531304970764993195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237537020869980509995463 13856305531304970764993195)
        ·
          refine ⟨20784458296957456147489793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856305531304970764993195 20784458296957456147489793)
          ·
            refine ⟨15588343722718092110617345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20784458296957456147489793 15588343722718092110617345)
            ·
              refine ⟨11691257792038569082963009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15588343722718092110617345 11691257792038569082963009)
              ·
                refine ⟨8768443344028926812222257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11691257792038569082963009 8768443344028926812222257)
                ·
                  refine ⟨6576332508021695109166693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768443344028926812222257 6576332508021695109166693)
                  ·
                    refine ⟨1233062345254067832968755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576332508021695109166693 1233062345254067832968755)
                    ·
                      rfl

theorem cell23_7204141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7204141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204141 prefixEnd_7204141 := by exact prefixLift 7204141
  have htrace : WordTrace (prefixWord ++ tailWord_7204141) baseStart_7204141 baseEnd_7204141 := by
    simpa [prefixWord, tailWord_7204141, baseEnd_7204141] using wordTrace_append hprefix tailTrace_7204141
  have hstable : (prefixWord ++ tailWord_7204141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204141).length < 2 ^ (prefixWord ++ tailWord_7204141).sum := by decide
  have hdescent : baseEnd_7204141 < baseStart_7204141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204148 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7204148 : Nat := 118140960795 + 7204148 * 2 ^ 59
def prefixEnd_7204148 : Nat := 4983230072969 + 3 ^ 40 * 7204148 * 2
def baseEnd_7204148 : Nat := 3699190630126784971518733

theorem tailTrace_7204148 : CollatzResearch.WordTrace tailWord_7204148 prefixEnd_7204148 3699190630126784971518733 := by
  unfold tailWord_7204148
  simp only [CollatzResearch.WordTrace]
  refine ⟨131378431952304820684354549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175171242603073094245806065 131378431952304820684354549)
  ·
    refine ⟨12316727995528576939158239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131378431952304820684354549 12316727995528576939158239)
    ·
      refine ⟨18475091993292865408737359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316727995528576939158239 18475091993292865408737359)
      ·
        refine ⟨27712637989939298113106039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475091993292865408737359 27712637989939298113106039)
        ·
          refine ⟨41568956984908947169659059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27712637989939298113106039 41568956984908947169659059)
          ·
            refine ⟨62353435477363420754488589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41568956984908947169659059 62353435477363420754488589)
            ·
              refine ⟨23382538304011282782933221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62353435477363420754488589 23382538304011282782933221)
              ·
                refine ⟨4384225932002115521799979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23382538304011282782933221 4384225932002115521799979)
                ·
                  refine ⟨6576338898003173282699969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384225932002115521799979 6576338898003173282699969)
                  ·
                    refine ⟨4932254173502379962024977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6576338898003173282699969 4932254173502379962024977)
                    ·
                      refine ⟨3699190630126784971518733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932254173502379962024977 3699190630126784971518733)
                      ·
                        rfl

theorem cell23_7204148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7204148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204148 prefixEnd_7204148 := by exact prefixLift 7204148
  have htrace : WordTrace (prefixWord ++ tailWord_7204148) baseStart_7204148 baseEnd_7204148 := by
    simpa [prefixWord, tailWord_7204148, baseEnd_7204148] using wordTrace_append hprefix tailTrace_7204148
  have hstable : (prefixWord ++ tailWord_7204148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204148).length < 2 ^ (prefixWord ++ tailWord_7204148).sum := by decide
  have hdescent : baseEnd_7204148 < baseStart_7204148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204164 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7204164 : Nat := 118140960795 + 7204164 * 2 ^ 59
def prefixEnd_7204164 : Nat := 4983230072969 + 3 ^ 40 * 7204164 * 2
def baseEnd_7204164 : Nat := 3699198845817256908918659

theorem tailTrace_7204164 : CollatzResearch.WordTrace tailWord_7204164 prefixEnd_7204164 3699198845817256908918659 := by
  unfold tailWord_7204164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131378723736275838050645773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175171631648367784067527697 131378723736275838050645773)
  ·
    refine ⟨49267021401103439268992165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131378723736275838050645773 49267021401103439268992165)
    ·
      refine ⟨9237566512706894862936031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49267021401103439268992165 9237566512706894862936031)
      ·
        refine ⟨13856349769060342294404047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237566512706894862936031 13856349769060342294404047)
        ·
          refine ⟨20784524653590513441606071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856349769060342294404047 20784524653590513441606071)
          ·
            refine ⟨31176786980385770162409107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784524653590513441606071 31176786980385770162409107)
            ·
              refine ⟨46765180470578655243613661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31176786980385770162409107 46765180470578655243613661)
              ·
                refine ⟨17536942676466995716355123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46765180470578655243613661 17536942676466995716355123)
                ·
                  refine ⟨26305414014700493574532685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17536942676466995716355123 26305414014700493574532685)
                  ·
                    refine ⟨9864530255512685090449757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26305414014700493574532685 9864530255512685090449757)
                    ·
                      refine ⟨3699198845817256908918659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9864530255512685090449757 3699198845817256908918659)
                      ·
                        rfl

theorem cell23_7204164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7204164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204164 prefixEnd_7204164 := by exact prefixLift 7204164
  have htrace : WordTrace (prefixWord ++ tailWord_7204164) baseStart_7204164 baseEnd_7204164 := by
    simpa [prefixWord, tailWord_7204164, baseEnd_7204164] using wordTrace_append hprefix tailTrace_7204164
  have hstable : (prefixWord ++ tailWord_7204164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204164).length < 2 ^ (prefixWord ++ tailWord_7204164).sum := by decide
  have hdescent : baseEnd_7204164 < baseStart_7204164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204174 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_7204174 : Nat := 118140960795 + 7204174 * 2 ^ 59
def prefixEnd_7204174 : Nat := 4983230072969 + 3 ^ 40 * 7204174 * 2
def baseEnd_7204174 : Nat := 3699203980623801869793613

theorem tailTrace_7204174 : CollatzResearch.WordTrace tailWord_7204174 prefixEnd_7204174 3699203980623801869793613 := by
  unfold tailWord_7204174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32844726525314430976144447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175171874801676965206103717 32844726525314430976144447)
  ·
    refine ⟨49267089787971646464216671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32844726525314430976144447 49267089787971646464216671)
    ·
      refine ⟨73900634681957469696325007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49267089787971646464216671 73900634681957469696325007)
      ·
        refine ⟨110850952022936204544487511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73900634681957469696325007 110850952022936204544487511)
        ·
          refine ⟨166276428034404306816731267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110850952022936204544487511 166276428034404306816731267)
          ·
            refine ⟨249414642051606460225096901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166276428034404306816731267 249414642051606460225096901)
            ·
              refine ⟨46765245384676211292205669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249414642051606460225096901 46765245384676211292205669)
              ·
                refine ⟨8768483509626789617288563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46765245384676211292205669 8768483509626789617288563)
                ·
                  refine ⟨13152725264440184425932845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768483509626789617288563 13152725264440184425932845)
                  ·
                    refine ⟨4932271974165069159724817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13152725264440184425932845 4932271974165069159724817)
                    ·
                      refine ⟨3699203980623801869793613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932271974165069159724817 3699203980623801869793613)
                      ·
                        rfl

theorem cell23_7204174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_7204174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204174 prefixEnd_7204174 := by exact prefixLift 7204174
  have htrace : WordTrace (prefixWord ++ tailWord_7204174) baseStart_7204174 baseEnd_7204174 := by
    simpa [prefixWord, tailWord_7204174, baseEnd_7204174] using wordTrace_append hprefix tailTrace_7204174
  have hstable : (prefixWord ++ tailWord_7204174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204174).length < 2 ^ (prefixWord ++ tailWord_7204174).sum := by decide
  have hdescent : baseEnd_7204174 < baseStart_7204174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204180 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_7204180 : Nat := 118140960795 + 7204180 * 2 ^ 59
def prefixEnd_7204180 : Nat := 4983230072969 + 3 ^ 40 * 7204180 * 2
def baseEnd_7204180 : Nat := 1233069020502576282106195

theorem tailTrace_7204180 : CollatzResearch.WordTrace tailWord_7204180 prefixEnd_7204180 1233069020502576282106195 := by
  unfold tailWord_7204180
  simp only [CollatzResearch.WordTrace]
  refine ⟨131379015520246855416936997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175172020693662473889249329 131379015520246855416936997)
  ·
    refine ⟨24633565410046285390675687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131379015520246855416936997 24633565410046285390675687)
    ·
      refine ⟨36950348115069428086013531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24633565410046285390675687 36950348115069428086013531)
      ·
        refine ⟨55425522172604142129020297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36950348115069428086013531 55425522172604142129020297)
        ·
          refine ⟨41569141629453106596765223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55425522172604142129020297 41569141629453106596765223)
          ·
            refine ⟨62353712444179659895147835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41569141629453106596765223 62353712444179659895147835)
            ·
              refine ⟨93530568666269489842721753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62353712444179659895147835 93530568666269489842721753)
              ·
                refine ⟨70147926499702117382041315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93530568666269489842721753 70147926499702117382041315)
                ·
                  refine ⟨105221889749553176073061973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70147926499702117382041315 105221889749553176073061973)
                  ·
                    refine ⟨1233069020502576282106195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105221889749553176073061973 1233069020502576282106195)
                    ·
                      rfl

theorem cell23_7204180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_7204180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204180 prefixEnd_7204180 := by exact prefixLift 7204180
  have htrace : WordTrace (prefixWord ++ tailWord_7204180) baseStart_7204180 baseEnd_7204180 := by
    simpa [prefixWord, tailWord_7204180, baseEnd_7204180] using wordTrace_append hprefix tailTrace_7204180
  have hstable : (prefixWord ++ tailWord_7204180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204180).length < 2 ^ (prefixWord ++ tailWord_7204180).sum := by decide
  have hdescent : baseEnd_7204180 < baseStart_7204180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204182 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7204182 : Nat := 118140960795 + 7204182 * 2 ^ 59
def prefixEnd_7204182 : Nat := 4983230072969 + 3 ^ 40 * 7204182 * 2
def baseEnd_7204182 : Nat := 3699208088469037838493577

theorem tailTrace_7204182 : CollatzResearch.WordTrace tailWord_7204182 prefixEnd_7204182 3699208088469037838493577 := by
  unfold tailWord_7204182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422381499155404073465425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175172069324324310116964533 16422381499155404073465425)
  ·
    refine ⟨12316786124366553055099069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16422381499155404073465425 12316786124366553055099069)
    ·
      refine ⟨4618794796637457395662151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12316786124366553055099069 4618794796637457395662151)
      ·
        refine ⟨6928192194956186093493227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618794796637457395662151 6928192194956186093493227)
        ·
          refine ⟨10392288292434279140239841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928192194956186093493227 10392288292434279140239841)
          ·
            refine ⟨7794216219325709355179881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10392288292434279140239841 7794216219325709355179881)
            ·
              refine ⟨5845662164494282016384911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7794216219325709355179881 5845662164494282016384911)
              ·
                refine ⟨8768493246741423024577367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845662164494282016384911 8768493246741423024577367)
                ·
                  refine ⟨13152739870112134536866051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768493246741423024577367 13152739870112134536866051)
                  ·
                    refine ⟨19729109805168201805299077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13152739870112134536866051 19729109805168201805299077)
                    ·
                      refine ⟨3699208088469037838493577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19729109805168201805299077 3699208088469037838493577)
                      ·
                        rfl

theorem cell23_7204182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7204182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204182 prefixEnd_7204182 := by exact prefixLift 7204182
  have htrace : WordTrace (prefixWord ++ tailWord_7204182) baseStart_7204182 baseEnd_7204182 := by
    simpa [prefixWord, tailWord_7204182, baseEnd_7204182] using wordTrace_append hprefix tailTrace_7204182
  have hstable : (prefixWord ++ tailWord_7204182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204182).length < 2 ^ (prefixWord ++ tailWord_7204182).sum := by decide
  have hdescent : baseEnd_7204182 < baseStart_7204182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204247 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_7204247 : Nat := 118140960795 + 7204247 * 2 ^ 59
def prefixEnd_7204247 : Nat := 4983230072969 + 3 ^ 40 * 7204247 * 2
def baseEnd_7204247 : Nat := 3699241464711580084180777

theorem tailTrace_7204247 : CollatzResearch.WordTrace tailWord_7204247 prefixEnd_7204247 3699241464711580084180777 := by
  unfold tailWord_7204247
  simp only [CollatzResearch.WordTrace]
  refine ⟨262760474731250981276562995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175173649820833987517708663 262760474731250981276562995)
  ·
    refine ⟨394140712096876471914844493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262760474731250981276562995 394140712096876471914844493)
    ·
      refine ⟨147802767036328676968066685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394140712096876471914844493 147802767036328676968066685)
      ·
        refine ⟨55426037638623253863025007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147802767036328676968066685 55426037638623253863025007)
        ·
          refine ⟨83139056457934880794537511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55426037638623253863025007 83139056457934880794537511)
          ·
            refine ⟨124708584686902321191806267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83139056457934880794537511 124708584686902321191806267)
            ·
              refine ⟨187062877030353481787709401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124708584686902321191806267 187062877030353481787709401)
              ·
                refine ⟨140297157772765111340782051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187062877030353481787709401 140297157772765111340782051)
                ·
                  refine ⟨210445736659147667011173077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140297157772765111340782051 210445736659147667011173077)
                  ·
                    refine ⟨4932321952948773445574369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 210445736659147667011173077 4932321952948773445574369)
                    ·
                      refine ⟨3699241464711580084180777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932321952948773445574369 3699241464711580084180777)
                      ·
                        rfl

theorem cell23_7204247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_7204247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204247 prefixEnd_7204247 := by exact prefixLift 7204247
  have htrace : WordTrace (prefixWord ++ tailWord_7204247) baseStart_7204247 baseEnd_7204247 := by
    simpa [prefixWord, tailWord_7204247, baseEnd_7204247] using wordTrace_append hprefix tailTrace_7204247
  have hstable : (prefixWord ++ tailWord_7204247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204247).length < 2 ^ (prefixWord ++ tailWord_7204247).sum := by decide
  have hdescent : baseEnd_7204247 < baseStart_7204247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204287 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 3, 4]
def baseStart_7204287 : Nat := 118140960795 + 7204287 * 2 ^ 59
def prefixEnd_7204287 : Nat := 4983230072969 + 3 ^ 40 * 7204287 * 2
def baseEnd_7204287 : Nat := 1233087334645919975893531

theorem tailTrace_7204287 : CollatzResearch.WordTrace tailWord_7204287 prefixEnd_7204287 1233087334645919975893531 := by
  unfold tailWord_7204287
  simp only [CollatzResearch.WordTrace]
  refine ⟨262761933651106068108019115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175174622434070712072012743 262761933651106068108019115)
  ·
    refine ⟨394142900476659102162028673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262761933651106068108019115 394142900476659102162028673)
    ·
      refine ⟨295607175357494326621521505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394142900476659102162028673 295607175357494326621521505)
      ·
        refine ⟨221705381518120744966141129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295607175357494326621521505 221705381518120744966141129)
        ·
          refine ⟨166279036138590558724605847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221705381518120744966141129 166279036138590558724605847)
          ·
            refine ⟨249418554207885838086908771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166279036138590558724605847 249418554207885838086908771)
            ·
              refine ⟨374127831311828757130363157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249418554207885838086908771 374127831311828757130363157)
              ·
                refine ⟨17537242092741972990485773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374127831311828757130363157 17537242092741972990485773)
                ·
                  refine ⟨6576465784778239871432165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17537242092741972990485773 6576465784778239871432165)
                  ·
                    refine ⟨1233087334645919975893531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576465784778239871432165 1233087334645919975893531)
                    ·
                      rfl

theorem cell23_7204287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_7204287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204287 prefixEnd_7204287 := by exact prefixLift 7204287
  have htrace : WordTrace (prefixWord ++ tailWord_7204287) baseStart_7204287 baseEnd_7204287 := by
    simpa [prefixWord, tailWord_7204287, baseEnd_7204287] using wordTrace_append hprefix tailTrace_7204287
  have hstable : (prefixWord ++ tailWord_7204287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204287).length < 2 ^ (prefixWord ++ tailWord_7204287).sum := by decide
  have hdescent : baseEnd_7204287 < baseStart_7204287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204314 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_7204314 : Nat := 118140960795 + 7204314 * 2 ^ 59
def prefixEnd_7204314 : Nat := 4983230072969 + 3 ^ 40 * 7204314 * 2
def baseEnd_7204314 : Nat := 3699275867915431322042969

theorem tailTrace_7204314 : CollatzResearch.WordTrace tailWord_7204314 prefixEnd_7204314 3699275867915431322042969 := by
  unfold tailWord_7204314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65690729605502062929812999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175175278948005501146167997 65690729605502062929812999)
  ·
    refine ⟨98536094408253094394719499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65690729605502062929812999 98536094408253094394719499)
    ·
      refine ⟨147804141612379641592079249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98536094408253094394719499 147804141612379641592079249)
      ·
        refine ⟨110853106209284731194059437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147804141612379641592079249 110853106209284731194059437)
        ·
          refine ⟨41569914828481774197772289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110853106209284731194059437 41569914828481774197772289)
          ·
            refine ⟨31177436121361330648329217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41569914828481774197772289 31177436121361330648329217)
            ·
              refine ⟨23383077091020997986246913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31177436121361330648329217 23383077091020997986246913)
              ·
                refine ⟨17537307818265748489685185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23383077091020997986246913 17537307818265748489685185)
                ·
                  refine ⟨13152980863699311367263889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17537307818265748489685185 13152980863699311367263889)
                  ·
                    refine ⟨9864735647774483525447917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13152980863699311367263889 9864735647774483525447917)
                    ·
                      refine ⟨3699275867915431322042969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9864735647774483525447917 3699275867915431322042969)
                      ·
                        rfl

theorem cell23_7204314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_7204314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204314 prefixEnd_7204314 := by exact prefixLift 7204314
  have htrace : WordTrace (prefixWord ++ tailWord_7204314) baseStart_7204314 baseEnd_7204314 := by
    simpa [prefixWord, tailWord_7204314, baseEnd_7204314] using wordTrace_append hprefix tailTrace_7204314
  have hstable : (prefixWord ++ tailWord_7204314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204314).length < 2 ^ (prefixWord ++ tailWord_7204314).sum := by decide
  have hdescent : baseEnd_7204314 < baseStart_7204314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204321 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 1, 4]
def baseStart_7204321 : Nat := 118140960795 + 7204321 * 2 ^ 59
def prefixEnd_7204321 : Nat := 4983230072969 + 3 ^ 40 * 7204321 * 2
def baseEnd_7204321 : Nat := 1233093154093337598218479

theorem tailTrace_7204321 : CollatzResearch.WordTrace tailWord_7204321 prefixEnd_7204321 1233093154093337598218479 := by
  unfold tailWord_7204321
  simp only [CollatzResearch.WordTrace]
  refine ⟨262763173732982891914756817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175175449155321927943171211 262763173732982891914756817)
  ·
    refine ⟨197072380299737168936067613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262763173732982891914756817 197072380299737168936067613)
    ·
      refine ⟨73902142612401438351025355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197072380299737168936067613 73902142612401438351025355)
      ·
        refine ⟨110853213918602157526538033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73902142612401438351025355 110853213918602157526538033)
        ·
          refine ⟨83139910438951618144903525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110853213918602157526538033 83139910438951618144903525)
          ·
            refine ⟨15588733207303428402169411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83139910438951618144903525 15588733207303428402169411)
            ·
              refine ⟨23383099810955142603254117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15588733207303428402169411 23383099810955142603254117)
              ·
                refine ⟨4384331214554089238110147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23383099810955142603254117 4384331214554089238110147)
                ·
                  refine ⟨6576496821831133857165221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384331214554089238110147 6576496821831133857165221)
                  ·
                    refine ⟨1233093154093337598218479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576496821831133857165221 1233093154093337598218479)
                    ·
                      rfl

theorem cell23_7204321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_7204321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204321 prefixEnd_7204321 := by exact prefixLift 7204321
  have htrace : WordTrace (prefixWord ++ tailWord_7204321) baseStart_7204321 baseEnd_7204321 := by
    simpa [prefixWord, tailWord_7204321, baseEnd_7204321] using wordTrace_append hprefix tailTrace_7204321
  have hstable : (prefixWord ++ tailWord_7204321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204321).length < 2 ^ (prefixWord ++ tailWord_7204321).sum := by decide
  have hdescent : baseEnd_7204321 < baseStart_7204321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204344 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_7204344 : Nat := 118140960795 + 7204344 * 2 ^ 59
def prefixEnd_7204344 : Nat := 4983230072969 + 3 ^ 40 * 7204344 * 2
def baseEnd_7204344 : Nat := 3699291272335066204667831

theorem tailTrace_7204344 : CollatzResearch.WordTrace tailWord_7204344 prefixEnd_7204344 3699291272335066204667831 := by
  unfold tailWord_7204344
  simp only [CollatzResearch.WordTrace]
  refine ⟨131382006305949783421422043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175176008407933044561896057 131382006305949783421422043)
  ·
    refine ⟨197073009458924675132133065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131382006305949783421422043 197073009458924675132133065)
    ·
      refine ⟨147804757094193506349099799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197073009458924675132133065 147804757094193506349099799)
      ·
        refine ⟨221707135641290259523649699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147804757094193506349099799 221707135641290259523649699)
        ·
          refine ⟨332560703461935389285474549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221707135641290259523649699 332560703461935389285474549)
          ·
            refine ⟨31177565949556442745513239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332560703461935389285474549 31177565949556442745513239)
            ·
              refine ⟨46766348924334664118269859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31177565949556442745513239 46766348924334664118269859)
              ·
                refine ⟨70149523386501996177404789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46766348924334664118269859 70149523386501996177404789)
                ·
                  refine ⟨6576517817484562141631699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70149523386501996177404789 6576517817484562141631699)
                  ·
                    refine ⟨9864776726226843212447549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6576517817484562141631699 9864776726226843212447549)
                    ·
                      refine ⟨3699291272335066204667831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9864776726226843212447549 3699291272335066204667831)
                      ·
                        rfl

theorem cell23_7204344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_7204344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204344 prefixEnd_7204344 := by exact prefixLift 7204344
  have htrace : WordTrace (prefixWord ++ tailWord_7204344) baseStart_7204344 baseEnd_7204344 := by
    simpa [prefixWord, tailWord_7204344, baseEnd_7204344] using wordTrace_append hprefix tailTrace_7204344
  have hstable : (prefixWord ++ tailWord_7204344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204344).length < 2 ^ (prefixWord ++ tailWord_7204344).sum := by decide
  have hdescent : baseEnd_7204344 < baseStart_7204344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204407 : List Nat := [1, 1, 3, 1, 2, 5, 1, 9]
def baseStart_7204407 : Nat := 118140960795 + 7204407 * 2 ^ 59
def prefixEnd_7204407 : Nat := 4983230072969 + 3 ^ 40 * 7204407 * 2
def baseEnd_7204407 : Nat := 137011985985788868821483

theorem tailTrace_7204407 : CollatzResearch.WordTrace tailWord_7204407 prefixEnd_7204407 137011985985788868821483 := by
  unfold tailWord_7204407
  simp only [CollatzResearch.WordTrace]
  refine ⟨262766310410671328602387475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175177540273780885734924983 262766310410671328602387475)
  ·
    refine ⟨394149465616006992903581213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262766310410671328602387475 394149465616006992903581213)
    ·
      refine ⟨147806049606002622338842955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394149465616006992903581213 147806049606002622338842955)
      ·
        refine ⟨221709074409003933508264433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147806049606002622338842955 221709074409003933508264433)
        ·
          refine ⟨166281805806752950131198325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221709074409003933508264433 166281805806752950131198325)
          ·
            refine ⟨15588919294383089074799843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166281805806752950131198325 15588919294383089074799843)
            ·
              refine ⟨23383378941574633612199765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15588919294383089074799843 23383378941574633612199765)
              ·
                refine ⟨137011985985788868821483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23383378941574633612199765 137011985985788868821483)
                ·
                  rfl

theorem cell23_7204407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 9].length) (baseStart_7204407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204407 prefixEnd_7204407 := by exact prefixLift 7204407
  have htrace : WordTrace (prefixWord ++ tailWord_7204407) baseStart_7204407 baseEnd_7204407 := by
    simpa [prefixWord, tailWord_7204407, baseEnd_7204407] using wordTrace_append hprefix tailTrace_7204407
  have hstable : (prefixWord ++ tailWord_7204407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204407).length < 2 ^ (prefixWord ++ tailWord_7204407).sum := by decide
  have hdescent : baseEnd_7204407 < baseStart_7204407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204412 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_7204412 : Nat := 118140960795 + 7204412 * 2 ^ 59
def prefixEnd_7204412 : Nat := 4983230072969 + 3 ^ 40 * 7204412 * 2
def baseEnd_7204412 : Nat := 3699326189019571938617519

theorem tailTrace_7204412 : CollatzResearch.WordTrace tailWord_7204412 prefixEnd_7204412 3699326189019571938617519 := by
  unfold tailWord_7204412
  simp only [CollatzResearch.WordTrace]
  refine ⟨131383246387826607228159745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175177661850435476304212993 131383246387826607228159745)
  ·
    refine ⟨98537434790869955421119809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131383246387826607228159745 98537434790869955421119809)
    ·
      refine ⟨73903076093152466565839857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98537434790869955421119809 73903076093152466565839857)
      ·
        refine ⟨55427307069864349924379893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73903076093152466565839857 55427307069864349924379893)
        ·
          refine ⟨5196310037799782805410615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55427307069864349924379893 5196310037799782805410615)
          ·
            refine ⟨7794465056699674208115923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196310037799782805410615 7794465056699674208115923)
            ·
              refine ⟨11691697585049511312173885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794465056699674208115923 11691697585049511312173885)
              ·
                refine ⟨4384386594393566742065207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11691697585049511312173885 4384386594393566742065207)
                ·
                  refine ⟨6576579891590350113097811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384386594393566742065207 6576579891590350113097811)
                  ·
                    refine ⟨9864869837385525169646717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6576579891590350113097811 9864869837385525169646717)
                    ·
                      refine ⟨3699326189019571938617519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9864869837385525169646717 3699326189019571938617519)
                      ·
                        rfl

theorem cell23_7204412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_7204412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204412 prefixEnd_7204412 := by exact prefixLift 7204412
  have htrace : WordTrace (prefixWord ++ tailWord_7204412) baseStart_7204412 baseEnd_7204412 := by
    simpa [prefixWord, tailWord_7204412, baseEnd_7204412] using wordTrace_append hprefix tailTrace_7204412
  have hstable : (prefixWord ++ tailWord_7204412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204412).length < 2 ^ (prefixWord ++ tailWord_7204412).sum := by decide
  have hdescent : baseEnd_7204412 < baseStart_7204412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204437 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_7204437 : Nat := 118140960795 + 7204437 * 2 ^ 59
def prefixEnd_7204437 : Nat := 4983230072969 + 3 ^ 40 * 7204437 * 2
def baseEnd_7204437 : Nat := 1233113008678644780268301

theorem tailTrace_7204437 : CollatzResearch.WordTrace tailWord_7204437 prefixEnd_7204437 1233113008678644780268301 := by
  unfold tailWord_7204437
  simp only [CollatzResearch.WordTrace]
  refine ⟨262767404600562643725979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175178269733708429150653043 262767404600562643725979565)
  ·
    refine ⟨98537776725210991397242337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262767404600562643725979565 98537776725210991397242337)
    ·
      refine ⟨73903332543908243547931753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98537776725210991397242337 73903332543908243547931753)
      ·
        refine ⟨55427499407931182660948815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73903332543908243547931753 55427499407931182660948815)
        ·
          refine ⟨83141249111896773991423223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55427499407931182660948815 83141249111896773991423223)
          ·
            refine ⟨124711873667845160987134835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83141249111896773991423223 124711873667845160987134835)
            ·
              refine ⟨187067810501767741480702253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124711873667845160987134835 187067810501767741480702253)
              ·
                refine ⟨70150428938162903055263345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187067810501767741480702253 70150428938162903055263345)
                ·
                  refine ⟨52612821703622177291447509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70150428938162903055263345 52612821703622177291447509)
                  ·
                    refine ⟨1233113008678644780268301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52612821703622177291447509 1233113008678644780268301)
                    ·
                      rfl

theorem cell23_7204437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_7204437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204437 prefixEnd_7204437 := by exact prefixLift 7204437
  have htrace : WordTrace (prefixWord ++ tailWord_7204437) baseStart_7204437 baseEnd_7204437 := by
    simpa [prefixWord, tailWord_7204437, baseEnd_7204437] using wordTrace_append hprefix tailTrace_7204437
  have hstable : (prefixWord ++ tailWord_7204437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204437).length < 2 ^ (prefixWord ++ tailWord_7204437).sum := by decide
  have hdescent : baseEnd_7204437 < baseStart_7204437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204445 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7204445 : Nat := 118140960795 + 7204445 * 2 ^ 59
def prefixEnd_7204445 : Nat := 4983230072969 + 3 ^ 40 * 7204445 * 2
def baseEnd_7204445 : Nat := 1233114377960390103168289

theorem tailTrace_7204445 : CollatzResearch.WordTrace tailWord_7204445 prefixEnd_7204445 1233114377960390103168289 := by
  unfold tailWord_7204445
  simp only [CollatzResearch.WordTrace]
  refine ⟨262767696384533661092270789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175178464256355774061513859 262767696384533661092270789)
  ·
    refine ⟨49268943072100061454800773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262767696384533661092270789 49268943072100061454800773)
    ·
      refine ⟨9237926826018761522775145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49268943072100061454800773 9237926826018761522775145)
      ·
        refine ⟨6928445119514071142081359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9237926826018761522775145 6928445119514071142081359)
        ·
          refine ⟨10392667679271106713122039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928445119514071142081359 10392667679271106713122039)
          ·
            refine ⟨15589001518906660069683059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10392667679271106713122039 15589001518906660069683059)
            ·
              refine ⟨23383502278359990104524589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589001518906660069683059 23383502278359990104524589)
              ·
                refine ⟨8768813354384996289196721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23383502278359990104524589 8768813354384996289196721)
                ·
                  refine ⟨6576610015788747216897541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768813354384996289196721 6576610015788747216897541)
                  ·
                    refine ⟨1233114377960390103168289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576610015788747216897541 1233114377960390103168289)
                    ·
                      rfl

theorem cell23_7204445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7204445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204445 prefixEnd_7204445 := by exact prefixLift 7204445
  have htrace : WordTrace (prefixWord ++ tailWord_7204445) baseStart_7204445 baseEnd_7204445 := by
    simpa [prefixWord, tailWord_7204445, baseEnd_7204445] using wordTrace_append hprefix tailTrace_7204445
  have hstable : (prefixWord ++ tailWord_7204445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204445).length < 2 ^ (prefixWord ++ tailWord_7204445).sum := by decide
  have hdescent : baseEnd_7204445 < baseStart_7204445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204504 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7204504 : Nat := 118140960795 + 7204504 * 2 ^ 59
def prefixEnd_7204504 : Nat := 4983230072969 + 3 ^ 40 * 7204504 * 2
def baseEnd_7204504 : Nat := 3699373429239785578667095

theorem tailTrace_7204504 : CollatzResearch.WordTrace tailWord_7204504 prefixEnd_7204504 3699373429239785578667095 := by
  unfold tailWord_7204504
  simp only [CollatzResearch.WordTrace]
  refine ⟨131384924145659957084334283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175179898860879942779112377 131384924145659957084334283)
  ·
    refine ⟨197077386218489935626501425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131384924145659957084334283 197077386218489935626501425)
    ·
      refine ⟨147808039663867451719876069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197077386218489935626501425 147808039663867451719876069)
      ·
        refine ⟨27714007436975147197476763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147808039663867451719876069 27714007436975147197476763)
        ·
          refine ⟨41571011155462720796215145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27714007436975147197476763 41571011155462720796215145)
          ·
            refine ⟨31178258366597040597161359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41571011155462720796215145 31178258366597040597161359)
            ·
              refine ⟨46767387549895560895742039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31178258366597040597161359 46767387549895560895742039)
              ·
                refine ⟨70151081324843341343613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46767387549895560895742039 70151081324843341343613059)
                ·
                  refine ⟨105226621987265012015419589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70151081324843341343613059 105226621987265012015419589)
                  ·
                    refine ⟨19729991622612189752891173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105226621987265012015419589 19729991622612189752891173)
                    ·
                      refine ⟨3699373429239785578667095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19729991622612189752891173 3699373429239785578667095)
                      ·
                        rfl

theorem cell23_7204504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7204504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204504 prefixEnd_7204504 := by exact prefixLift 7204504
  have htrace : WordTrace (prefixWord ++ tailWord_7204504) baseStart_7204504 baseEnd_7204504 := by
    simpa [prefixWord, tailWord_7204504, baseEnd_7204504] using wordTrace_append hprefix tailTrace_7204504
  have hstable : (prefixWord ++ tailWord_7204504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204504).length < 2 ^ (prefixWord ++ tailWord_7204504).sum := by decide
  have hdescent : baseEnd_7204504 < baseStart_7204504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204531 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 5]
def baseStart_7204531 : Nat := 118140960795 + 7204531 * 2 ^ 59
def prefixEnd_7204531 : Nat := 4983230072969 + 3 ^ 40 * 7204531 * 2
def baseEnd_7204531 : Nat := 411043032579717441447719

theorem tailTrace_7204531 : CollatzResearch.WordTrace tailWord_7204531 prefixEnd_7204531 411043032579717441447719 := by
  unfold tailWord_7204531
  simp only [CollatzResearch.WordTrace]
  refine ⟨262770833062222097779901447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175180555374814731853267631 262770833062222097779901447)
  ·
    refine ⟨394156249593333146669852171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262770833062222097779901447 394156249593333146669852171)
    ·
      refine ⟨591234374389999720004778257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394156249593333146669852171 591234374389999720004778257)
      ·
        refine ⟨443425780792499790003583693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591234374389999720004778257 443425780792499790003583693)
        ·
          refine ⟨166284667797187421251343885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443425780792499790003583693 166284667797187421251343885)
          ·
            refine ⟨62356750423945282969253957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166284667797187421251343885 62356750423945282969253957)
            ·
              refine ⟨11691890704489740556735117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62356750423945282969253957 11691890704489740556735117)
              ·
                refine ⟨4384459014183652708775669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11691890704489740556735117 4384459014183652708775669)
                ·
                  refine ⟨411043032579717441447719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4384459014183652708775669 411043032579717441447719)
                  ·
                    rfl

theorem cell23_7204531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 5].length) (baseStart_7204531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204531 prefixEnd_7204531 := by exact prefixLift 7204531
  have htrace : WordTrace (prefixWord ++ tailWord_7204531) baseStart_7204531 baseEnd_7204531 := by
    simpa [prefixWord, tailWord_7204531, baseEnd_7204531] using wordTrace_append hprefix tailTrace_7204531
  have hstable : (prefixWord ++ tailWord_7204531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204531).length < 2 ^ (prefixWord ++ tailWord_7204531).sum := by decide
  have hdescent : baseEnd_7204531 < baseStart_7204531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204542 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_7204542 : Nat := 118140960795 + 7204542 * 2 ^ 59
def prefixEnd_7204542 : Nat := 4983230072969 + 3 ^ 40 * 7204542 * 2
def baseEnd_7204542 : Nat := 3699392941504656429991921

theorem tailTrace_7204542 : CollatzResearch.WordTrace tailWord_7204542 prefixEnd_7204542 3699392941504656429991921 := by
  unfold tailWord_7204542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846404283147780832318985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175180822843454831105701253 32846404283147780832318985)
  ·
    refine ⟨24634803212360835624239239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32846404283147780832318985 24634803212360835624239239)
    ·
      refine ⟨36952204818541253436358859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24634803212360835624239239 36952204818541253436358859)
      ·
        refine ⟨55428307227811880154538289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36952204818541253436358859 55428307227811880154538289)
        ·
          refine ⟨41571230420858910115903717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55428307227811880154538289 41571230420858910115903717)
          ·
            refine ⟨7794605703911045646731947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41571230420858910115903717 7794605703911045646731947)
            ·
              refine ⟨11691908555866568470097921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794605703911045646731947 11691908555866568470097921)
              ·
                refine ⟨8768931416899926352573441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11691908555866568470097921 8768931416899926352573441)
                ·
                  refine ⟨6576698562674944764430081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768931416899926352573441 6576698562674944764430081)
                  ·
                    refine ⟨4932523922006208573322561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6576698562674944764430081 4932523922006208573322561)
                    ·
                      refine ⟨3699392941504656429991921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932523922006208573322561 3699392941504656429991921)
                      ·
                        rfl

theorem cell23_7204542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_7204542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204542 prefixEnd_7204542 := by exact prefixLift 7204542
  have htrace : WordTrace (prefixWord ++ tailWord_7204542) baseStart_7204542 baseEnd_7204542 := by
    simpa [prefixWord, tailWord_7204542, baseEnd_7204542] using wordTrace_append hprefix tailTrace_7204542
  have hstable : (prefixWord ++ tailWord_7204542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204542).length < 2 ^ (prefixWord ++ tailWord_7204542).sum := by decide
  have hdescent : baseEnd_7204542 < baseStart_7204542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204544 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_7204544 : Nat := 118140960795 + 7204544 * 2 ^ 59
def prefixEnd_7204544 : Nat := 4983230072969 + 3 ^ 40 * 7204544 * 2
def baseEnd_7204544 : Nat := 1233131322821988474055637

theorem tailTrace_7204544 : CollatzResearch.WordTrace tailWord_7204544 prefixEnd_7204544 1233131322821988474055637 := by
  unfold tailWord_7204544
  simp only [CollatzResearch.WordTrace]
  refine ⟨131385653605587500500062343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175180871474116667333416457 131385653605587500500062343)
  ·
    refine ⟨197078480408381250750093515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131385653605587500500062343 197078480408381250750093515)
    ·
      refine ⟨295617720612571876125140273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197078480408381250750093515 295617720612571876125140273)
      ·
        refine ⟨221713290459428907093855205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295617720612571876125140273 221713290459428907093855205)
        ·
          refine ⟨41571241961142920080097851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221713290459428907093855205 41571241961142920080097851)
          ·
            refine ⟨62356862941714380120146777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41571241961142920080097851 62356862941714380120146777)
            ·
              refine ⟨46767647206285785090110083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62356862941714380120146777 46767647206285785090110083)
              ·
                refine ⟨70151470809428677635165125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46767647206285785090110083 70151470809428677635165125)
                ·
                  refine ⟨13153400776767877056593461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70151470809428677635165125 13153400776767877056593461)
                  ·
                    refine ⟨1233131322821988474055637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13153400776767877056593461 1233131322821988474055637)
                    ·
                      rfl

theorem cell23_7204544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_7204544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204544 prefixEnd_7204544 := by exact prefixLift 7204544
  have htrace : WordTrace (prefixWord ++ tailWord_7204544) baseStart_7204544 baseEnd_7204544 := by
    simpa [prefixWord, tailWord_7204544, baseEnd_7204544] using wordTrace_append hprefix tailTrace_7204544
  have hstable : (prefixWord ++ tailWord_7204544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204544).length < 2 ^ (prefixWord ++ tailWord_7204544).sum := by decide
  have hdescent : baseEnd_7204544 < baseStart_7204544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204581 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7204581 : Nat := 118140960795 + 7204581 * 2 ^ 59
def prefixEnd_7204581 : Nat := 4983230072969 + 3 ^ 40 * 7204581 * 2
def baseEnd_7204581 : Nat := 3699412967250181777404241

theorem tailTrace_7204581 : CollatzResearch.WordTrace tailWord_7204581 prefixEnd_7204581 3699412967250181777404241 := by
  unfold tailWord_7204581
  simp only [CollatzResearch.WordTrace]
  refine ⟨262772656712040956319221597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175181771141360637546147731 262772656712040956319221597)
  ·
    refine ⟨98539746267015358619708099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262772656712040956319221597 98539746267015358619708099)
    ·
      refine ⟨147809619400523037929562149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98539746267015358619708099 147809619400523037929562149)
      ·
        refine ⟨27714303637598069611792903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147809619400523037929562149 27714303637598069611792903)
        ·
          refine ⟨41571455456397104417689355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27714303637598069611792903 41571455456397104417689355)
          ·
            refine ⟨62357183184595656626534033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41571455456397104417689355 62357183184595656626534033)
            ·
              refine ⟨46767887388446742469900525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62357183184595656626534033 46767887388446742469900525)
              ·
                refine ⟨17537957770667528426212697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46767887388446742469900525 17537957770667528426212697)
                ·
                  refine ⟨13153468328000646319659523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17537957770667528426212697 13153468328000646319659523)
                  ·
                    refine ⟨19730202492000969479489285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13153468328000646319659523 19730202492000969479489285)
                    ·
                      refine ⟨3699412967250181777404241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19730202492000969479489285 3699412967250181777404241)
                      ·
                        rfl

theorem cell23_7204581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7204581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204581 prefixEnd_7204581 := by exact prefixLift 7204581
  have htrace : WordTrace (prefixWord ++ tailWord_7204581) baseStart_7204581 baseEnd_7204581 := by
    simpa [prefixWord, tailWord_7204581, baseEnd_7204581] using wordTrace_append hprefix tailTrace_7204581
  have hstable : (prefixWord ++ tailWord_7204581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204581).length < 2 ^ (prefixWord ++ tailWord_7204581).sum := by decide
  have hdescent : baseEnd_7204581 < baseStart_7204581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204598 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7204598 : Nat := 118140960795 + 7204598 * 2 ^ 59
def prefixEnd_7204598 : Nat := 4983230072969 + 3 ^ 40 * 7204598 * 2
def baseEnd_7204598 : Nat := 3699421696421308210891663

theorem tailTrace_7204598 : CollatzResearch.WordTrace tailWord_7204598 prefixEnd_7204598 3699421696421308210891663 := by
  unfold tailWord_7204598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423329797061210513911903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175182184501986245481726965 16423329797061210513911903)
  ·
    refine ⟨24634994695591815770867855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423329797061210513911903 24634994695591815770867855)
    ·
      refine ⟨36952492043387723656301783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24634994695591815770867855 36952492043387723656301783)
      ·
        refine ⟨55428738065081585484452675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36952492043387723656301783 55428738065081585484452675)
        ·
          refine ⟨83143107097622378226679013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55428738065081585484452675 83143107097622378226679013)
          ·
            refine ⟨15589332580804195917502315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83143107097622378226679013 15589332580804195917502315)
            ·
              refine ⟨23383998871206293876253473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589332580804195917502315 23383998871206293876253473)
              ·
                refine ⟨17537999153404720407190105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23383998871206293876253473 17537999153404720407190105)
                ·
                  refine ⟨13153499365053540305392579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17537999153404720407190105 13153499365053540305392579)
                  ·
                    refine ⟨19730249047580310458088869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13153499365053540305392579 19730249047580310458088869)
                    ·
                      refine ⟨3699421696421308210891663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19730249047580310458088869 3699421696421308210891663)
                      ·
                        rfl

theorem cell23_7204598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7204598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204598 prefixEnd_7204598 := by exact prefixLift 7204598
  have htrace : WordTrace (prefixWord ++ tailWord_7204598) baseStart_7204598 baseEnd_7204598 := by
    simpa [prefixWord, tailWord_7204598, baseEnd_7204598] using wordTrace_append hprefix tailTrace_7204598
  have hstable : (prefixWord ++ tailWord_7204598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204598).length < 2 ^ (prefixWord ++ tailWord_7204598).sum := by decide
  have hdescent : baseEnd_7204598 < baseStart_7204598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204604 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 8]
def baseStart_7204604 : Nat := 118140960795 + 7204604 * 2 ^ 59
def prefixEnd_7204604 : Nat := 4983230072969 + 3 ^ 40 * 7204604 * 2
def baseEnd_7204604 : Nat := 411047197478359465268515

theorem tailTrace_7204604 : CollatzResearch.WordTrace tailWord_7204604 prefixEnd_7204604 411047197478359465268515 := by
  unfold tailWord_7204604
  simp only [CollatzResearch.WordTrace]
  refine ⟨131386747795478815623654433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175182330393971754164872577 131386747795478815623654433)
  ·
    refine ⟨98540060846609111717740825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131386747795478815623654433 98540060846609111717740825)
    ·
      refine ⟨73905045634956833788305619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98540060846609111717740825 73905045634956833788305619)
      ·
        refine ⟨110857568452435250682458429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73905045634956833788305619 110857568452435250682458429)
        ·
          refine ⟨41571588169663219005921911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110857568452435250682458429 41571588169663219005921911)
          ·
            refine ⟨62357382254494828508882867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41571588169663219005921911 62357382254494828508882867)
            ·
              refine ⟨93536073381742242763324301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62357382254494828508882867 93536073381742242763324301)
              ·
                refine ⟨35076027518153341036246613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93536073381742242763324301 35076027518153341036246613)
                ·
                  refine ⟨411047197478359465268515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35076027518153341036246613 411047197478359465268515)
                  ·
                    rfl

theorem cell23_7204604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_7204604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204604 prefixEnd_7204604 := by exact prefixLift 7204604
  have htrace : WordTrace (prefixWord ++ tailWord_7204604) baseStart_7204604 baseEnd_7204604 := by
    simpa [prefixWord, tailWord_7204604, baseEnd_7204604] using wordTrace_append hprefix tailTrace_7204604
  have hstable : (prefixWord ++ tailWord_7204604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204604).length < 2 ^ (prefixWord ++ tailWord_7204604).sum := by decide
  have hdescent : baseEnd_7204604 < baseStart_7204604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204659 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 1, 4]
def baseStart_7204659 : Nat := 118140960795 + 7204659 * 2 ^ 59
def prefixEnd_7204659 : Nat := 4983230072969 + 3 ^ 40 * 7204659 * 2
def baseEnd_7204659 : Nat := 1233151006247077490742961

theorem tailTrace_7204659 : CollatzResearch.WordTrace tailWord_7204659 prefixEnd_7204659 1233151006247077490742961 := by
  unfold tailWord_7204659
  simp only [CollatzResearch.WordTrace]
  refine ⟨262775501605758375640561031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175183667737172250427040687 262775501605758375640561031)
  ·
    refine ⟨394163252408637563460841547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262775501605758375640561031 394163252408637563460841547)
    ·
      refine ⟨591244878612956345191262321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394163252408637563460841547 591244878612956345191262321)
      ·
        refine ⟨443433658959717258893446741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591244878612956345191262321 443433658959717258893446741)
        ·
          refine ⟨5196488190934186627657579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 443433658959717258893446741 5196488190934186627657579)
          ·
            refine ⟨7794732286401279941486369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196488190934186627657579 7794732286401279941486369)
            ·
              refine ⟨5846049214800959956114777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7794732286401279941486369 5846049214800959956114777)
              ·
                refine ⟨4384536911100719967086083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5846049214800959956114777 4384536911100719967086083)
                ·
                  refine ⟨6576805366651079950629125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384536911100719967086083 6576805366651079950629125)
                  ·
                    refine ⟨1233151006247077490742961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6576805366651079950629125 1233151006247077490742961)
                    ·
                      rfl

theorem cell23_7204659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 4].length) (baseStart_7204659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204659 prefixEnd_7204659 := by exact prefixLift 7204659
  have htrace : WordTrace (prefixWord ++ tailWord_7204659) baseStart_7204659 baseEnd_7204659 := by
    simpa [prefixWord, tailWord_7204659, baseEnd_7204659] using wordTrace_append hprefix tailTrace_7204659
  have hstable : (prefixWord ++ tailWord_7204659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204659).length < 2 ^ (prefixWord ++ tailWord_7204659).sum := by decide
  have hdescent : baseEnd_7204659 < baseStart_7204659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204681 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_7204681 : Nat := 118140960795 + 7204681 * 2 ^ 59
def prefixEnd_7204681 : Nat := 4983230072969 + 3 ^ 40 * 7204681 * 2
def baseEnd_7204681 : Nat := 1233154771771877128717927

theorem tailTrace_7204681 : CollatzResearch.WordTrace tailWord_7204681 prefixEnd_7204681 1233154771771877128717927 := by
  unfold tailWord_7204681
  simp only [CollatzResearch.WordTrace]
  refine ⟨262776304011678673397861897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175184202674452448931907931 262776304011678673397861897)
  ·
    refine ⟨197082228008759005048396423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262776304011678673397861897 197082228008759005048396423)
    ·
      refine ⟨295623342013138507572594635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197082228008759005048396423 295623342013138507572594635)
      ·
        refine ⟨443435013019707761358891953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295623342013138507572594635 443435013019707761358891953)
        ·
          refine ⟨332576259764780821019168965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443435013019707761358891953 332576259764780821019168965)
          ·
            refine ⟨62358048705896403941094181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332576259764780821019168965 62358048705896403941094181)
            ·
              refine ⟨11692134132355575738955159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62358048705896403941094181 11692134132355575738955159)
              ·
                refine ⟨17538201198533363608432739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692134132355575738955159 17538201198533363608432739)
                ·
                  refine ⟨26307301797800045412649109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17538201198533363608432739 26307301797800045412649109)
                  ·
                    refine ⟨1233154771771877128717927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26307301797800045412649109 1233154771771877128717927)
                    ·
                      rfl

theorem cell23_7204681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_7204681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204681 prefixEnd_7204681 := by exact prefixLift 7204681
  have htrace : WordTrace (prefixWord ++ tailWord_7204681) baseStart_7204681 baseEnd_7204681 := by
    simpa [prefixWord, tailWord_7204681, baseEnd_7204681] using wordTrace_append hprefix tailTrace_7204681
  have hstable : (prefixWord ++ tailWord_7204681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204681).length < 2 ^ (prefixWord ++ tailWord_7204681).sum := by decide
  have hdescent : baseEnd_7204681 < baseStart_7204681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204692 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_7204692 : Nat := 118140960795 + 7204692 * 2 ^ 59
def prefixEnd_7204692 : Nat := 4983230072969 + 3 ^ 40 * 7204692 * 2
def baseEnd_7204692 : Nat := 3699469963602830843116231

theorem tailTrace_7204692 : CollatzResearch.WordTrace tailWord_7204692 prefixEnd_7204692 3699469963602830843116231 := by
  unfold tailWord_7204692
  simp only [CollatzResearch.WordTrace]
  refine ⟨131388352607319411138256165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175184470143092548184341553 131388352607319411138256165)
  ·
    refine ⟨24635316113872389588423031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131388352607319411138256165 24635316113872389588423031)
    ·
      refine ⟨36952974170808584382634547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24635316113872389588423031 36952974170808584382634547)
      ·
        refine ⟨55429461256212876573951821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36952974170808584382634547 55429461256212876573951821)
        ·
          refine ⟨20786047971079828715231933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55429461256212876573951821 20786047971079828715231933)
          ·
            refine ⟨7794767989154935768211975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20786047971079828715231933 7794767989154935768211975)
            ·
              refine ⟨11692151983732403652317963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794767989154935768211975 11692151983732403652317963)
              ·
                refine ⟨17538227975598605478476945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692151983732403652317963 17538227975598605478476945)
                ·
                  refine ⟨13153670981698954108857709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17538227975598605478476945 13153670981698954108857709)
                  ·
                    refine ⟨4932626618137107790821641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13153670981698954108857709 4932626618137107790821641)
                    ·
                      refine ⟨3699469963602830843116231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932626618137107790821641 3699469963602830843116231)
                      ·
                        rfl

theorem cell23_7204692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_7204692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204692 prefixEnd_7204692 := by exact prefixLift 7204692
  have htrace : WordTrace (prefixWord ++ tailWord_7204692) baseStart_7204692 baseEnd_7204692 := by
    simpa [prefixWord, tailWord_7204692, baseEnd_7204692] using wordTrace_append hprefix tailTrace_7204692
  have hstable : (prefixWord ++ tailWord_7204692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204692).length < 2 ^ (prefixWord ++ tailWord_7204692).sum := by decide
  have hdescent : baseEnd_7204692 < baseStart_7204692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204756 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7204756 : Nat := 118140960795 + 7204756 * 2 ^ 59
def prefixEnd_7204756 : Nat := 4983230072969 + 3 ^ 40 * 7204756 * 2
def baseEnd_7204756 : Nat := 3699502826364718592715937

theorem tailTrace_7204756 : CollatzResearch.WordTrace tailWord_7204756 prefixEnd_7204756 3699502826364718592715937 := by
  unfold tailWord_7204756
  simp only [CollatzResearch.WordTrace]
  refine ⟨131389519743203480603421061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175186026324271307471228081 131389519743203480603421061)
  ·
    refine ⟨24635534951850652613141449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131389519743203480603421061 24635534951850652613141449)
    ·
      refine ⟨18476651213887989459856087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24635534951850652613141449 18476651213887989459856087)
      ·
        refine ⟨27714976820831984189784131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18476651213887989459856087 27714976820831984189784131)
        ·
          refine ⟨41572465231247976284676197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27714976820831984189784131 41572465231247976284676197)
          ·
            refine ⟨7794837230858995553376787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41572465231247976284676197 7794837230858995553376787)
            ·
              refine ⟨11692255846288493330065181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794837230858995553376787 11692255846288493330065181)
              ·
                refine ⟨4384595942358184998774443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11692255846288493330065181 4384595942358184998774443)
                ·
                  refine ⟨6576893913537277498161665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384595942358184998774443 6576893913537277498161665)
                  ·
                    refine ⟨4932670435152958123621249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6576893913537277498161665 4932670435152958123621249)
                    ·
                      refine ⟨3699502826364718592715937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932670435152958123621249 3699502826364718592715937)
                      ·
                        rfl

theorem cell23_7204756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7204756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204756 prefixEnd_7204756 := by exact prefixLift 7204756
  have htrace : WordTrace (prefixWord ++ tailWord_7204756) baseStart_7204756 baseEnd_7204756 := by
    simpa [prefixWord, tailWord_7204756, baseEnd_7204756] using wordTrace_append hprefix tailTrace_7204756
  have hstable : (prefixWord ++ tailWord_7204756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204756).length < 2 ^ (prefixWord ++ tailWord_7204756).sum := by decide
  have hdescent : baseEnd_7204756 < baseStart_7204756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204789 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_7204789 : Nat := 118140960795 + 7204789 * 2 ^ 59
def prefixEnd_7204789 : Nat := 4983230072969 + 3 ^ 40 * 7204789 * 2
def baseEnd_7204789 : Nat := 3699519771226316963603285

theorem tailTrace_7204789 : CollatzResearch.WordTrace tailWord_7204789 prefixEnd_7204789 3699519771226316963603285 := by
  unfold tailWord_7204789
  simp only [CollatzResearch.WordTrace]
  refine ⟨262780243095287407842793421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175186828730191605228528947 262780243095287407842793421)
  ·
    refine ⟨98542591160732777941047533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262780243095287407842793421 98542591160732777941047533)
    ·
      refine ⟨36953471685274791727892825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98542591160732777941047533 36953471685274791727892825)
      ·
        refine ⟨27715103763956093795919619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36953471685274791727892825 27715103763956093795919619)
        ·
          refine ⟨41572655645934140693879429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27715103763956093795919619 41572655645934140693879429)
          ·
            refine ⟨7794872933612651380102393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41572655645934140693879429 7794872933612651380102393)
            ·
              refine ⟨5846154700209488535076795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7794872933612651380102393 5846154700209488535076795)
              ·
                refine ⟨8769232050314232802615193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846154700209488535076795 8769232050314232802615193)
                ·
                  refine ⟨6576924037735674601961395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8769232050314232802615193 6576924037735674601961395)
                  ·
                    refine ⟨9865386056603511902942093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6576924037735674601961395 9865386056603511902942093)
                    ·
                      refine ⟨3699519771226316963603285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9865386056603511902942093 3699519771226316963603285)
                      ·
                        rfl

theorem cell23_7204789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_7204789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204789 prefixEnd_7204789 := by exact prefixLift 7204789
  have htrace : WordTrace (prefixWord ++ tailWord_7204789) baseStart_7204789 baseEnd_7204789 := by
    simpa [prefixWord, tailWord_7204789, baseEnd_7204789] using wordTrace_append hprefix tailTrace_7204789
  have hstable : (prefixWord ++ tailWord_7204789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204789).length < 2 ^ (prefixWord ++ tailWord_7204789).sum := by decide
  have hdescent : baseEnd_7204789 < baseStart_7204789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204791 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_7204791 : Nat := 118140960795 + 7204791 * 2 ^ 59
def prefixEnd_7204791 : Nat := 4983230072969 + 3 ^ 40 * 7204791 * 2
def baseEnd_7204791 : Nat := 3699520798187625955778275

theorem tailTrace_7204791 : CollatzResearch.WordTrace tailWord_7204791 prefixEnd_7204791 3699520798187625955778275 := by
  unfold tailWord_7204791
  simp only [CollatzResearch.WordTrace]
  refine ⟨262780316041280162184366227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175186877360853441456244151 262780316041280162184366227)
  ·
    refine ⟨394170474061920243276549341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262780316041280162184366227 394170474061920243276549341)
    ·
      refine ⟨147813927773220091228706003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394170474061920243276549341 147813927773220091228706003)
      ·
        refine ⟨221720891659830136843059005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147813927773220091228706003 221720891659830136843059005)
        ·
          refine ⟨83145334372436301316147127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221720891659830136843059005 83145334372436301316147127)
          ·
            refine ⟨124718001558654451974220691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83145334372436301316147127 124718001558654451974220691)
            ·
              refine ⟨187077002337981677961331037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124718001558654451974220691 187077002337981677961331037)
              ·
                refine ⟨70153875876743129235499139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187077002337981677961331037 70153875876743129235499139)
                ·
                  refine ⟨105230813815114693853248709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70153875876743129235499139 105230813815114693853248709)
                  ·
                    refine ⟨19730777590334005097484133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105230813815114693853248709 19730777590334005097484133)
                    ·
                      refine ⟨3699520798187625955778275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19730777590334005097484133 3699520798187625955778275)
                      ·
                        rfl

theorem cell23_7204791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_7204791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204791 prefixEnd_7204791 := by exact prefixLift 7204791
  have htrace : WordTrace (prefixWord ++ tailWord_7204791) baseStart_7204791 baseEnd_7204791 := by
    simpa [prefixWord, tailWord_7204791, baseEnd_7204791] using wordTrace_append hprefix tailTrace_7204791
  have hstable : (prefixWord ++ tailWord_7204791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204791).length < 2 ^ (prefixWord ++ tailWord_7204791).sum := by decide
  have hdescent : baseEnd_7204791 < baseStart_7204791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204798 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_7204798 : Nat := 118140960795 + 7204798 * 2 ^ 59
def prefixEnd_7204798 : Nat := 4983230072969 + 3 ^ 40 * 7204798 * 2
def baseEnd_7204798 : Nat := 3699524392552207428390743

theorem tailTrace_7204798 : CollatzResearch.WordTrace tailWord_7204798 prefixEnd_7204798 3699524392552207428390743 := by
  unfold tailWord_7204798
  simp only [CollatzResearch.WordTrace]
  refine ⟨32847571419031850297483881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175187047568169868253247365 32847571419031850297483881)
  ·
    refine ⟨24635678564273887723112911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32847571419031850297483881 24635678564273887723112911)
    ·
      refine ⟨36953517846410831584669367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24635678564273887723112911 36953517846410831584669367)
      ·
        refine ⟨55430276769616247377004051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36953517846410831584669367 55430276769616247377004051)
        ·
          refine ⟨83145415154424371065506077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55430276769616247377004051 83145415154424371065506077)
          ·
            refine ⟨31179530682909139149564779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83145415154424371065506077 31179530682909139149564779)
            ·
              refine ⟨46769296024363708724347169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31179530682909139149564779 46769296024363708724347169)
              ·
                refine ⟨35076972018272781543260377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46769296024363708724347169 35076972018272781543260377)
                ·
                  refine ⟨26307729013704586157445283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35076972018272781543260377 26307729013704586157445283)
                  ·
                    refine ⟨39461593520556879236167925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26307729013704586157445283 39461593520556879236167925)
                    ·
                      refine ⟨3699524392552207428390743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39461593520556879236167925 3699524392552207428390743)
                      ·
                        rfl

theorem cell23_7204798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_7204798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204798 prefixEnd_7204798 := by exact prefixLift 7204798
  have htrace : WordTrace (prefixWord ++ tailWord_7204798) baseStart_7204798 baseEnd_7204798 := by
    simpa [prefixWord, tailWord_7204798, baseEnd_7204798] using wordTrace_append hprefix tailTrace_7204798
  have hstable : (prefixWord ++ tailWord_7204798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204798).length < 2 ^ (prefixWord ++ tailWord_7204798).sum := by decide
  have hdescent : baseEnd_7204798 < baseStart_7204798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204835 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 5]
def baseStart_7204835 : Nat := 118140960795 + 7204835 * 2 ^ 59
def prefixEnd_7204835 : Nat := 4983230072969 + 3 ^ 40 * 7204835 * 2
def baseEnd_7204835 : Nat := 411060376815158198180897

theorem tailTrace_7204835 : CollatzResearch.WordTrace tailWord_7204835 prefixEnd_7204835 411060376815158198180897 := by
  unfold tailWord_7204835
  simp only [CollatzResearch.WordTrace]
  refine ⟨262781920853120757698967959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175187947235413838465978639 262781920853120757698967959)
  ·
    refine ⟨394172881279681136548451939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262781920853120757698967959 394172881279681136548451939)
    ·
      refine ⟨591259321919521704822677909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394172881279681136548451939 591259321919521704822677909)
      ·
        refine ⟨27715280714977579913563027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 591259321919521704822677909 27715280714977579913563027)
        ·
          refine ⟨41572921072466369870344541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27715280714977579913563027 41572921072466369870344541)
          ·
            refine ⟨15589845402174888701379203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41572921072466369870344541 15589845402174888701379203)
            ·
              refine ⟨23384768103262333052068805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589845402174888701379203 23384768103262333052068805)
              ·
                refine ⟨4384644019361687447262901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23384768103262333052068805 4384644019361687447262901)
                ·
                  refine ⟨411060376815158198180897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4384644019361687447262901 411060376815158198180897)
                  ·
                    rfl

theorem cell23_7204835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 5].length) (baseStart_7204835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204835 prefixEnd_7204835 := by exact prefixLift 7204835
  have htrace : WordTrace (prefixWord ++ tailWord_7204835) baseStart_7204835 baseEnd_7204835 := by
    simpa [prefixWord, tailWord_7204835, baseEnd_7204835] using wordTrace_append hprefix tailTrace_7204835
  have hstable : (prefixWord ++ tailWord_7204835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204835).length < 2 ^ (prefixWord ++ tailWord_7204835).sum := by decide
  have hdescent : baseEnd_7204835 < baseStart_7204835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204895 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 3, 4]
def baseStart_7204895 : Nat := 118140960795 + 7204895 * 2 ^ 59
def prefixEnd_7204895 : Nat := 4983230072969 + 3 ^ 40 * 7204895 * 2
def baseEnd_7204895 : Nat := 1233191400058564516292599

theorem tailTrace_7204895 : CollatzResearch.WordTrace tailWord_7204895 prefixEnd_7204895 1233191400058564516292599 := by
  unfold tailWord_7204895
  simp only [CollatzResearch.WordTrace]
  refine ⟨262784109232903387946152139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175189406155268925297434759 262784109232903387946152139)
  ·
    refine ⟨394176163849355081919228209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262784109232903387946152139 394176163849355081919228209)
    ·
      refine ⟨295632122887016311439421157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394176163849355081919228209 295632122887016311439421157)
      ·
        refine ⟨55431023041315558394891467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295632122887016311439421157 55431023041315558394891467)
        ·
          refine ⟨83146534561973337592337201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55431023041315558394891467 83146534561973337592337201)
          ·
            refine ⟨62359900921480003194252901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83146534561973337592337201 62359900921480003194252901)
            ·
              refine ⟨11692481422777500598922419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62359900921480003194252901 11692481422777500598922419)
              ·
                refine ⟨17538722134166250898383629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692481422777500598922419 17538722134166250898383629)
                ·
                  refine ⟨6577020800312344086893861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17538722134166250898383629 6577020800312344086893861)
                  ·
                    refine ⟨1233191400058564516292599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577020800312344086893861 1233191400058564516292599)
                    ·
                      rfl

theorem cell23_7204895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_7204895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204895 prefixEnd_7204895 := by exact prefixLift 7204895
  have htrace : WordTrace (prefixWord ++ tailWord_7204895) baseStart_7204895 baseEnd_7204895 := by
    simpa [prefixWord, tailWord_7204895, baseEnd_7204895] using wordTrace_append hprefix tailTrace_7204895
  have hstable : (prefixWord ++ tailWord_7204895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204895).length < 2 ^ (prefixWord ++ tailWord_7204895).sum := by decide
  have hdescent : baseEnd_7204895 < baseStart_7204895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204898 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7204898 : Nat := 118140960795 + 7204898 * 2 ^ 59
def prefixEnd_7204898 : Nat := 4983230072969 + 3 ^ 40 * 7204898 * 2
def baseEnd_7204898 : Nat := 3699575740617657037140283

theorem tailTrace_7204898 : CollatzResearch.WordTrace tailWord_7204898 prefixEnd_7204898 3699575740617657037140283 := by
  unfold tailWord_7204898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65696054662973129864627837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175189479101261679639007565 65696054662973129864627837)
  ·
    refine ⟨24636020498614923699235439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65696054662973129864627837 24636020498614923699235439)
    ·
      refine ⟨36954030747922385548853159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24636020498614923699235439 36954030747922385548853159)
      ·
        refine ⟨55431046121883578323279739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36954030747922385548853159 55431046121883578323279739)
        ·
          refine ⟨83146569182825367484919609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55431046121883578323279739 83146569182825367484919609)
          ·
            refine ⟨62359926887119025613689707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83146569182825367484919609 62359926887119025613689707)
            ·
              refine ⟨93539890330678538420534561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62359926887119025613689707 93539890330678538420534561)
              ·
                refine ⟨70154917748008903815400921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93539890330678538420534561 70154917748008903815400921)
                ·
                  refine ⟨52616188311006677861550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70154917748008903815400921 52616188311006677861550691)
                  ·
                    refine ⟨78924282466510016792326037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52616188311006677861550691 78924282466510016792326037)
                    ·
                      refine ⟨3699575740617657037140283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78924282466510016792326037 3699575740617657037140283)
                      ·
                        rfl

theorem cell23_7204898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7204898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204898 prefixEnd_7204898 := by exact prefixLift 7204898
  have htrace : WordTrace (prefixWord ++ tailWord_7204898) baseStart_7204898 baseEnd_7204898 := by
    simpa [prefixWord, tailWord_7204898, baseEnd_7204898] using wordTrace_append hprefix tailTrace_7204898
  have hstable : (prefixWord ++ tailWord_7204898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204898).length < 2 ^ (prefixWord ++ tailWord_7204898).sum := by decide
  have hdescent : baseEnd_7204898 < baseStart_7204898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204929 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7204929 : Nat := 118140960795 + 7204929 * 2 ^ 59
def prefixEnd_7204929 : Nat := 4983230072969 + 3 ^ 40 * 7204929 * 2
def baseEnd_7204929 : Nat := 1233197219505982138617547

theorem tailTrace_7204929 : CollatzResearch.WordTrace tailWord_7204929 prefixEnd_7204929 1233197219505982138617547 := by
  unfold tailWord_7204929
  simp only [CollatzResearch.WordTrace]
  refine ⟨262785349314780211752889841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175190232876520141168593227 262785349314780211752889841)
  ·
    refine ⟨197089011986085158814667381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262785349314780211752889841 197089011986085158814667381)
    ·
      refine ⟨18477094873695483638875067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197089011986085158814667381 18477094873695483638875067)
      ·
        refine ⟨27715642310543225458312601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18477094873695483638875067 27715642310543225458312601)
        ·
          refine ⟨20786731732907419093734451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27715642310543225458312601 20786731732907419093734451)
          ·
            refine ⟨31180097599361128640601677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20786731732907419093734451 31180097599361128640601677)
            ·
              refine ⟨11692536599760423240225629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31180097599361128640601677 11692536599760423240225629)
              ·
                refine ⟨4384701224910158715084611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11692536599760423240225629 4384701224910158715084611)
                ·
                  refine ⟨6577051837365238072626917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384701224910158715084611 6577051837365238072626917)
                  ·
                    refine ⟨1233197219505982138617547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577051837365238072626917 1233197219505982138617547)
                    ·
                      rfl

theorem cell23_7204929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7204929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204929 prefixEnd_7204929 := by exact prefixLift 7204929
  have htrace : WordTrace (prefixWord ++ tailWord_7204929) baseStart_7204929 baseEnd_7204929 := by
    simpa [prefixWord, tailWord_7204929, baseEnd_7204929] using wordTrace_append hprefix tailTrace_7204929
  have hstable : (prefixWord ++ tailWord_7204929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204929).length < 2 ^ (prefixWord ++ tailWord_7204929).sum := by decide
  have hdescent : baseEnd_7204929 < baseStart_7204929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204938 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_7204938 : Nat := 118140960795 + 7204938 * 2 ^ 59
def prefixEnd_7204938 : Nat := 4983230072969 + 3 ^ 40 * 7204938 * 2
def baseEnd_7204938 : Nat := 1233198759947945626880033

theorem tailTrace_7204938 : CollatzResearch.WordTrace tailWord_7204938 prefixEnd_7204938 1233198759947945626880033 := by
  unfold tailWord_7204938
  simp only [CollatzResearch.WordTrace]
  refine ⟨65696419392936901572491867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175190451714498404193311645 65696419392936901572491867)
  ·
    refine ⟨98544629089405352358737801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65696419392936901572491867 98544629089405352358737801)
    ·
      refine ⟨73908471817054014269053351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98544629089405352358737801 73908471817054014269053351)
      ·
        refine ⟨110862707725581021403580027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73908471817054014269053351 110862707725581021403580027)
        ·
          refine ⟨166294061588371532105370041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110862707725581021403580027 166294061588371532105370041)
          ·
            refine ⟨124720546191278649079027531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166294061588371532105370041 124720546191278649079027531)
            ·
              refine ⟨187080819286917973618541297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124720546191278649079027531 187080819286917973618541297)
              ·
                refine ⟨140310614465188480213905973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187080819286917973618541297 140310614465188480213905973)
                ·
                  refine ⟨13154120106111420020053685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140310614465188480213905973 13154120106111420020053685)
                  ·
                    refine ⟨1233198759947945626880033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13154120106111420020053685 1233198759947945626880033)
                    ·
                      rfl

theorem cell23_7204938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_7204938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204938 prefixEnd_7204938 := by exact prefixLift 7204938
  have htrace : WordTrace (prefixWord ++ tailWord_7204938) baseStart_7204938 baseEnd_7204938 := by
    simpa [prefixWord, tailWord_7204938, baseEnd_7204938] using wordTrace_append hprefix tailTrace_7204938
  have hstable : (prefixWord ++ tailWord_7204938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204938).length < 2 ^ (prefixWord ++ tailWord_7204938).sum := by decide
  have hdescent : baseEnd_7204938 < baseStart_7204938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204946 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_7204946 : Nat := 118140960795 + 7204946 * 2 ^ 59
def prefixEnd_7204946 : Nat := 4983230072969 + 3 ^ 40 * 7204946 * 2
def baseEnd_7204946 : Nat := 1233200129229690949780021

theorem tailTrace_7204946 : CollatzResearch.WordTrace tailWord_7204946 prefixEnd_7204946 1233200129229690949780021 := by
  unfold tailWord_7204946
  simp only [CollatzResearch.WordTrace]
  refine ⟨65696492338929655914064673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175190646237145749104172461 65696492338929655914064673)
  ·
    refine ⟨49272369254197241935548505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65696492338929655914064673 49272369254197241935548505)
    ·
      refine ⟨36954276940647931451661379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49272369254197241935548505 36954276940647931451661379)
      ·
        refine ⟨55431415410971897177492069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36954276940647931451661379 55431415410971897177492069)
        ·
          refine ⟨10393390389557230720779763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55431415410971897177492069 10393390389557230720779763)
          ·
            refine ⟨15590085584335846081169645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10393390389557230720779763 15590085584335846081169645)
            ·
              refine ⟨5846282094125942280438617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15590085584335846081169645 5846282094125942280438617)
              ·
                refine ⟨4384711570594456710328963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5846282094125942280438617 4384711570594456710328963)
                ·
                  refine ⟨6577067355891685065493445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384711570594456710328963 6577067355891685065493445)
                  ·
                    refine ⟨1233200129229690949780021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577067355891685065493445 1233200129229690949780021)
                    ·
                      rfl

theorem cell23_7204946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_7204946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204946 prefixEnd_7204946 := by exact prefixLift 7204946
  have htrace : WordTrace (prefixWord ++ tailWord_7204946) baseStart_7204946 baseEnd_7204946 := by
    simpa [prefixWord, tailWord_7204946, baseEnd_7204946] using wordTrace_append hprefix tailTrace_7204946
  have hstable : (prefixWord ++ tailWord_7204946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204946).length < 2 ^ (prefixWord ++ tailWord_7204946).sum := by decide
  have hdescent : baseEnd_7204946 < baseStart_7204946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204948 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_7204948 : Nat := 118140960795 + 7204948 * 2 ^ 59
def prefixEnd_7204948 : Nat := 4983230072969 + 3 ^ 40 * 7204948 * 2
def baseEnd_7204948 : Nat := 3699601414650381841515053

theorem tailTrace_7204948 : CollatzResearch.WordTrace tailWord_7204948 prefixEnd_7204948 3699601414650381841515053 := by
  unfold tailWord_7204948
  simp only [CollatzResearch.WordTrace]
  refine ⟨131393021150855688998915749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175190694867807585331887665 131393021150855688998915749)
  ·
    refine ⟨24636191465785441687296703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131393021150855688998915749 24636191465785441687296703)
    ·
      refine ⟨36954287198678162530945055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24636191465785441687296703 36954287198678162530945055)
      ·
        refine ⟨55431430798017243796417583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36954287198678162530945055 55431430798017243796417583)
        ·
          refine ⟨83147146197025865694626375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55431430798017243796417583 83147146197025865694626375)
          ·
            refine ⟨124720719295538798541939563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83147146197025865694626375 124720719295538798541939563)
            ·
              refine ⟨187081078943308197812909345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124720719295538798541939563 187081078943308197812909345)
              ·
                refine ⟨140310809207481148359682009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187081078943308197812909345 140310809207481148359682009)
                ·
                  refine ⟨105233106905610861269761507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140310809207481148359682009 105233106905610861269761507)
                  ·
                    refine ⟨157849660358416291904642261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105233106905610861269761507 157849660358416291904642261)
                    ·
                      refine ⟨3699601414650381841515053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157849660358416291904642261 3699601414650381841515053)
                      ·
                        rfl

theorem cell23_7204948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_7204948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204948 prefixEnd_7204948 := by exact prefixLift 7204948
  have htrace : WordTrace (prefixWord ++ tailWord_7204948) baseStart_7204948 baseEnd_7204948 := by
    simpa [prefixWord, tailWord_7204948, baseEnd_7204948] using wordTrace_append hprefix tailTrace_7204948
  have hstable : (prefixWord ++ tailWord_7204948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204948).length < 2 ^ (prefixWord ++ tailWord_7204948).sum := by decide
  have hdescent : baseEnd_7204948 < baseStart_7204948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204952 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_7204952 : Nat := 118140960795 + 7204952 * 2 ^ 59
def prefixEnd_7204952 : Nat := 4983230072969 + 3 ^ 40 * 7204952 * 2
def baseEnd_7204952 : Nat := 3699603468572999825865035

theorem tailTrace_7204952 : CollatzResearch.WordTrace tailWord_7204952 prefixEnd_7204952 3699603468572999825865035 := by
  unfold tailWord_7204952
  simp only [CollatzResearch.WordTrace]
  refine ⟨131393094096848443340488555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175190792129131257787318073 131393094096848443340488555)
  ·
    refine ⟨197089641145272665010732833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131393094096848443340488555 197089641145272665010732833)
    ·
      refine ⟨147817230858954498758049625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197089641145272665010732833 147817230858954498758049625)
      ·
        refine ⟨110862923144215874068537219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147817230858954498758049625 110862923144215874068537219)
        ·
          refine ⟨166294384716323811102805829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110862923144215874068537219 166294384716323811102805829)
          ·
            refine ⟨31180197134310714581776093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166294384716323811102805829 31180197134310714581776093)
            ·
              refine ⟨11692573925366517968166035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31180197134310714581776093 11692573925366517968166035)
              ·
                refine ⟨17538860888049776952249053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692573925366517968166035 17538860888049776952249053)
                ·
                  refine ⟨6577072833018666357093395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17538860888049776952249053 6577072833018666357093395)
                  ·
                    refine ⟨9865609249527999535640093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6577072833018666357093395 9865609249527999535640093)
                    ·
                      refine ⟨3699603468572999825865035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9865609249527999535640093 3699603468572999825865035)
                      ·
                        rfl

theorem cell23_7204952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_7204952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204952 prefixEnd_7204952 := by exact prefixLift 7204952
  have htrace : WordTrace (prefixWord ++ tailWord_7204952) baseStart_7204952 baseEnd_7204952 := by
    simpa [prefixWord, tailWord_7204952, baseEnd_7204952] using wordTrace_append hprefix tailTrace_7204952
  have hstable : (prefixWord ++ tailWord_7204952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204952).length < 2 ^ (prefixWord ++ tailWord_7204952).sum := by decide
  have hdescent : baseEnd_7204952 < baseStart_7204952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204972 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_7204972 : Nat := 118140960795 + 7204972 * 2 ^ 59
def prefixEnd_7204972 : Nat := 4983230072969 + 3 ^ 40 * 7204972 * 2
def baseEnd_7204972 : Nat := 1233204579395363249204981

theorem tailTrace_7204972 : CollatzResearch.WordTrace tailWord_7204972 prefixEnd_7204972 1233204579395363249204981 := by
  unfold tailWord_7204972
  simp only [CollatzResearch.WordTrace]
  refine ⟨131393458826812215048352585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175191278435749620064470113 131393458826812215048352585)
  ·
    refine ⟨98545094120109161286264439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131393458826812215048352585 98545094120109161286264439)
    ·
      refine ⟨147817641180163741929396659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98545094120109161286264439 147817641180163741929396659)
      ·
        refine ⟨221726461770245612894094989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147817641180163741929396659 221726461770245612894094989)
        ·
          refine ⟨83147423163842104835285621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221726461770245612894094989 83147423163842104835285621)
          ·
            refine ⟨7795070921610197328308027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83147423163842104835285621 7795070921610197328308027)
            ·
              refine ⟨11692606382415295992462041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795070921610197328308027 11692606382415295992462041)
              ·
                refine ⟨8769454786811471994346531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11692606382415295992462041 8769454786811471994346531)
                ·
                  refine ⟨13154182180217207991519797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769454786811471994346531 13154182180217207991519797)
                  ·
                    refine ⟨1233204579395363249204981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13154182180217207991519797 1233204579395363249204981)
                    ·
                      rfl

theorem cell23_7204972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_7204972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204972 prefixEnd_7204972 := by exact prefixLift 7204972
  have htrace : WordTrace (prefixWord ++ tailWord_7204972) baseStart_7204972 baseEnd_7204972 := by
    simpa [prefixWord, tailWord_7204972, baseEnd_7204972] using wordTrace_append hprefix tailTrace_7204972
  have hstable : (prefixWord ++ tailWord_7204972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204972).length < 2 ^ (prefixWord ++ tailWord_7204972).sum := by decide
  have hdescent : baseEnd_7204972 < baseStart_7204972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204975 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_7204975 : Nat := 118140960795 + 7204975 * 2 ^ 59
def prefixEnd_7204975 : Nat := 4983230072969 + 3 ^ 40 * 7204975 * 2
def baseEnd_7204975 : Nat := 3699615278628053235877429

theorem tailTrace_7204975 : CollatzResearch.WordTrace tailWord_7204975 prefixEnd_7204975 3699615278628053235877429 := by
  unfold tailWord_7204975
  simp only [CollatzResearch.WordTrace]
  refine ⟨262787027072613561609064379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175191351381742374406042919 262787027072613561609064379)
  ·
    refine ⟨394180540608920342413596569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262787027072613561609064379 394180540608920342413596569)
    ·
      refine ⟨295635405456690256810197427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394180540608920342413596569 295635405456690256810197427)
      ·
        refine ⟨443453108185035385215296141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295635405456690256810197427 443453108185035385215296141)
        ·
          refine ⟨166294915569388269455736053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443453108185035385215296141 166294915569388269455736053)
          ·
            refine ⟨15590148334630150261475255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166294915569388269455736053 15590148334630150261475255)
            ·
              refine ⟨23385222501945225392212883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15590148334630150261475255 23385222501945225392212883)
              ·
                refine ⟨35077833752917838088319325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23385222501945225392212883 35077833752917838088319325)
                ·
                  refine ⟨13154187657344189283119747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35077833752917838088319325 13154187657344189283119747)
                  ·
                    refine ⟨19731281486016283924679621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13154187657344189283119747 19731281486016283924679621)
                    ·
                      refine ⟨3699615278628053235877429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19731281486016283924679621 3699615278628053235877429)
                      ·
                        rfl

theorem cell23_7204975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_7204975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204975 prefixEnd_7204975 := by exact prefixLift 7204975
  have htrace : WordTrace (prefixWord ++ tailWord_7204975) baseStart_7204975 baseEnd_7204975 := by
    simpa [prefixWord, tailWord_7204975, baseEnd_7204975] using wordTrace_append hprefix tailTrace_7204975
  have hstable : (prefixWord ++ tailWord_7204975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204975).length < 2 ^ (prefixWord ++ tailWord_7204975).sum := by decide
  have hdescent : baseEnd_7204975 < baseStart_7204975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204985 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_7204985 : Nat := 118140960795 + 7204985 * 2 ^ 59
def prefixEnd_7204985 : Nat := 4983230072969 + 3 ^ 40 * 7204985 * 2
def baseEnd_7204985 : Nat := 1233206804478199398917461

theorem tailTrace_7204985 : CollatzResearch.WordTrace tailWord_7204985 prefixEnd_7204985 1233206804478199398917461 := by
  unfold tailWord_7204985
  simp only [CollatzResearch.WordTrace]
  refine ⟨262787391802577333316928409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175191594535051555544618939 262787391802577333316928409)
  ·
    refine ⟨197090543851932999987696307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262787391802577333316928409 197090543851932999987696307)
    ·
      refine ⟨295635815777899499981544461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197090543851932999987696307 295635815777899499981544461)
      ·
        refine ⟨110863430916712312493079173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295635815777899499981544461 110863430916712312493079173)
        ·
          refine ⟨20786893296883558592452345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110863430916712312493079173 20786893296883558592452345)
          ·
            refine ⟨15590169972662668944339259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20786893296883558592452345 15590169972662668944339259)
            ·
              refine ⟨23385254958994003416508889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15590169972662668944339259 23385254958994003416508889)
              ·
                refine ⟨17538941219245502562381667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23385254958994003416508889 17538941219245502562381667)
                ·
                  refine ⟨26308411828868253843572501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17538941219245502562381667 26308411828868253843572501)
                  ·
                    refine ⟨1233206804478199398917461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26308411828868253843572501 1233206804478199398917461)
                    ·
                      rfl

theorem cell23_7204985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_7204985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204985 prefixEnd_7204985 := by exact prefixLift 7204985
  have htrace : WordTrace (prefixWord ++ tailWord_7204985) baseStart_7204985 baseEnd_7204985 := by
    simpa [prefixWord, tailWord_7204985, baseEnd_7204985] using wordTrace_append hprefix tailTrace_7204985
  have hstable : (prefixWord ++ tailWord_7204985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204985).length < 2 ^ (prefixWord ++ tailWord_7204985).sum := by decide
  have hdescent : baseEnd_7204985 < baseStart_7204985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7204995 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5]
def baseStart_7204995 : Nat := 118140960795 + 7204995 * 2 ^ 59
def prefixEnd_7204995 : Nat := 4983230072969 + 3 ^ 40 * 7204995 * 2
def baseEnd_7204995 : Nat := 3699625548241143157627337

theorem tailTrace_7204995 : CollatzResearch.WordTrace tailWord_7204995 prefixEnd_7204995 3699625548241143157627337 := by
  unfold tailWord_7204995
  simp only [CollatzResearch.WordTrace]
  refine ⟨262787756532541105024792439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175191837688360736683194959 262787756532541105024792439)
  ·
    refine ⟨394181634798811657537188659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262787756532541105024792439 394181634798811657537188659)
    ·
      refine ⟨591272452198217486305782989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394181634798811657537188659 591272452198217486305782989)
      ·
        refine ⟨221727169574331557364668621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591272452198217486305782989 221727169574331557364668621)
        ·
          refine ⟨83147688590374334011750733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221727169574331557364668621 83147688590374334011750733)
          ·
            refine ⟨31180383221390375254406525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83147688590374334011750733 31180383221390375254406525)
            ·
              refine ⟨11692643708021390720402447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31180383221390375254406525 11692643708021390720402447)
              ·
                refine ⟨17538965562032086080603671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692643708021390720402447 17538965562032086080603671)
                ·
                  refine ⟨26308448343048129120905507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17538965562032086080603671 26308448343048129120905507)
                  ·
                    refine ⟨39462672514572193681358261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26308448343048129120905507 39462672514572193681358261)
                    ·
                      refine ⟨3699625548241143157627337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39462672514572193681358261 3699625548241143157627337)
                      ·
                        rfl

theorem cell23_7204995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_7204995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7204995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7204995 prefixEnd_7204995 := by exact prefixLift 7204995
  have htrace : WordTrace (prefixWord ++ tailWord_7204995) baseStart_7204995 baseEnd_7204995 := by
    simpa [prefixWord, tailWord_7204995, baseEnd_7204995] using wordTrace_append hprefix tailTrace_7204995
  have hstable : (prefixWord ++ tailWord_7204995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7204995).length < 2 ^ (prefixWord ++ tailWord_7204995).sum := by decide
  have hdescent : baseEnd_7204995 < baseStart_7204995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7204995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205002 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_7205002 : Nat := 118140960795 + 7205002 * 2 ^ 59
def prefixEnd_7205002 : Nat := 4983230072969 + 3 ^ 40 * 7205002 * 2
def baseEnd_7205002 : Nat := 1233209714201908210079935

theorem tailTrace_7205002 : CollatzResearch.WordTrace tailWord_7205002 prefixEnd_7205002 1233209714201908210079935 := by
  unfold tailWord_7205002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65697002960878936305074315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175192007895677163480198173 65697002960878936305074315)
  ·
    refine ⟨98545504441318404457611473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65697002960878936305074315 98545504441318404457611473)
    ·
      refine ⟨73909128330988803343208605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98545504441318404457611473 73909128330988803343208605)
      ·
        refine ⟨27715923124120801253703227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73909128330988803343208605 27715923124120801253703227)
        ·
          refine ⟨41573884686181201880554841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27715923124120801253703227 41573884686181201880554841)
          ·
            refine ⟨31180413514635901410416131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41573884686181201880554841 31180413514635901410416131)
            ·
              refine ⟨46770620271953852115624197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31180413514635901410416131 46770620271953852115624197)
              ·
                refine ⟨8769491300991347271679537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46770620271953852115624197 8769491300991347271679537)
                ·
                  refine ⟨6577118475743510453759653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8769491300991347271679537 6577118475743510453759653)
                  ·
                    refine ⟨1233209714201908210079935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577118475743510453759653 1233209714201908210079935)
                    ·
                      rfl

theorem cell23_7205002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_7205002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205002 prefixEnd_7205002 := by exact prefixLift 7205002
  have htrace : WordTrace (prefixWord ++ tailWord_7205002) baseStart_7205002 baseEnd_7205002 := by
    simpa [prefixWord, tailWord_7205002, baseEnd_7205002] using wordTrace_append hprefix tailTrace_7205002
  have hstable : (prefixWord ++ tailWord_7205002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205002).length < 2 ^ (prefixWord ++ tailWord_7205002).sum := by decide
  have hdescent : baseEnd_7205002 < baseStart_7205002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205026 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7205026 : Nat := 118140960795 + 7205026 * 2 ^ 59
def prefixEnd_7205026 : Nat := 4983230072969 + 3 ^ 40 * 7205026 * 2
def baseEnd_7205026 : Nat := 3699641466141432536339695

theorem tailTrace_7205026 : CollatzResearch.WordTrace tailWord_7205026 prefixEnd_7205026 3699641466141432536339695 := by
  unfold tailWord_7205026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65697221798857199329792733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175192591463619198212780621 65697221798857199329792733)
  ·
    refine ⟨24636458174571449748672275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65697221798857199329792733 24636458174571449748672275)
    ·
      refine ⟨36954687261857174623008413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24636458174571449748672275 36954687261857174623008413)
      ·
        refine ⟨13858007723196440483628155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36954687261857174623008413 13858007723196440483628155)
        ·
          refine ⟨20787011584794660725442233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858007723196440483628155 20787011584794660725442233)
          ·
            refine ⟨15590258688595995544081675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20787011584794660725442233 15590258688595995544081675)
            ·
              refine ⟨23385388032893993316122513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15590258688595995544081675 23385388032893993316122513)
              ·
                refine ⟨17539041024670494987091885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23385388032893993316122513 17539041024670494987091885)
                ·
                  refine ⟨6577140384251435620159457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17539041024670494987091885 6577140384251435620159457)
                  ·
                    refine ⟨4932855288188576715119593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577140384251435620159457 4932855288188576715119593)
                    ·
                      refine ⟨3699641466141432536339695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4932855288188576715119593 3699641466141432536339695)
                      ·
                        rfl

theorem cell23_7205026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7205026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205026 prefixEnd_7205026 := by exact prefixLift 7205026
  have htrace : WordTrace (prefixWord ++ tailWord_7205026) baseStart_7205026 baseEnd_7205026 := by
    simpa [prefixWord, tailWord_7205026, baseEnd_7205026] using wordTrace_append hprefix tailTrace_7205026
  have hstable : (prefixWord ++ tailWord_7205026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205026).length < 2 ^ (prefixWord ++ tailWord_7205026).sum := by decide
  have hdescent : baseEnd_7205026 < baseStart_7205026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205042 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_7205042 : Nat := 118140960795 + 7205042 * 2 ^ 59
def prefixEnd_7205042 : Nat := 4983230072969 + 3 ^ 40 * 7205042 * 2
def baseEnd_7205042 : Nat := 3699649681831904473739621

theorem tailTrace_7205042 : CollatzResearch.WordTrace tailWord_7205042 prefixEnd_7205042 3699649681831904473739621 := by
  unfold tailWord_7205042
  simp only [CollatzResearch.WordTrace]
  refine ⟨65697367690842708012938345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175192980508913888034502253 65697367690842708012938345)
  ·
    refine ⟨49273025768132031009703759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65697367690842708012938345 49273025768132031009703759)
    ·
      refine ⟨73909538652198046514555639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49273025768132031009703759 73909538652198046514555639)
      ·
        refine ⟨110864307978297069771833459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73909538652198046514555639 110864307978297069771833459)
        ·
          refine ⟨166296461967445604657750189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110864307978297069771833459 166296461967445604657750189)
          ·
            refine ⟨62361173237792101746656321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166296461967445604657750189 62361173237792101746656321)
            ·
              refine ⟨46770879928344076309992241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62361173237792101746656321 46770879928344076309992241)
              ·
                refine ⟨35078159946258057232494181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46770879928344076309992241 35078159946258057232494181)
                ·
                  refine ⟨6577154989923385731092659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35078159946258057232494181 6577154989923385731092659)
                  ·
                    refine ⟨9865732484885078596638989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6577154989923385731092659 9865732484885078596638989)
                    ·
                      refine ⟨3699649681831904473739621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9865732484885078596638989 3699649681831904473739621)
                      ·
                        rfl

theorem cell23_7205042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_7205042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205042 prefixEnd_7205042 := by exact prefixLift 7205042
  have htrace : WordTrace (prefixWord ++ tailWord_7205042) baseStart_7205042 baseEnd_7205042 := by
    simpa [prefixWord, tailWord_7205042, baseEnd_7205042] using wordTrace_append hprefix tailTrace_7205042
  have hstable : (prefixWord ++ tailWord_7205042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205042).length < 2 ^ (prefixWord ++ tailWord_7205042).sum := by decide
  have hdescent : baseEnd_7205042 < baseStart_7205042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205152 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_7205152 : Nat := 118140960795 + 7205152 * 2 ^ 59
def prefixEnd_7205152 : Nat := 4983230072969 + 3 ^ 40 * 7205152 * 2
def baseEnd_7205152 : Nat := 1233235388234633014454705

theorem tailTrace_7205152 : CollatzResearch.WordTrace tailWord_7205152 prefixEnd_7205152 1233235388234633014454705 := by
  unfold tailWord_7205152
  simp only [CollatzResearch.WordTrace]
  refine ⟨131396741396486160419128855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175195655195314880558838473 131396741396486160419128855)
  ·
    refine ⟨197095112094729240628693283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131396741396486160419128855 197095112094729240628693283)
    ·
      refine ⟨295642668142093860943039925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197095112094729240628693283 295642668142093860943039925)
      ·
        refine ⟨27716500138321299463409993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295642668142093860943039925 27716500138321299463409993)
        ·
          refine ⟨20787375103740974597557495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27716500138321299463409993 20787375103740974597557495)
          ·
            refine ⟨31181062655611461896336243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20787375103740974597557495 31181062655611461896336243)
            ·
              refine ⟨46771593983417192844504365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31181062655611461896336243 46771593983417192844504365)
              ·
                refine ⟨17539347743781447316689137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46771593983417192844504365 17539347743781447316689137)
                ·
                  refine ⟨13154510807836085487516853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17539347743781447316689137 13154510807836085487516853)
                  ·
                    refine ⟨1233235388234633014454705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13154510807836085487516853 1233235388234633014454705)
                    ·
                      rfl

theorem cell23_7205152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_7205152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205152 prefixEnd_7205152 := by exact prefixLift 7205152
  have htrace : WordTrace (prefixWord ++ tailWord_7205152) baseStart_7205152 baseEnd_7205152 := by
    simpa [prefixWord, tailWord_7205152, baseEnd_7205152] using wordTrace_append hprefix tailTrace_7205152
  have hstable : (prefixWord ++ tailWord_7205152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205152).length < 2 ^ (prefixWord ++ tailWord_7205152).sum := by decide
  have hdescent : baseEnd_7205152 < baseStart_7205152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205192 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_7205192 : Nat := 118140960795 + 7205192 * 2 ^ 59
def prefixEnd_7205192 : Nat := 4983230072969 + 3 ^ 40 * 7205192 * 2
def baseEnd_7205192 : Nat := 3699726703930078886863931

theorem tailTrace_7205192 : CollatzResearch.WordTrace tailWord_7205192 prefixEnd_7205192 3699726703930078886863931 := by
  unfold tailWord_7205192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131397470856413703834856915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175196627808551605113142553 131397470856413703834856915)
  ·
    refine ⟨197096206284620555752285373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131397470856413703834856915 197096206284620555752285373)
    ·
      refine ⟨73911077356732708407107015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197096206284620555752285373 73911077356732708407107015)
      ·
        refine ⟨110866616035099062610660523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73911077356732708407107015 110866616035099062610660523)
        ·
          refine ⟨166299924052648593915990785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110866616035099062610660523 166299924052648593915990785)
          ·
            refine ⟨124724943039486445436993089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166299924052648593915990785 124724943039486445436993089)
            ·
              refine ⟨93543707279614834077744817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124724943039486445436993089 93543707279614834077744817)
              ·
                refine ⟨70157780459711125558308613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93543707279614834077744817 70157780459711125558308613)
                ·
                  refine ⟨13154583836195836042182865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70157780459711125558308613 13154583836195836042182865)
                  ·
                    refine ⟨9865937877146877031637149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13154583836195836042182865 9865937877146877031637149)
                    ·
                      refine ⟨3699726703930078886863931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9865937877146877031637149 3699726703930078886863931)
                      ·
                        rfl

theorem cell23_7205192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_7205192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205192 prefixEnd_7205192 := by exact prefixLift 7205192
  have htrace : WordTrace (prefixWord ++ tailWord_7205192) baseStart_7205192 baseEnd_7205192 := by
    simpa [prefixWord, tailWord_7205192, baseEnd_7205192] using wordTrace_append hprefix tailTrace_7205192
  have hstable : (prefixWord ++ tailWord_7205192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205192).length < 2 ^ (prefixWord ++ tailWord_7205192).sum := by decide
  have hdescent : baseEnd_7205192 < baseStart_7205192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205235 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_7205235 : Nat := 118140960795 + 7205235 * 2 ^ 59
def prefixEnd_7205235 : Nat := 4983230072969 + 3 ^ 40 * 7205235 * 2
def baseEnd_7205235 : Nat := 3699748783598222218626233

theorem tailTrace_7205235 : CollatzResearch.WordTrace tailWord_7205235 prefixEnd_7205235 3699748783598222218626233 := by
  unfold tailWord_7205235
  simp only [CollatzResearch.WordTrace]
  refine ⟨262796510051671626013529159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175197673367781084009019439 262796510051671626013529159)
  ·
    refine ⟨394194765077507439020293739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262796510051671626013529159 394194765077507439020293739)
    ·
      refine ⟨591292147616261158530440609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394194765077507439020293739 591292147616261158530440609)
      ·
        refine ⟨443469110712195868897830457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591292147616261158530440609 443469110712195868897830457)
        ·
          refine ⟨332601833034146901673372843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443469110712195868897830457 332601833034146901673372843)
          ·
            refine ⟨498902749551220352510059265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332601833034146901673372843 498902749551220352510059265)
            ·
              refine ⟨374177062163415264382544449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498902749551220352510059265 374177062163415264382544449)
              ·
                refine ⟨280632796622561448286908337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374177062163415264382544449 280632796622561448286908337)
                ·
                  refine ⟨210474597466921086215181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280632796622561448286908337 210474597466921086215181253)
                  ·
                    refine ⟨39463987025047703665346485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210474597466921086215181253 39463987025047703665346485)
                    ·
                      refine ⟨3699748783598222218626233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39463987025047703665346485 3699748783598222218626233)
                      ·
                        rfl

theorem cell23_7205235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_7205235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205235 prefixEnd_7205235 := by exact prefixLift 7205235
  have htrace : WordTrace (prefixWord ++ tailWord_7205235) baseStart_7205235 baseEnd_7205235 := by
    simpa [prefixWord, tailWord_7205235, baseEnd_7205235] using wordTrace_append hprefix tailTrace_7205235
  have hstable : (prefixWord ++ tailWord_7205235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205235).length < 2 ^ (prefixWord ++ tailWord_7205235).sum := by decide
  have hdescent : baseEnd_7205235 < baseStart_7205235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205259 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 1, 5]
def baseStart_7205259 : Nat := 118140960795 + 7205259 * 2 ^ 59
def prefixEnd_7205259 : Nat := 4983230072969 + 3 ^ 40 * 7205259 * 2
def baseEnd_7205259 : Nat := 1233253702377976708242041

theorem tailTrace_7205259 : CollatzResearch.WordTrace tailWord_7205259 prefixEnd_7205259 1233253702377976708242041 := by
  unfold tailWord_7205259
  simp only [CollatzResearch.WordTrace]
  refine ⟨262797385403584678112402831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175198256935723118741601887 262797385403584678112402831)
  ·
    refine ⟨394196078105377017168604247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262797385403584678112402831 394196078105377017168604247)
    ·
      refine ⟨591294117158065525752906371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394196078105377017168604247 591294117158065525752906371)
      ·
        refine ⟨886941175737098288629359557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591294117158065525752906371 886941175737098288629359557)
        ·
          refine ⟨166301470450705929118004917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 886941175737098288629359557 166301470450705929118004917)
          ·
            refine ⟨15590762854753680854812961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166301470450705929118004917 15590762854753680854812961)
            ·
              refine ⟨11693072141065260641109721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15590762854753680854812961 11693072141065260641109721)
              ·
                refine ⟨8769804105798945480832291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11693072141065260641109721 8769804105798945480832291)
                ·
                  refine ⟨13154706158698418221248437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769804105798945480832291 13154706158698418221248437)
                  ·
                    refine ⟨1233253702377976708242041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13154706158698418221248437 1233253702377976708242041)
                    ·
                      rfl

theorem cell23_7205259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 5].length) (baseStart_7205259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205259 prefixEnd_7205259 := by exact prefixLift 7205259
  have htrace : WordTrace (prefixWord ++ tailWord_7205259) baseStart_7205259 baseEnd_7205259 := by
    simpa [prefixWord, tailWord_7205259, baseEnd_7205259] using wordTrace_append hprefix tailTrace_7205259
  have hstable : (prefixWord ++ tailWord_7205259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205259).length < 2 ^ (prefixWord ++ tailWord_7205259).sum := by decide
  have hdescent : baseEnd_7205259 < baseStart_7205259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205279 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7205279 : Nat := 118140960795 + 7205279 * 2 ^ 59
def prefixEnd_7205279 : Nat := 4983230072969 + 3 ^ 40 * 7205279 * 2
def baseEnd_7205279 : Nat := 3699771376747020046476031

theorem tailTrace_7205279 : CollatzResearch.WordTrace tailWord_7205279 prefixEnd_7205279 3699771376747020046476031 := by
  unfold tailWord_7205279
  simp only [CollatzResearch.WordTrace]
  refine ⟨262798114863512221528130891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175198743242341481018753927 262798114863512221528130891)
  ·
    refine ⟨394197172295268332292196337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262798114863512221528130891 394197172295268332292196337)
    ·
      refine ⟨295647879221451249219147253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394197172295268332292196337 295647879221451249219147253)
      ·
        refine ⟨27716988677011054614295055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295647879221451249219147253 27716988677011054614295055)
        ·
          refine ⟨41575483015516581921442583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27716988677011054614295055 41575483015516581921442583)
          ·
            refine ⟨62363224523274872882163875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41575483015516581921442583 62363224523274872882163875)
            ·
              refine ⟨93544836784912309323245813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62363224523274872882163875 93544836784912309323245813)
              ·
                refine ⟨8769828448585528999054295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93544836784912309323245813 8769828448585528999054295)
                ·
                  refine ⟨13154742672878293498581443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769828448585528999054295 13154742672878293498581443)
                  ·
                    refine ⟨19732114009317440247872165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13154742672878293498581443 19732114009317440247872165)
                    ·
                      refine ⟨3699771376747020046476031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19732114009317440247872165 3699771376747020046476031)
                      ·
                        rfl

theorem cell23_7205279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7205279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205279 prefixEnd_7205279 := by exact prefixLift 7205279
  have htrace : WordTrace (prefixWord ++ tailWord_7205279) baseStart_7205279 baseEnd_7205279 := by
    simpa [prefixWord, tailWord_7205279, baseEnd_7205279] using wordTrace_append hprefix tailTrace_7205279
  have hstable : (prefixWord ++ tailWord_7205279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205279).length < 2 ^ (prefixWord ++ tailWord_7205279).sum := by decide
  have hdescent : baseEnd_7205279 < baseStart_7205279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205329 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_7205329 : Nat := 118140960795 + 7205329 * 2 ^ 59
def prefixEnd_7205329 : Nat := 4983230072969 + 3 ^ 40 * 7205329 * 2
def baseEnd_7205329 : Nat := 3699797050779744850850801

theorem tailTrace_7205329 : CollatzResearch.WordTrace tailWord_7205329 prefixEnd_7205329 3699797050779744850850801 := by
  unfold tailWord_7205329
  simp only [CollatzResearch.WordTrace]
  refine ⟨262799938513331080067451041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175199959008887386711634027 262799938513331080067451041)
  ·
    refine ⟨197099953884998310050588281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262799938513331080067451041 197099953884998310050588281)
    ·
      refine ⟨147824965413748732537941211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197099953884998310050588281 147824965413748732537941211)
      ·
        refine ⟨221737448120623098806911817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147824965413748732537941211 221737448120623098806911817)
        ·
          refine ⟨166303086090467324105183863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221737448120623098806911817 166303086090467324105183863)
          ·
            refine ⟨249454629135700986157775795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166303086090467324105183863 249454629135700986157775795)
            ·
              refine ⟨374181943703551479236663693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249454629135700986157775795 374181943703551479236663693)
              ·
                refine ⟨140318228888831804713748885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374181943703551479236663693 140318228888831804713748885)
                ·
                  refine ⟨6577416979163990845956979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140318228888831804713748885 6577416979163990845956979)
                  ·
                    refine ⟨9866125468745986268935469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6577416979163990845956979 9866125468745986268935469)
                    ·
                      refine ⟨3699797050779744850850801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9866125468745986268935469 3699797050779744850850801)
                      ·
                        rfl

theorem cell23_7205329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_7205329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205329 prefixEnd_7205329 := by exact prefixLift 7205329
  have htrace : WordTrace (prefixWord ++ tailWord_7205329) baseStart_7205329 baseEnd_7205329 := by
    simpa [prefixWord, tailWord_7205329, baseEnd_7205329] using wordTrace_append hprefix tailTrace_7205329
  have hstable : (prefixWord ++ tailWord_7205329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205329).length < 2 ^ (prefixWord ++ tailWord_7205329).sum := by decide
  have hdescent : baseEnd_7205329 < baseStart_7205329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205330 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7205330 : Nat := 118140960795 + 7205330 * 2 ^ 59
def prefixEnd_7205330 : Nat := 4983230072969 + 3 ^ 40 * 7205330 * 2
def baseEnd_7205330 : Nat := 3699797564260399346938297

theorem tailTrace_7205330 : CollatzResearch.WordTrace tailWord_7205330 prefixEnd_7205330 3699797564260399346938297 := by
  unfold tailWord_7205330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65699993746581864309559361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175199983324218304825491629 65699993746581864309559361)
  ·
    refine ⟨49274995309936398232169521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65699993746581864309559361 49274995309936398232169521)
    ·
      refine ⟨36956246482452298674127141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49274995309936398232169521 36956246482452298674127141)
      ·
        refine ⟨6929296215459806001398839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36956246482452298674127141 6929296215459806001398839)
        ·
          refine ⟨10393944323189709002098259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929296215459806001398839 10393944323189709002098259)
          ·
            refine ⟨15590916484784563503147389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10393944323189709002098259 15590916484784563503147389)
            ·
              refine ⟨5846593681794211313680271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15590916484784563503147389 5846593681794211313680271)
              ·
                refine ⟨8769890522691316970520407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846593681794211313680271 8769890522691316970520407)
                ·
                  refine ⟨13154835784036975455780611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769890522691316970520407 13154835784036975455780611)
                  ·
                    refine ⟨19732253676055463183670917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13154835784036975455780611 19732253676055463183670917)
                    ·
                      refine ⟨3699797564260399346938297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19732253676055463183670917 3699797564260399346938297)
                      ·
                        rfl

theorem cell23_7205330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7205330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205330 prefixEnd_7205330 := by exact prefixLift 7205330
  have htrace : WordTrace (prefixWord ++ tailWord_7205330) baseStart_7205330 baseEnd_7205330 := by
    simpa [prefixWord, tailWord_7205330, baseEnd_7205330] using wordTrace_append hprefix tailTrace_7205330
  have hstable : (prefixWord ++ tailWord_7205330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205330).length < 2 ^ (prefixWord ++ tailWord_7205330).sum := by decide
  have hdescent : baseEnd_7205330 < baseStart_7205330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
