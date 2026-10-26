import V185TrunkScan23Chunk0302

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1792432 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_1792432 : Nat := 118140960795 + 1792432 * 2 ^ 59
def prefixEnd_1792432 : Nat := 4983230072969 + 3 ^ 40 * 1792432 * 2
def baseEnd_1792432 : Nat := 920379156499836335256761

theorem tailTrace_1792432 : CollatzResearch.WordTrace tailWord_1792432 prefixEnd_1792432 920379156499836335256761 := by
  unfold tailWord_1792432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32687682921166230929505775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43583577228221641239341033 32687682921166230929505775)
  ·
    refine ⟨49031524381749346394258663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32687682921166230929505775 49031524381749346394258663)
    ·
      refine ⟨73547286572624019591387995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49031524381749346394258663 73547286572624019591387995)
      ·
        refine ⟨110320929858936029387081993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73547286572624019591387995 110320929858936029387081993)
        ·
          refine ⟨82740697394202022040311495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110320929858936029387081993 82740697394202022040311495)
          ·
            refine ⟨124111046091303033060467243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82740697394202022040311495 124111046091303033060467243)
            ·
              refine ⟨186166569136954549590700865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124111046091303033060467243 186166569136954549590700865)
              ·
                refine ⟨139624926852715912193025649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186166569136954549590700865 139624926852715912193025649)
                ·
                  refine ⟨104718695139536934144769237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139624926852715912193025649 104718695139536934144769237)
                  ·
                    refine ⟨2454344417332896894018029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 104718695139536934144769237 2454344417332896894018029)
                    ·
                      refine ⟨920379156499836335256761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454344417332896894018029 920379156499836335256761)
                      ·
                        rfl

theorem cell23_1792432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_1792432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792432 prefixEnd_1792432 := by exact prefixLift 1792432
  have htrace : WordTrace (prefixWord ++ tailWord_1792432) baseStart_1792432 baseEnd_1792432 := by
    simpa [prefixWord, tailWord_1792432, baseEnd_1792432] using wordTrace_append hprefix tailTrace_1792432
  have hstable : (prefixWord ++ tailWord_1792432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792432).length < 2 ^ (prefixWord ++ tailWord_1792432).sum := by decide
  have hdescent : baseEnd_1792432 < baseStart_1792432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792433 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_1792433 : Nat := 118140960795 + 1792433 * 2 ^ 59
def prefixEnd_1792433 : Nat := 4983230072969 + 3 ^ 40 * 1792433 * 2
def baseEnd_1792433 : Nat := 920379669980490831344257

theorem tailTrace_1792433 : CollatzResearch.WordTrace tailWord_1792433 prefixEnd_1792433 920379669980490831344257 := by
  unfold tailWord_1792433
  simp only [CollatzResearch.WordTrace]
  refine ⟨65375402315328839029797953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43583601543552559353198635 65375402315328839029797953)
  ·
    refine ⟨49031551736496629272348465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65375402315328839029797953 49031551736496629272348465)
    ·
      refine ⟨36773663802372471954261349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49031551736496629272348465 36773663802372471954261349)
      ·
        refine ⟨6895061962944838491424003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36773663802372471954261349 6895061962944838491424003)
        ·
          refine ⟨10342592944417257737136005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895061962944838491424003 10342592944417257737136005)
          ·
            refine ⟨1939236177078235825713001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10342592944417257737136005 1939236177078235825713001)
            ·
              refine ⟨1454427132808676869284751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939236177078235825713001 1454427132808676869284751)
              ·
                refine ⟨2181640699213015303927127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454427132808676869284751 2181640699213015303927127)
                ·
                  refine ⟨3272461048819522955890691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181640699213015303927127 3272461048819522955890691)
                  ·
                    refine ⟨4908691573229284433836037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3272461048819522955890691 4908691573229284433836037)
                    ·
                      refine ⟨920379669980490831344257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4908691573229284433836037 920379669980490831344257)
                      ·
                        rfl

theorem cell23_1792433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_1792433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792433 prefixEnd_1792433 := by exact prefixLift 1792433
  have htrace : WordTrace (prefixWord ++ tailWord_1792433) baseStart_1792433 baseEnd_1792433 := by
    simpa [prefixWord, tailWord_1792433, baseEnd_1792433] using wordTrace_append hprefix tailTrace_1792433
  have hstable : (prefixWord ++ tailWord_1792433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792433).length < 2 ^ (prefixWord ++ tailWord_1792433).sum := by decide
  have hdescent : baseEnd_1792433 < baseStart_1792433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792509 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1792509 : Nat := 118140960795 + 1792509 * 2 ^ 59
def prefixEnd_1792509 : Nat := 4983230072969 + 3 ^ 40 * 1792509 * 2
def baseEnd_1792509 : Nat := 920418694510232533993907

theorem tailTrace_1792509 : CollatzResearch.WordTrace tailWord_1792509 prefixEnd_1792509 920418694510232533993907 := by
  unfold tailWord_1792509
  simp only [CollatzResearch.WordTrace]
  refine ⟨65378174263053504009564581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43585449508702336006376387 65378174263053504009564581)
  ·
    refine ⟨12258407674322532001793359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65378174263053504009564581 12258407674322532001793359)
    ·
      refine ⟨18387611511483798002690039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258407674322532001793359 18387611511483798002690039)
      ·
        refine ⟨27581417267225697004035059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18387611511483798002690039 27581417267225697004035059)
        ·
          refine ⟨41372125900838545506052589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27581417267225697004035059 41372125900838545506052589)
          ·
            refine ⟨15514547212814454564769721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41372125900838545506052589 15514547212814454564769721)
            ·
              refine ⟨11635910409610840923577291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15514547212814454564769721 11635910409610840923577291)
              ·
                refine ⟨17453865614416261385365937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635910409610840923577291 17453865614416261385365937)
                ·
                  refine ⟨13090399210812196039024453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17453865614416261385365937 13090399210812196039024453)
                  ·
                    refine ⟨2454449852027286757317085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13090399210812196039024453 2454449852027286757317085)
                    ·
                      refine ⟨920418694510232533993907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454449852027286757317085 920418694510232533993907)
                      ·
                        rfl

theorem cell23_1792509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1792509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792509 prefixEnd_1792509 := by exact prefixLift 1792509
  have htrace : WordTrace (prefixWord ++ tailWord_1792509) baseStart_1792509 baseEnd_1792509 := by
    simpa [prefixWord, tailWord_1792509, baseEnd_1792509] using wordTrace_append hprefix tailTrace_1792509
  have hstable : (prefixWord ++ tailWord_1792509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792509).length < 2 ^ (prefixWord ++ tailWord_1792509).sum := by decide
  have hdescent : baseEnd_1792509 < baseStart_1792509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792546 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1792546 : Nat := 118140960795 + 1792546 * 2 ^ 59
def prefixEnd_1792546 : Nat := 4983230072969 + 3 ^ 40 * 1792546 * 2
def baseEnd_1792546 : Nat := 102270854810494321025693

theorem tailTrace_1792546 : CollatzResearch.WordTrace tailWord_1792546 prefixEnd_1792546 102270854810494321025693 := by
  unfold tailWord_1792546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16344880940979864832165373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43586349175946306219107661 16344880940979864832165373)
  ·
    refine ⟨6129330352867449312062015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16344880940979864832165373 6129330352867449312062015)
    ·
      refine ⟨9193995529301173968093023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129330352867449312062015 9193995529301173968093023)
      ·
        refine ⟨13790993293951760952139535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193995529301173968093023 13790993293951760952139535)
        ·
          refine ⟨20686489940927641428209303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13790993293951760952139535 20686489940927641428209303)
          ·
            refine ⟨31029734911391462142313955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20686489940927641428209303 31029734911391462142313955)
            ·
              refine ⟨46544602367087193213470933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31029734911391462142313955 46544602367087193213470933)
              ·
                refine ⟨1090889117978606090940725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46544602367087193213470933 1090889117978606090940725)
                ·
                  refine ⟨102270854810494321025693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090889117978606090940725 102270854810494321025693)
                  ·
                    rfl

theorem cell23_1792546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1792546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792546 prefixEnd_1792546 := by exact prefixLift 1792546
  have htrace : WordTrace (prefixWord ++ tailWord_1792546) baseStart_1792546 baseEnd_1792546 := by
    simpa [prefixWord, tailWord_1792546, baseEnd_1792546] using wordTrace_append hprefix tailTrace_1792546
  have hstable : (prefixWord ++ tailWord_1792546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792546).length < 2 ^ (prefixWord ++ tailWord_1792546).sum := by decide
  have hdescent : baseEnd_1792546 < baseStart_1792546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792569 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1792569 : Nat := 118140960795 + 1792569 * 2 ^ 59
def prefixEnd_1792569 : Nat := 4983230072969 + 3 ^ 40 * 1792569 * 2
def baseEnd_1792569 : Nat := 920449503349502299243631

theorem tailTrace_1792569 : CollatzResearch.WordTrace tailWord_1792569 prefixEnd_1792569 920449503349502299243631 := by
  unfold tailWord_1792569
  simp only [CollatzResearch.WordTrace]
  refine ⟨65380362642836134256748761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43586908428557422837832507 65380362642836134256748761)
  ·
    refine ⟨49035271982127100692561571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65380362642836134256748761 49035271982127100692561571)
    ·
      refine ⟨73552907973190651038842357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49035271982127100692561571 73552907973190651038842357)
      ·
        refine ⟨6895585122486623534891471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73552907973190651038842357 6895585122486623534891471)
        ·
          refine ⟨10343377683729935302337207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895585122486623534891471 10343377683729935302337207)
          ·
            refine ⟨15515066525594902953505811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343377683729935302337207 15515066525594902953505811)
            ·
              refine ⟨23272599788392354430258717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515066525594902953505811 23272599788392354430258717)
              ·
                refine ⟨8727224920647132911347019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23272599788392354430258717 8727224920647132911347019)
                ·
                  refine ⟨13090837380970699367020529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727224920647132911347019 13090837380970699367020529)
                  ·
                    refine ⟨9818128035728024525265397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13090837380970699367020529 9818128035728024525265397)
                    ·
                      refine ⟨920449503349502299243631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9818128035728024525265397 920449503349502299243631)
                      ·
                        rfl

theorem cell23_1792569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1792569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792569 prefixEnd_1792569 := by exact prefixLift 1792569
  have htrace : WordTrace (prefixWord ++ tailWord_1792569) baseStart_1792569 baseEnd_1792569 := by
    simpa [prefixWord, tailWord_1792569, baseEnd_1792569] using wordTrace_append hprefix tailTrace_1792569
  have hstable : (prefixWord ++ tailWord_1792569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792569).length < 2 ^ (prefixWord ++ tailWord_1792569).sum := by decide
  have hdescent : baseEnd_1792569 < baseStart_1792569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792579 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4]
def baseStart_1792579 : Nat := 118140960795 + 1792579 * 2 ^ 59
def prefixEnd_1792579 : Nat := 4983230072969 + 3 ^ 40 * 1792579 * 2
def baseEnd_1792579 : Nat := 920454638156047260118585

theorem tailTrace_1792579 : CollatzResearch.WordTrace tailWord_1792579 prefixEnd_1792579 920454638156047260118585 := by
  unfold tailWord_1792579
  simp only [CollatzResearch.WordTrace]
  refine ⟨65380727372799905964612791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43587151581866603976408527 65380727372799905964612791)
  ·
    refine ⟨98071091059199858946919187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65380727372799905964612791 98071091059199858946919187)
    ·
      refine ⟨147106636588799788420378781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98071091059199858946919187 147106636588799788420378781)
      ·
        refine ⟨55164988720799920657642043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147106636588799788420378781 55164988720799920657642043)
        ·
          refine ⟨82747483081199880986463065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55164988720799920657642043 82747483081199880986463065)
          ·
            refine ⟨62060612310899910739847299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82747483081199880986463065 62060612310899910739847299)
            ·
              refine ⟨93090918466349866109770949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62060612310899910739847299 93090918466349866109770949)
              ·
                refine ⟨17454547212440599895582053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93090918466349866109770949 17454547212440599895582053)
                ·
                  refine ⟨3272727602332612480421635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17454547212440599895582053 3272727602332612480421635)
                  ·
                    refine ⟨4909091403498918720632453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3272727602332612480421635 4909091403498918720632453)
                    ·
                      refine ⟨920454638156047260118585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4909091403498918720632453 920454638156047260118585)
                      ·
                        rfl

theorem cell23_1792579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_1792579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792579 prefixEnd_1792579 := by exact prefixLift 1792579
  have htrace : WordTrace (prefixWord ++ tailWord_1792579) baseStart_1792579 baseEnd_1792579 := by
    simpa [prefixWord, tailWord_1792579, baseEnd_1792579] using wordTrace_append hprefix tailTrace_1792579
  have hstable : (prefixWord ++ tailWord_1792579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792579).length < 2 ^ (prefixWord ++ tailWord_1792579).sum := by decide
  have hdescent : baseEnd_1792579 < baseStart_1792579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792580 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 7]
def baseStart_1792580 : Nat := 118140960795 + 1792580 * 2 ^ 59
def prefixEnd_1792580 : Nat := 4983230072969 + 3 ^ 40 * 1792580 * 2
def baseEnd_1792580 : Nat := 102272794626300195134009

theorem tailTrace_1792580 : CollatzResearch.WordTrace tailWord_1792580 prefixEnd_1792580 102272794626300195134009 := by
  unfold tailWord_1792580
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690381922898141567699597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43587175897197522090266129 32690381922898141567699597)
  ·
    refine ⟨12258893221086803087887349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32690381922898141567699597 12258893221086803087887349)
    ·
      refine ⟨1149271239476887789489439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12258893221086803087887349 1149271239476887789489439)
      ·
        refine ⟨1723906859215331684234159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149271239476887789489439 1723906859215331684234159)
        ·
          refine ⟨2585860288822997526351239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723906859215331684234159 2585860288822997526351239)
          ·
            refine ⟨3878790433234496289526859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585860288822997526351239 3878790433234496289526859)
            ·
              refine ⟨5818185649851744434290289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878790433234496289526859 5818185649851744434290289)
              ·
                refine ⟨4363639237388808325717717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818185649851744434290289 4363639237388808325717717)
                ·
                  refine ⟨102272794626300195134009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4363639237388808325717717 102272794626300195134009)
                  ·
                    rfl

theorem cell23_1792580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_1792580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792580 prefixEnd_1792580 := by exact prefixLift 1792580
  have htrace : WordTrace (prefixWord ++ tailWord_1792580) baseStart_1792580 baseEnd_1792580 := by
    simpa [prefixWord, tailWord_1792580, baseEnd_1792580] using wordTrace_append hprefix tailTrace_1792580
  have hstable : (prefixWord ++ tailWord_1792580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792580).length < 2 ^ (prefixWord ++ tailWord_1792580).sum := by decide
  have hdescent : baseEnd_1792580 < baseStart_1792580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792596 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1792596 : Nat := 118140960795 + 1792596 * 2 ^ 59
def prefixEnd_1792596 : Nat := 4983230072969 + 3 ^ 40 * 1792596 * 2
def baseEnd_1792596 : Nat := 920463367327173693606007

theorem tailTrace_1792596 : CollatzResearch.WordTrace tailWord_1792596 prefixEnd_1792596 920463367327173693606007 := by
  unfold tailWord_1792596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690673706869158933990821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43587564942492211911987761 32690673706869158933990821)
  ·
    refine ⟨6129501320037967300123279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32690673706869158933990821 6129501320037967300123279)
    ·
      refine ⟨9194251980056950950184919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129501320037967300123279 9194251980056950950184919)
      ·
        refine ⟨13791377970085426425277379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9194251980056950950184919 13791377970085426425277379)
        ·
          refine ⟨20687066955128139637916069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13791377970085426425277379 20687066955128139637916069)
          ·
            refine ⟨3878825054086526182109263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20687066955128139637916069 3878825054086526182109263)
            ·
              refine ⟨5818237581129789273163895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878825054086526182109263 5818237581129789273163895)
              ·
                refine ⟨8727356371694683909745843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818237581129789273163895 8727356371694683909745843)
                ·
                  refine ⟨13091034557542025864618765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8727356371694683909745843 13091034557542025864618765)
                  ·
                    refine ⟨4909137959078259699232037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13091034557542025864618765 4909137959078259699232037)
                    ·
                      refine ⟨920463367327173693606007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4909137959078259699232037 920463367327173693606007)
                      ·
                        rfl

theorem cell23_1792596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1792596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792596 prefixEnd_1792596 := by exact prefixLift 1792596
  have htrace : WordTrace (prefixWord ++ tailWord_1792596) baseStart_1792596 baseEnd_1792596 := by
    simpa [prefixWord, tailWord_1792596, baseEnd_1792596] using wordTrace_append hprefix tailTrace_1792596
  have hstable : (prefixWord ++ tailWord_1792596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792596).length < 2 ^ (prefixWord ++ tailWord_1792596).sum := by decide
  have hdescent : baseEnd_1792596 < baseStart_1792596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792609 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1792609 : Nat := 118140960795 + 1792609 * 2 ^ 59
def prefixEnd_1792609 : Nat := 4983230072969 + 3 ^ 40 * 1792609 * 2
def baseEnd_1792609 : Nat := 920470042575682142743447

theorem tailTrace_1792609 : CollatzResearch.WordTrace tailWord_1792609 prefixEnd_1792609 920470042575682142743447 := by
  unfold tailWord_1792609
  simp only [CollatzResearch.WordTrace]
  refine ⟨65381821562691221088204881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43587881041794147392136587 65381821562691221088204881)
  ·
    refine ⟨49036366172018415816153661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65381821562691221088204881 49036366172018415816153661)
    ·
      refine ⟨18388637314506905931057623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49036366172018415816153661 18388637314506905931057623)
      ·
        refine ⟨27582955971760358896586435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388637314506905931057623 27582955971760358896586435)
        ·
          refine ⟨41374433957640538344879653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582955971760358896586435 41374433957640538344879653)
          ·
            refine ⟨7757706367057600939664935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41374433957640538344879653 7757706367057600939664935)
            ·
              refine ⟨11636559550586401409497403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757706367057600939664935 11636559550586401409497403)
              ·
                refine ⟨17454839325879602114246105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11636559550586401409497403 17454839325879602114246105)
                ·
                  refine ⟨13091129494409701585684579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17454839325879602114246105 13091129494409701585684579)
                  ·
                    refine ⟨19636694241614552378526869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13091129494409701585684579 19636694241614552378526869)
                    ·
                      refine ⟨920470042575682142743447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19636694241614552378526869 920470042575682142743447)
                      ·
                        rfl

theorem cell23_1792609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1792609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792609 prefixEnd_1792609 := by exact prefixLift 1792609
  have htrace : WordTrace (prefixWord ++ tailWord_1792609) baseStart_1792609 baseEnd_1792609 := by
    simpa [prefixWord, tailWord_1792609, baseEnd_1792609] using wordTrace_append hprefix tailTrace_1792609
  have hstable : (prefixWord ++ tailWord_1792609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792609).length < 2 ^ (prefixWord ++ tailWord_1792609).sum := by decide
  have hdescent : baseEnd_1792609 < baseStart_1792609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792619 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 6]
def baseStart_1792619 : Nat := 118140960795 + 1792619 * 2 ^ 59
def prefixEnd_1792619 : Nat := 4983230072969 + 3 ^ 40 * 1792619 * 2
def baseEnd_1792619 : Nat := 102275019709136344846489

theorem tailTrace_1792619 : CollatzResearch.WordTrace tailWord_1792619 prefixEnd_1792619 102275019709136344846489 := by
  unfold tailWord_1792619
  simp only [CollatzResearch.WordTrace]
  refine ⟨65382186292654992796068911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43588124195103328530712607 65382186292654992796068911)
  ·
    refine ⟨98073279438982489194103367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65382186292654992796068911 98073279438982489194103367)
    ·
      refine ⟨147109919158473733791155051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98073279438982489194103367 147109919158473733791155051)
      ·
        refine ⟨220664878737710600686732577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147109919158473733791155051 220664878737710600686732577)
        ·
          refine ⟨165498659053282950515049433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220664878737710600686732577 165498659053282950515049433)
          ·
            refine ⟨124123994289962212886287075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165498659053282950515049433 124123994289962212886287075)
            ·
              refine ⟨186185991434943319329430613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124123994289962212886287075 186185991434943319329430613)
              ·
                refine ⟨2181867087128242023391765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 186185991434943319329430613 2181867087128242023391765)
                ·
                  refine ⟨102275019709136344846489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2181867087128242023391765 102275019709136344846489)
                  ·
                    rfl

theorem cell23_1792619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 6].length) (baseStart_1792619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792619 prefixEnd_1792619 := by exact prefixLift 1792619
  have htrace : WordTrace (prefixWord ++ tailWord_1792619) baseStart_1792619 baseEnd_1792619 := by
    simpa [prefixWord, tailWord_1792619, baseEnd_1792619] using wordTrace_append hprefix tailTrace_1792619
  have hstable : (prefixWord ++ tailWord_1792619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792619).length < 2 ^ (prefixWord ++ tailWord_1792619).sum := by decide
  have hdescent : baseEnd_1792619 < baseStart_1792619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792623 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 1, 4]
def baseStart_1792623 : Nat := 118140960795 + 1792623 * 2 ^ 59
def prefixEnd_1792623 : Nat := 4983230072969 + 3 ^ 40 * 1792623 * 2
def baseEnd_1792623 : Nat := 306825743768281695989461

theorem tailTrace_1792623 : CollatzResearch.WordTrace tailWord_1792623 prefixEnd_1792623 306825743768281695989461 := by
  unfold tailWord_1792623
  simp only [CollatzResearch.WordTrace]
  refine ⟨65382332184640501479214523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43588221456427000986143015 65382332184640501479214523)
  ·
    refine ⟨98073498276960752218821785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65382332184640501479214523 98073498276960752218821785)
    ·
      refine ⟨73555123707720564164116339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98073498276960752218821785 73555123707720564164116339)
      ·
        refine ⟨110332685561580846246174509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73555123707720564164116339 110332685561580846246174509)
        ·
          refine ⟨41374757085592817342315441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110332685561580846246174509 41374757085592817342315441)
          ·
            refine ⟨31031067814194613006736581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41374757085592817342315441 31031067814194613006736581)
            ·
              refine ⟨5818325215161489938763109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31031067814194613006736581 5818325215161489938763109)
              ·
                refine ⟨1090935977842779363518083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5818325215161489938763109 1090935977842779363518083)
                ·
                  refine ⟨1636403966764169045277125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090935977842779363518083 1636403966764169045277125)
                  ·
                    refine ⟨306825743768281695989461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636403966764169045277125 306825743768281695989461)
                    ·
                      rfl

theorem cell23_1792623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 4].length) (baseStart_1792623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792623 prefixEnd_1792623 := by exact prefixLift 1792623
  have htrace : WordTrace (prefixWord ++ tailWord_1792623) baseStart_1792623 baseEnd_1792623 := by
    simpa [prefixWord, tailWord_1792623, baseEnd_1792623] using wordTrace_append hprefix tailTrace_1792623
  have hstable : (prefixWord ++ tailWord_1792623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792623).length < 2 ^ (prefixWord ++ tailWord_1792623).sum := by decide
  have hdescent : baseEnd_1792623 < baseStart_1792623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792703 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_1792703 : Nat := 118140960795 + 1792703 * 2 ^ 59
def prefixEnd_1792703 : Nat := 4983230072969 + 3 ^ 40 * 1792703 * 2
def baseEnd_1792703 : Nat := 920518309757204774968015

theorem tailTrace_1792703 : CollatzResearch.WordTrace tailWord_1792703 prefixEnd_1792703 920518309757204774968015 := by
  unfold tailWord_1792703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65385250024350675142126763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43590166682900450094751175 65385250024350675142126763)
  ·
    refine ⟨98077875036526012713190145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65385250024350675142126763 98077875036526012713190145)
    ·
      refine ⟨73558406277394509534892609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98077875036526012713190145 73558406277394509534892609)
      ·
        refine ⟨55168804708045882151169457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73558406277394509534892609 55168804708045882151169457)
        ·
          refine ⟨41376603531034411613377093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55168804708045882151169457 41376603531034411613377093)
          ·
            refine ⟨7758113162068952177508205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41376603531034411613377093 7758113162068952177508205)
            ·
              refine ⟨2909292435775857066565577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7758113162068952177508205 2909292435775857066565577)
              ·
                refine ⟨2181969326831892799924183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909292435775857066565577 2181969326831892799924183)
                ·
                  refine ⟨3272953990247839199886275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181969326831892799924183 3272953990247839199886275)
                  ·
                    refine ⟨4909430985371758799829413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3272953990247839199886275 4909430985371758799829413)
                    ·
                      refine ⟨920518309757204774968015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4909430985371758799829413 920518309757204774968015)
                      ·
                        rfl

theorem cell23_1792703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_1792703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792703 prefixEnd_1792703 := by exact prefixLift 1792703
  have htrace : WordTrace (prefixWord ++ tailWord_1792703) baseStart_1792703 baseEnd_1792703 := by
    simpa [prefixWord, tailWord_1792703, baseEnd_1792703] using wordTrace_append hprefix tailTrace_1792703
  have hstable : (prefixWord ++ tailWord_1792703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792703).length < 2 ^ (prefixWord ++ tailWord_1792703).sum := by decide
  have hdescent : baseEnd_1792703 < baseStart_1792703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792726 : List Nat := [5, 2, 1, 15]
def baseStart_1792726 : Nat := 118140960795 + 1792726 * 2 ^ 59
def prefixEnd_1792726 : Nat := 4983230072969 + 3 ^ 40 * 1792726 * 2
def baseEnd_1792726 : Nat := 420909977051787007307

theorem tailTrace_1792726 : CollatzResearch.WordTrace tailWord_1792726 prefixEnd_1792726 420909977051787007307 := by
  unfold tailWord_1792726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086630556454209379388377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43590725935511566713476021 4086630556454209379388377)
  ·
    refine ⟨3064972917340657034541283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4086630556454209379388377 3064972917340657034541283)
    ·
      refine ⟨4597459376010985551811925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064972917340657034541283 4597459376010985551811925)
      ·
        refine ⟨420909977051787007307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 4597459376010985551811925 420909977051787007307)
        ·
          rfl

theorem cell23_1792726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 15].length) (baseStart_1792726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792726 prefixEnd_1792726 := by exact prefixLift 1792726
  have htrace : WordTrace (prefixWord ++ tailWord_1792726) baseStart_1792726 baseEnd_1792726 := by
    simpa [prefixWord, tailWord_1792726, baseEnd_1792726] using wordTrace_append hprefix tailTrace_1792726
  have hstable : (prefixWord ++ tailWord_1792726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792726).length < 2 ^ (prefixWord ++ tailWord_1792726).sum := by decide
  have hdescent : baseEnd_1792726 < baseStart_1792726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792736 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1792736 : Nat := 118140960795 + 1792736 * 2 ^ 59
def prefixEnd_1792736 : Nat := 4983230072969 + 3 ^ 40 * 1792736 * 2
def baseEnd_1792736 : Nat := 920535254618803145855363

theorem tailTrace_1792736 : CollatzResearch.WordTrace tailWord_1792736 prefixEnd_1792736 920535254618803145855363 := by
  unfold tailWord_1792736
  simp only [CollatzResearch.WordTrace]
  refine ⟨32693226816615560889039031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43590969088820747852052041 32693226816615560889039031)
  ·
    refine ⟨49039840224923341333558547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32693226816615560889039031 49039840224923341333558547)
    ·
      refine ⟨73559760337385012000337821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49039840224923341333558547 73559760337385012000337821)
      ·
        refine ⟨27584910126519379500126683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73559760337385012000337821 27584910126519379500126683)
        ·
          refine ⟨41377365189779069250190025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27584910126519379500126683 41377365189779069250190025)
          ·
            refine ⟨31033023892334301937642519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41377365189779069250190025 31033023892334301937642519)
            ·
              refine ⟨46549535838501452906463779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31033023892334301937642519 46549535838501452906463779)
              ·
                refine ⟨69824303757752179359695669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46549535838501452906463779 69824303757752179359695669)
                ·
                  refine ⟨6546028477289266814971469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69824303757752179359695669 6546028477289266814971469)
                  ·
                    refine ⟨2454760678983475055614301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6546028477289266814971469 2454760678983475055614301)
                    ·
                      refine ⟨920535254618803145855363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454760678983475055614301 920535254618803145855363)
                      ·
                        rfl

theorem cell23_1792736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1792736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792736 prefixEnd_1792736 := by exact prefixLift 1792736
  have htrace : WordTrace (prefixWord ++ tailWord_1792736) baseStart_1792736 baseEnd_1792736 := by
    simpa [prefixWord, tailWord_1792736, baseEnd_1792736] using wordTrace_append hprefix tailTrace_1792736
  have hstable : (prefixWord ++ tailWord_1792736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792736).length < 2 ^ (prefixWord ++ tailWord_1792736).sum := by decide
  have hdescent : baseEnd_1792736 < baseStart_1792736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792753 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_1792753 : Nat := 118140960795 + 1792753 * 2 ^ 59
def prefixEnd_1792753 : Nat := 4983230072969 + 3 ^ 40 * 1792753 * 2
def baseEnd_1792753 : Nat := 920543983789929579342785

theorem tailTrace_1792753 : CollatzResearch.WordTrace tailWord_1792753 prefixEnd_1792753 920543983789929579342785 := by
  unfold tailWord_1792753
  simp only [CollatzResearch.WordTrace]
  refine ⟨65387073674169533681446913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43591382449446355787631275 65387073674169533681446913)
  ·
    refine ⟨49040305255627150261085185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65387073674169533681446913 49040305255627150261085185)
    ·
      refine ⟨36780228941720362695813889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49040305255627150261085185 36780228941720362695813889)
      ·
        refine ⟨27585171706290272021860417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36780228941720362695813889 27585171706290272021860417)
        ·
          refine ⟨20688878779717704016395313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27585171706290272021860417 20688878779717704016395313)
          ·
            refine ⟨15516659084788278012296485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20688878779717704016395313 15516659084788278012296485)
            ·
              refine ⟨2909373578397802127305591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15516659084788278012296485 2909373578397802127305591)
              ·
                refine ⟨4364060367596703190958387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909373578397802127305591 4364060367596703190958387)
                ·
                  refine ⟨6546090551395054786437581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364060367596703190958387 6546090551395054786437581)
                  ·
                    refine ⟨2454783956773145544914093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6546090551395054786437581 2454783956773145544914093)
                    ·
                      refine ⟨920543983789929579342785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454783956773145544914093 920543983789929579342785)
                      ·
                        rfl

theorem cell23_1792753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_1792753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792753 prefixEnd_1792753 := by exact prefixLift 1792753
  have htrace : WordTrace (prefixWord ++ tailWord_1792753) baseStart_1792753 baseEnd_1792753 := by
    simpa [prefixWord, tailWord_1792753, baseEnd_1792753] using wordTrace_append hprefix tailTrace_1792753
  have hstable : (prefixWord ++ tailWord_1792753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792753).length < 2 ^ (prefixWord ++ tailWord_1792753).sum := by decide
  have hdescent : baseEnd_1792753 < baseStart_1792753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792770 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1792770 : Nat := 118140960795 + 1792770 * 2 ^ 59
def prefixEnd_1792770 : Nat := 4983230072969 + 3 ^ 40 * 1792770 * 2
def baseEnd_1792770 : Nat := 920552712961056012830207

theorem tailTrace_1792770 : CollatzResearch.WordTrace tailWord_1792770 prefixEnd_1792770 920552712961056012830207 := by
  unfold tailWord_1792770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16346923428776986396203941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43591795810071963723210509 16346923428776986396203941)
  ·
    refine ⟨3065048142895684949288239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16346923428776986396203941 3065048142895684949288239)
    ·
      refine ⟨4597572214343527423932359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065048142895684949288239 4597572214343527423932359)
      ·
        refine ⟨6896358321515291135898539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597572214343527423932359 6896358321515291135898539)
        ·
          refine ⟨10344537482272936703847809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896358321515291135898539 10344537482272936703847809)
          ·
            refine ⟨7758403111704702527885857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10344537482272936703847809 7758403111704702527885857)
            ·
              refine ⟨5818802333778526895914393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7758403111704702527885857 5818802333778526895914393)
              ·
                refine ⟨4364101750333895171935795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818802333778526895914393 4364101750333895171935795)
                ·
                  refine ⟨6546152625500842757903693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364101750333895171935795 6546152625500842757903693)
                  ·
                    refine ⟨2454807234562816034213885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6546152625500842757903693 2454807234562816034213885)
                    ·
                      refine ⟨920552712961056012830207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454807234562816034213885 920552712961056012830207)
                      ·
                        rfl

theorem cell23_1792770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1792770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792770 prefixEnd_1792770 := by exact prefixLift 1792770
  have htrace : WordTrace (prefixWord ++ tailWord_1792770) baseStart_1792770 baseEnd_1792770 := by
    simpa [prefixWord, tailWord_1792770, baseEnd_1792770] using wordTrace_append hprefix tailTrace_1792770
  have hstable : (prefixWord ++ tailWord_1792770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792770).length < 2 ^ (prefixWord ++ tailWord_1792770).sum := by decide
  have hdescent : baseEnd_1792770 < baseStart_1792770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792804 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_1792804 : Nat := 118140960795 + 1792804 * 2 ^ 59
def prefixEnd_1792804 : Nat := 4983230072969 + 3 ^ 40 * 1792804 * 2
def baseEnd_1792804 : Nat := 920570171303308879805051

theorem tailTrace_1792804 : CollatzResearch.WordTrace tailWord_1792804 prefixEnd_1792804 920570171303308879805051 := by
  unfold tailWord_1792804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32694466898492384695776733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43592622531323179594368977 32694466898492384695776733)
  ·
    refine ⟨12260425086934644260916275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32694466898492384695776733 12260425086934644260916275)
    ·
      refine ⟨18390637630401966391374413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12260425086934644260916275 18390637630401966391374413)
      ·
        refine ⟨6896489111400737396765405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18390637630401966391374413 6896489111400737396765405)
        ·
          refine ⟨2586183416775276523787027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6896489111400737396765405 2586183416775276523787027)
          ·
            refine ⟨3879275125162914785680541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586183416775276523787027 3879275125162914785680541)
            ·
              refine ⟨1454728171936093044630203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879275125162914785680541 1454728171936093044630203)
              ·
                refine ⟨2182092257904139566945305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454728171936093044630203 2182092257904139566945305)
                ·
                  refine ⟨1636569193428104675208979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2182092257904139566945305 1636569193428104675208979)
                  ·
                    refine ⟨2454853790142157012813469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1636569193428104675208979 2454853790142157012813469)
                    ·
                      refine ⟨920570171303308879805051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2454853790142157012813469 920570171303308879805051)
                      ·
                        rfl

theorem cell23_1792804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_1792804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792804 prefixEnd_1792804 := by exact prefixLift 1792804
  have htrace : WordTrace (prefixWord ++ tailWord_1792804) baseStart_1792804 baseEnd_1792804 := by
    simpa [prefixWord, tailWord_1792804, baseEnd_1792804] using wordTrace_append hprefix tailTrace_1792804
  have hstable : (prefixWord ++ tailWord_1792804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792804).length < 2 ^ (prefixWord ++ tailWord_1792804).sum := by decide
  have hdescent : baseEnd_1792804 < baseStart_1792804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792814 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1792814 : Nat := 118140960795 + 1792814 * 2 ^ 59
def prefixEnd_1792814 : Nat := 4983230072969 + 3 ^ 40 * 1792814 * 2
def baseEnd_1792814 : Nat := 920575306109853840680005

theorem tailTrace_1792814 : CollatzResearch.WordTrace tailWord_1792814 prefixEnd_1792814 920575306109853840680005 := by
  unfold tailWord_1792814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173662315868567637427187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43592865684632360732944997 8173662315868567637427187)
  ·
    refine ⟨12260493473802851456140781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8173662315868567637427187 12260493473802851456140781)
    ·
      refine ⟨4597685052676069296052793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12260493473802851456140781 4597685052676069296052793)
      ·
        refine ⟨3448263789507051972039595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4597685052676069296052793 3448263789507051972039595)
        ·
          refine ⟨5172395684260577958059393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448263789507051972039595 5172395684260577958059393)
          ·
            refine ⟨3879296763195433468544545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5172395684260577958059393 3879296763195433468544545)
            ·
              refine ⟨2909472572396575101408409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3879296763195433468544545 2909472572396575101408409)
              ·
                refine ⟨2182104429297431326056307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909472572396575101408409 2182104429297431326056307)
                ·
                  refine ⟨3273156643946146989084461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182104429297431326056307 3273156643946146989084461)
                  ·
                    refine ⟨1227433741479805120906673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273156643946146989084461 1227433741479805120906673)
                    ·
                      refine ⟨920575306109853840680005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227433741479805120906673 920575306109853840680005)
                      ·
                        rfl

theorem cell23_1792814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1792814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792814 prefixEnd_1792814 := by exact prefixLift 1792814
  have htrace : WordTrace (prefixWord ++ tailWord_1792814) baseStart_1792814 baseEnd_1792814 := by
    simpa [prefixWord, tailWord_1792814, baseEnd_1792814] using wordTrace_append hprefix tailTrace_1792814
  have hstable : (prefixWord ++ tailWord_1792814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792814).length < 2 ^ (prefixWord ++ tailWord_1792814).sum := by decide
  have hdescent : baseEnd_1792814 < baseStart_1792814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792830 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1792830 : Nat := 118140960795 + 1792830 * 2 ^ 59
def prefixEnd_1792830 : Nat := 4983230072969 + 3 ^ 40 * 1792830 * 2
def baseEnd_1792830 : Nat := 920583521800325778079931

theorem tailTrace_1792830 : CollatzResearch.WordTrace tailWord_1792830 prefixEnd_1792830 920583521800325778079931 := by
  unfold tailWord_1792830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173735261861321978999993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43593254729927050554666629 8173735261861321978999993)
  ·
    refine ⟨6130301446395991484249995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8173735261861321978999993 6130301446395991484249995)
    ·
      refine ⟨9195452169593987226374993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6130301446395991484249995 9195452169593987226374993)
      ·
        refine ⟨6896589127195490419781245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9195452169593987226374993 6896589127195490419781245)
        ·
          refine ⟨2586220922698308907417967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6896589127195490419781245 2586220922698308907417967)
          ·
            refine ⟨3879331384047463361126951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586220922698308907417967 3879331384047463361126951)
            ·
              refine ⟨5818997076071195041690427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879331384047463361126951 5818997076071195041690427)
              ·
                refine ⟨8728495614106792562535641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818997076071195041690427 8728495614106792562535641)
                ·
                  refine ⟨6546371710580094421901731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8728495614106792562535641 6546371710580094421901731)
                  ·
                    refine ⟨9819557565870141632852597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6546371710580094421901731 9819557565870141632852597)
                    ·
                      refine ⟨920583521800325778079931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9819557565870141632852597 920583521800325778079931)
                      ·
                        rfl

theorem cell23_1792830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1792830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792830 prefixEnd_1792830 := by exact prefixLift 1792830
  have htrace : WordTrace (prefixWord ++ tailWord_1792830) baseStart_1792830 baseEnd_1792830 := by
    simpa [prefixWord, tailWord_1792830, baseEnd_1792830] using wordTrace_append hprefix tailTrace_1792830
  have hstable : (prefixWord ++ tailWord_1792830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792830).length < 2 ^ (prefixWord ++ tailWord_1792830).sum := by decide
  have hdescent : baseEnd_1792830 < baseStart_1792830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792883 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4]
def baseStart_1792883 : Nat := 118140960795 + 1792883 * 2 ^ 59
def prefixEnd_1792883 : Nat := 4983230072969 + 3 ^ 40 * 1792883 * 2
def baseEnd_1792883 : Nat := 920610736275014070717187

theorem tailTrace_1792883 : CollatzResearch.WordTrace tailWord_1792883 prefixEnd_1792883 920610736275014070717187 := by
  unfold tailWord_1792883
  simp only [CollatzResearch.WordTrace]
  refine ⟨65391815163698565883679303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43594543442465710589119535 65391815163698565883679303)
  ·
    refine ⟨98087722745547848825518955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65391815163698565883679303 98087722745547848825518955)
    ·
      refine ⟨147131584118321773238278433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98087722745547848825518955 147131584118321773238278433)
      ·
        refine ⟨110348688088741329928708825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147131584118321773238278433 110348688088741329928708825)
        ·
          refine ⟨82761516066555997446531619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110348688088741329928708825 82761516066555997446531619)
          ·
            refine ⟨124142274099833996169797429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82761516066555997446531619 124142274099833996169797429)
            ·
              refine ⟨11638338196859437140918509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124142274099833996169797429 11638338196859437140918509)
              ·
                refine ⟨4364376823822288927844441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11638338196859437140918509 4364376823822288927844441)
                ·
                  refine ⟨3273282617866716695883331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4364376823822288927844441 3273282617866716695883331)
                  ·
                    refine ⟨4909923926800075043824997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3273282617866716695883331 4909923926800075043824997)
                    ·
                      refine ⟨920610736275014070717187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4909923926800075043824997 920610736275014070717187)
                      ·
                        rfl

theorem cell23_1792883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_1792883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792883 prefixEnd_1792883 := by exact prefixLift 1792883
  have htrace : WordTrace (prefixWord ++ tailWord_1792883) baseStart_1792883 baseEnd_1792883 := by
    simpa [prefixWord, tailWord_1792883, baseEnd_1792883] using wordTrace_append hprefix tailTrace_1792883
  have hstable : (prefixWord ++ tailWord_1792883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792883).length < 2 ^ (prefixWord ++ tailWord_1792883).sum := by decide
  have hdescent : baseEnd_1792883 < baseStart_1792883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792900 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1792900 : Nat := 118140960795 + 1792900 * 2 ^ 59
def prefixEnd_1792900 : Nat := 4983230072969 + 3 ^ 40 * 1792900 * 2
def baseEnd_1792900 : Nat := 920619465446140504204609

theorem tailTrace_1792900 : CollatzResearch.WordTrace tailWord_1792900 prefixEnd_1792900 920619465446140504204609 := by
  unfold tailWord_1792900
  simp only [CollatzResearch.WordTrace]
  refine ⟨32696217602318488893524077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43594956803091318524698769 32696217602318488893524077)
  ·
    refine ⟨12261081600869433335071529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32696217602318488893524077 12261081600869433335071529)
    ·
      refine ⟨9195811200652075001303647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12261081600869433335071529 9195811200652075001303647)
      ·
        refine ⟨13793716800978112501955471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9195811200652075001303647 13793716800978112501955471)
        ·
          refine ⟨20690575201467168752933207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13793716800978112501955471 20690575201467168752933207)
          ·
            refine ⟨31035862802200753129399811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20690575201467168752933207 31035862802200753129399811)
            ·
              refine ⟨46553794203301129694099717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31035862802200753129399811 46553794203301129694099717)
              ·
                refine ⟨8728836413118961817643697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46553794203301129694099717 8728836413118961817643697)
                ·
                  refine ⟨6546627309839221363232773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8728836413118961817643697 6546627309839221363232773)
                  ·
                    refine ⟨1227492620594854005606145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546627309839221363232773 1227492620594854005606145)
                    ·
                      refine ⟨920619465446140504204609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227492620594854005606145 920619465446140504204609)
                      ·
                        rfl

theorem cell23_1792900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1792900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792900 prefixEnd_1792900 := by exact prefixLift 1792900
  have htrace : WordTrace (prefixWord ++ tailWord_1792900) baseStart_1792900 baseEnd_1792900 := by
    simpa [prefixWord, tailWord_1792900, baseEnd_1792900] using wordTrace_append hprefix tailTrace_1792900
  have hstable : (prefixWord ++ tailWord_1792900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792900).length < 2 ^ (prefixWord ++ tailWord_1792900).sum := by decide
  have hdescent : baseEnd_1792900 < baseStart_1792900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792957 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 6]
def baseStart_1792957 : Nat := 118140960795 + 1792957 * 2 ^ 59
def prefixEnd_1792957 : Nat := 4983230072969 + 3 ^ 40 * 1792957 * 2
def baseEnd_1792957 : Nat := 102294303760382975687983

theorem tailTrace_1792957 : CollatzResearch.WordTrace tailWord_1792957 prefixEnd_1792957 102294303760382975687983 := by
  unfold tailWord_1792957
  simp only [CollatzResearch.WordTrace]
  refine ⟨65394514165430476521873125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43596342776953651014582083 65394514165430476521873125)
  ·
    refine ⟨12261471406018214347851211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65394514165430476521873125 12261471406018214347851211)
    ·
      refine ⟨18392207109027321521776817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12261471406018214347851211 18392207109027321521776817)
      ·
        refine ⟨13794155331770491141332613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18392207109027321521776817 13794155331770491141332613)
        ·
          refine ⟨2586404124706967088999865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13794155331770491141332613 2586404124706967088999865)
          ·
            refine ⟨1939803093530225316749899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586404124706967088999865 1939803093530225316749899)
            ·
              refine ⟨2909704640295337975124849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939803093530225316749899 2909704640295337975124849)
              ·
                refine ⟨2182278480221503481343637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909704640295337975124849 2182278480221503481343637)
                ·
                  refine ⟨102294303760382975687983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2182278480221503481343637 102294303760382975687983)
                  ·
                    rfl

theorem cell23_1792957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_1792957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792957 prefixEnd_1792957 := by exact prefixLift 1792957
  have htrace : WordTrace (prefixWord ++ tailWord_1792957) baseStart_1792957 baseEnd_1792957 := by
    simpa [prefixWord, tailWord_1792957, baseEnd_1792957] using wordTrace_append hprefix tailTrace_1792957
  have hstable : (prefixWord ++ tailWord_1792957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792957).length < 2 ^ (prefixWord ++ tailWord_1792957).sum := by decide
  have hdescent : baseEnd_1792957 < baseStart_1792957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792983 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 1, 6]
def baseStart_1792983 : Nat := 118140960795 + 1792983 * 2 ^ 59
def prefixEnd_1792983 : Nat := 4983230072969 + 3 ^ 40 * 1792983 * 2
def baseEnd_1792983 : Nat := 306887361446821226488909

theorem tailTrace_1792983 : CollatzResearch.WordTrace tailWord_1792983 prefixEnd_1792983 306887361446821226488909 := by
  unfold tailWord_1792983
  simp only [CollatzResearch.WordTrace]
  refine ⟨65395462463336282962319603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43596974975557521974879735 65395462463336282962319603)
  ·
    refine ⟨98093193695004424443479405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65395462463336282962319603 98093193695004424443479405)
    ·
      refine ⟨36784947635626659166304777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98093193695004424443479405 36784947635626659166304777)
      ·
        refine ⟨27588710726719994374728583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36784947635626659166304777 27588710726719994374728583)
        ·
          refine ⟨41383066090079991562092875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27588710726719994374728583 41383066090079991562092875)
          ·
            refine ⟨62074599135119987343139313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41383066090079991562092875 62074599135119987343139313)
            ·
              refine ⟨46555949351339990507354485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62074599135119987343139313 46555949351339990507354485)
              ·
                refine ⟨4364620251688124110064483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46555949351339990507354485 4364620251688124110064483)
                ·
                  refine ⟨6546930377532186165096725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364620251688124110064483 6546930377532186165096725)
                  ·
                    refine ⟨306887361446821226488909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6546930377532186165096725 306887361446821226488909)
                    ·
                      rfl

theorem cell23_1792983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_1792983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792983 prefixEnd_1792983 := by exact prefixLift 1792983
  have htrace : WordTrace (prefixWord ++ tailWord_1792983) baseStart_1792983 baseEnd_1792983 := by
    simpa [prefixWord, tailWord_1792983, baseEnd_1792983] using wordTrace_append hprefix tailTrace_1792983
  have hstable : (prefixWord ++ tailWord_1792983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792983).length < 2 ^ (prefixWord ++ tailWord_1792983).sum := by decide
  have hdescent : baseEnd_1792983 < baseStart_1792983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792993 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1792993 : Nat := 118140960795 + 1792993 * 2 ^ 59
def prefixEnd_1792993 : Nat := 4983230072969 + 3 ^ 40 * 1792993 * 2
def baseEnd_1792993 : Nat := 920667219147008640341681

theorem tailTrace_1792993 : CollatzResearch.WordTrace tailWord_1792993 prefixEnd_1792993 920667219147008640341681 := by
  unfold tailWord_1792993
  simp only [CollatzResearch.WordTrace]
  refine ⟨65395827193300054670183633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43597218128866703113455755 65395827193300054670183633)
  ·
    refine ⟨49046870394975041002637725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65395827193300054670183633 49046870394975041002637725)
    ·
      refine ⟨18392576398115640375989147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49046870394975041002637725 18392576398115640375989147)
      ·
        refine ⟨27588864597173460563983721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18392576398115640375989147 27588864597173460563983721)
        ·
          refine ⟨20691648447880095422987791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27588864597173460563983721 20691648447880095422987791)
          ·
            refine ⟨31037472671820143134481687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20691648447880095422987791 31037472671820143134481687)
            ·
              refine ⟨46556209007730214701722531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31037472671820143134481687 46556209007730214701722531)
              ·
                refine ⟨69834313511595322052583797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46556209007730214701722531 69834313511595322052583797)
                ·
                  refine ⟨6546966891712061442429731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69834313511595322052583797 6546966891712061442429731)
                  ·
                    refine ⟨9820450337568092163644597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6546966891712061442429731 9820450337568092163644597)
                    ·
                      refine ⟨920667219147008640341681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9820450337568092163644597 920667219147008640341681)
                      ·
                        rfl

theorem cell23_1792993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1792993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792993 prefixEnd_1792993 := by exact prefixLift 1792993
  have htrace : WordTrace (prefixWord ++ tailWord_1792993) baseStart_1792993 baseEnd_1792993 := by
    simpa [prefixWord, tailWord_1792993, baseEnd_1792993] using wordTrace_append hprefix tailTrace_1792993
  have hstable : (prefixWord ++ tailWord_1792993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792993).length < 2 ^ (prefixWord ++ tailWord_1792993).sum := by decide
  have hdescent : baseEnd_1792993 < baseStart_1792993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1792994 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1792994 : Nat := 118140960795 + 1792994 * 2 ^ 59
def prefixEnd_1792994 : Nat := 4983230072969 + 3 ^ 40 * 1792994 * 2
def baseEnd_1792994 : Nat := 920667732627663136429177

theorem tailTrace_1792994 : CollatzResearch.WordTrace tailWord_1792994 prefixEnd_1792994 920667732627663136429177 := by
  unfold tailWord_1792994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348965916574107960242509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43597242444197621227313357 16348965916574107960242509)
  ·
    refine ⟨6130862218715290485090941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16348965916574107960242509 6130862218715290485090941)
    ·
      refine ⟨2299073332018233931909103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6130862218715290485090941 2299073332018233931909103)
      ·
        refine ⟨3448609998027350897863655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299073332018233931909103 3448609998027350897863655)
        ·
          refine ⟨5172914997041026346795483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448609998027350897863655 5172914997041026346795483)
          ·
            refine ⟨7759372495561539520193225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172914997041026346795483 7759372495561539520193225)
            ·
              refine ⟨5819529371671154640144919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759372495561539520193225 5819529371671154640144919)
              ·
                refine ⟨8729294057506731960217379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5819529371671154640144919 8729294057506731960217379)
                ·
                  refine ⟨13093941086260097940326069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8729294057506731960217379 13093941086260097940326069)
                  ·
                    refine ⟨1227556976836884181905569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13093941086260097940326069 1227556976836884181905569)
                    ·
                      refine ⟨920667732627663136429177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227556976836884181905569 920667732627663136429177)
                      ·
                        rfl

theorem cell23_1792994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1792994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1792994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1792994 prefixEnd_1792994 := by exact prefixLift 1792994
  have htrace : WordTrace (prefixWord ++ tailWord_1792994) baseStart_1792994 baseEnd_1792994 := by
    simpa [prefixWord, tailWord_1792994, baseEnd_1792994] using wordTrace_append hprefix tailTrace_1792994
  have hstable : (prefixWord ++ tailWord_1792994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1792994).length < 2 ^ (prefixWord ++ tailWord_1792994).sum := by decide
  have hdescent : baseEnd_1792994 < baseStart_1792994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1792994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793000 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1793000 : Nat := 118140960795 + 1793000 * 2 ^ 59
def prefixEnd_1793000 : Nat := 4983230072969 + 3 ^ 40 * 1793000 * 2
def baseEnd_1793000 : Nat := 306890271170530037651383

theorem tailTrace_1793000 : CollatzResearch.WordTrace tailWord_1793000 prefixEnd_1793000 306890271170530037651383 := by
  unfold tailWord_1793000
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698041252137347432844227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43597388336183129910458969 32698041252137347432844227)
  ·
    refine ⟨49047061878206021149266341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32698041252137347432844227 49047061878206021149266341)
    ·
      refine ⟨9196324102163628965487439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49047061878206021149266341 9196324102163628965487439)
      ·
        refine ⟨13794486153245443448231159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9196324102163628965487439 13794486153245443448231159)
        ·
          refine ⟨20691729229868165172346739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13794486153245443448231159 20691729229868165172346739)
          ·
            refine ⟨31037593844802247758520109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20691729229868165172346739 31037593844802247758520109)
            ·
              refine ⟨11639097691800842909445041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31037593844802247758520109 11639097691800842909445041)
              ·
                refine ⟨8729323268850632182083781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11639097691800842909445041 8729323268850632182083781)
                ·
                  refine ⟨1636748112909493534140709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8729323268850632182083781 1636748112909493534140709)
                  ·
                    refine ⟨306890271170530037651383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636748112909493534140709 306890271170530037651383)
                    ·
                      rfl

theorem cell23_1793000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1793000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793000 prefixEnd_1793000 := by exact prefixLift 1793000
  have htrace : WordTrace (prefixWord ++ tailWord_1793000) baseStart_1793000 baseEnd_1793000 := by
    simpa [prefixWord, tailWord_1793000, baseEnd_1793000] using wordTrace_append hprefix tailTrace_1793000
  have hstable : (prefixWord ++ tailWord_1793000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793000).length < 2 ^ (prefixWord ++ tailWord_1793000).sum := by decide
  have hdescent : baseEnd_1793000 < baseStart_1793000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793012 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1793012 : Nat := 118140960795 + 1793012 * 2 ^ 59
def prefixEnd_1793012 : Nat := 4983230072969 + 3 ^ 40 * 1793012 * 2
def baseEnd_1793012 : Nat := 306892325093148022001365

theorem tailTrace_1793012 : CollatzResearch.WordTrace tailWord_1793012 prefixEnd_1793012 306892325093148022001365 := by
  unfold tailWord_1793012
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698260090115610457562645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43597680120154147276750193 32698260090115610457562645)
  ·
    refine ⟨1532730941724169240198249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32698260090115610457562645 1532730941724169240198249)
    ·
      refine ⟨1149548206293126930148687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1532730941724169240198249 1149548206293126930148687)
      ·
        refine ⟨1724322309439690395223031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149548206293126930148687 1724322309439690395223031)
        ·
          refine ⟨2586483464159535592834547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724322309439690395223031 2586483464159535592834547)
          ·
            refine ⟨3879725196239303389251821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586483464159535592834547 3879725196239303389251821)
            ·
              refine ⟨1454896948589738770969433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879725196239303389251821 1454896948589738770969433)
              ·
                refine ⟨1091172711442304078227075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454896948589738770969433 1091172711442304078227075)
                ·
                  refine ⟨1636759067163456117340613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091172711442304078227075 1636759067163456117340613)
                  ·
                    refine ⟨306892325093148022001365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636759067163456117340613 306892325093148022001365)
                    ·
                      rfl

theorem cell23_1793012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1793012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793012 prefixEnd_1793012 := by exact prefixLift 1793012
  have htrace : WordTrace (prefixWord ++ tailWord_1793012) baseStart_1793012 baseEnd_1793012 := by
    simpa [prefixWord, tailWord_1793012, baseEnd_1793012] using wordTrace_append hprefix tailTrace_1793012
  have hstable : (prefixWord ++ tailWord_1793012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793012).length < 2 ^ (prefixWord ++ tailWord_1793012).sum := by decide
  have hdescent : baseEnd_1793012 < baseStart_1793012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793034 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1793034 : Nat := 118140960795 + 1793034 * 2 ^ 59
def prefixEnd_1793034 : Nat := 4983230072969 + 3 ^ 40 * 1793034 * 2
def baseEnd_1793034 : Nat := 306896090617947659976331

theorem tailTrace_1793034 : CollatzResearch.WordTrace tailWord_1793034 prefixEnd_1793034 306896090617947659976331 := by
  unfold tailWord_1793034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349330646537879668106539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43598215057434345781617437 16349330646537879668106539)
  ·
    refine ⟨24523995969806819502159809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16349330646537879668106539 24523995969806819502159809)
    ·
      refine ⟨18392996977355114626619857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24523995969806819502159809 18392996977355114626619857)
      ·
        refine ⟨13794747733016335969964893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18392996977355114626619857 13794747733016335969964893)
        ·
          refine ⟨5173030399881125988736835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13794747733016335969964893 5173030399881125988736835)
          ·
            refine ⟨7759545599821688983105253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173030399881125988736835 7759545599821688983105253)
            ·
              refine ⟨1454914799966566684332235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7759545599821688983105253 1454914799966566684332235)
              ·
                refine ⟨2182372199949850026498353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454914799966566684332235 2182372199949850026498353)
                ·
                  refine ⟨1636779149962387519873765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2182372199949850026498353 1636779149962387519873765)
                  ·
                    refine ⟨306896090617947659976331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636779149962387519873765 306896090617947659976331)
                    ·
                      rfl

theorem cell23_1793034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1793034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793034 prefixEnd_1793034 := by exact prefixLift 1793034
  have htrace : WordTrace (prefixWord ++ tailWord_1793034) baseStart_1793034 baseEnd_1793034 := by
    simpa [prefixWord, tailWord_1793034, baseEnd_1793034] using wordTrace_append hprefix tailTrace_1793034
  have hstable : (prefixWord ++ tailWord_1793034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793034).length < 2 ^ (prefixWord ++ tailWord_1793034).sum := by decide
  have hdescent : baseEnd_1793034 < baseStart_1793034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793057 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1793057 : Nat := 118140960795 + 1793057 * 2 ^ 59
def prefixEnd_1793057 : Nat := 4983230072969 + 3 ^ 40 * 1793057 * 2
def baseEnd_1793057 : Nat := 920700081908896389941387

theorem tailTrace_1793057 : CollatzResearch.WordTrace tailWord_1793057 prefixEnd_1793057 920700081908896389941387 := by
  unfold tailWord_1793057
  simp only [CollatzResearch.WordTrace]
  refine ⟨65398161465068193600513425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43598774310045462400342283 65398161465068193600513425)
  ·
    refine ⟨49048621098801145200385069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65398161465068193600513425 49048621098801145200385069)
    ·
      refine ⟨18393232912050429450144401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49048621098801145200385069 18393232912050429450144401)
      ·
        refine ⟨13794924684037822087608301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18393232912050429450144401 13794924684037822087608301)
        ·
          refine ⟨5173096756514183282853113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13794924684037822087608301 5173096756514183282853113)
          ·
            refine ⟨3879822567385637462139835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5173096756514183282853113 3879822567385637462139835)
            ·
              refine ⟨5819733851078456193209753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879822567385637462139835 5819733851078456193209753)
              ·
                refine ⟨4364800388308842144907315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819733851078456193209753 4364800388308842144907315)
                ·
                  refine ⟨6547200582463263217360973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364800388308842144907315 6547200582463263217360973)
                  ·
                    refine ⟨2455200218423723706510365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6547200582463263217360973 2455200218423723706510365)
                    ·
                      refine ⟨920700081908896389941387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455200218423723706510365 920700081908896389941387)
                      ·
                        rfl

theorem cell23_1793057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1793057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793057 prefixEnd_1793057 := by exact prefixLift 1793057
  have htrace : WordTrace (prefixWord ++ tailWord_1793057) baseStart_1793057 baseEnd_1793057 := by
    simpa [prefixWord, tailWord_1793057, baseEnd_1793057] using wordTrace_append hprefix tailTrace_1793057
  have hstable : (prefixWord ++ tailWord_1793057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793057).length < 2 ^ (prefixWord ++ tailWord_1793057).sum := by decide
  have hdescent : baseEnd_1793057 < baseStart_1793057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793074 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_1793074 : Nat := 118140960795 + 1793074 * 2 ^ 59
def prefixEnd_1793074 : Nat := 4983230072969 + 3 ^ 40 * 1793074 * 2
def baseEnd_1793074 : Nat := 920708811080022823428809

theorem tailTrace_1793074 : CollatzResearch.WordTrace tailWord_1793074 prefixEnd_1793074 920708811080022823428809 := by
  unfold tailWord_1793074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349695376501651375970569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43599187670671070335921517 16349695376501651375970569)
  ·
    refine ⟨12262271532376238531977927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16349695376501651375970569 12262271532376238531977927)
    ·
      refine ⟨18393407298564357797966891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12262271532376238531977927 18393407298564357797966891)
      ·
        refine ⟨27590110947846536696950337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18393407298564357797966891 27590110947846536696950337)
        ·
          refine ⟨20692583210884902522712753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27590110947846536696950337 20692583210884902522712753)
          ·
            refine ⟨15519437408163676892034565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20692583210884902522712753 15519437408163676892034565)
            ·
              refine ⟨2909894514030689417256481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15519437408163676892034565 2909894514030689417256481)
              ·
                refine ⟨2182420885523017062942361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909894514030689417256481 2182420885523017062942361)
                ·
                  refine ⟨1636815664142262797206771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2182420885523017062942361 1636815664142262797206771)
                  ·
                    refine ⟨2455223496213394195810157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1636815664142262797206771 2455223496213394195810157)
                    ·
                      refine ⟨920708811080022823428809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455223496213394195810157 920708811080022823428809)
                      ·
                        rfl

theorem cell23_1793074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_1793074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793074 prefixEnd_1793074 := by exact prefixLift 1793074
  have htrace : WordTrace (prefixWord ++ tailWord_1793074) baseStart_1793074 baseEnd_1793074 := by
    simpa [prefixWord, tailWord_1793074, baseEnd_1793074] using wordTrace_append hprefix tailTrace_1793074
  have hstable : (prefixWord ++ tailWord_1793074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793074).length < 2 ^ (prefixWord ++ tailWord_1793074).sum := by decide
  have hdescent : baseEnd_1793074 < baseStart_1793074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793080 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1793080 : Nat := 118140960795 + 1793080 * 2 ^ 59
def prefixEnd_1793080 : Nat := 4983230072969 + 3 ^ 40 * 1793080 * 2
def baseEnd_1793080 : Nat := 920711891963949799953781

theorem tailTrace_1793080 : CollatzResearch.WordTrace tailWord_1793080 prefixEnd_1793080 920711891963949799953781 := by
  unfold tailWord_1793080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32699500171992434264300347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43599333562656579019067129 32699500171992434264300347)
  ·
    refine ⟨49049250257988651396450521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32699500171992434264300347 49049250257988651396450521)
    ·
      refine ⟨36786937693491488547337891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49049250257988651396450521 36786937693491488547337891)
      ·
        refine ⟨55180406540237232821006837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36786937693491488547337891 55180406540237232821006837)
        ·
          refine ⟨5173163113147240576969391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55180406540237232821006837 5173163113147240576969391)
          ·
            refine ⟨7759744669720860865454087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173163113147240576969391 7759744669720860865454087)
            ·
              refine ⟨11639617004581291298181131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759744669720860865454087 11639617004581291298181131)
              ·
                refine ⟨17459425506871936947271697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639617004581291298181131 17459425506871936947271697)
                ·
                  refine ⟨13094569130153952710453773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17459425506871936947271697 13094569130153952710453773)
                  ·
                    refine ⟨4910463423807732266420165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13094569130153952710453773 4910463423807732266420165)
                    ·
                      refine ⟨920711891963949799953781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4910463423807732266420165 920711891963949799953781)
                      ·
                        rfl

theorem cell23_1793080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1793080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793080 prefixEnd_1793080 := by exact prefixLift 1793080
  have htrace : WordTrace (prefixWord ++ tailWord_1793080) baseStart_1793080 baseEnd_1793080 := by
    simpa [prefixWord, tailWord_1793080, baseEnd_1793080] using wordTrace_append hprefix tailTrace_1793080
  have hstable : (prefixWord ++ tailWord_1793080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793080).length < 2 ^ (prefixWord ++ tailWord_1793080).sum := by decide
  have hdescent : baseEnd_1793080 < baseStart_1793080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793100 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1793100 : Nat := 118140960795 + 1793100 * 2 ^ 59
def prefixEnd_1793100 : Nat := 4983230072969 + 3 ^ 40 * 1793100 * 2
def baseEnd_1793100 : Nat := 920722161577039721703689

theorem tailTrace_1793100 : CollatzResearch.WordTrace tailWord_1793100 prefixEnd_1793100 920722161577039721703689 := by
  unfold tailWord_1793100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32699864901956205972164377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43599819869274941296219169 32699864901956205972164377)
  ·
    refine ⟨24524898676467154479123283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32699864901956205972164377 24524898676467154479123283)
    ·
      refine ⟨36787348014700731718684925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24524898676467154479123283 36787348014700731718684925)
      ·
        refine ⟨13795255505512774394506847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36787348014700731718684925 13795255505512774394506847)
        ·
          refine ⟨20692883258269161591760271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795255505512774394506847 20692883258269161591760271)
          ·
            refine ⟨31039324887403742387640407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20692883258269161591760271 31039324887403742387640407)
            ·
              refine ⟨46558987331105613581460611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31039324887403742387640407 46558987331105613581460611)
              ·
                refine ⟨69838480996658420372190917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46558987331105613581460611 69838480996658420372190917)
                ·
                  refine ⟨13094715186873453819785797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69838480996658420372190917 13094715186873453819785797)
                  ·
                    refine ⟨2455259097538772591209837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13094715186873453819785797 2455259097538772591209837)
                    ·
                      refine ⟨920722161577039721703689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455259097538772591209837 920722161577039721703689)
                      ·
                        rfl

theorem cell23_1793100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1793100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793100 prefixEnd_1793100 := by exact prefixLift 1793100
  have htrace : WordTrace (prefixWord ++ tailWord_1793100) baseStart_1793100 baseEnd_1793100 := by
    simpa [prefixWord, tailWord_1793100, baseEnd_1793100] using wordTrace_append hprefix tailTrace_1793100
  have hstable : (prefixWord ++ tailWord_1793100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793100).length < 2 ^ (prefixWord ++ tailWord_1793100).sum := by decide
  have hdescent : baseEnd_1793100 < baseStart_1793100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793187 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 4, 4, 2]
def baseStart_1793187 : Nat := 118140960795 + 1793187 * 2 ^ 59
def prefixEnd_1793187 : Nat := 4983230072969 + 3 ^ 40 * 1793187 * 2
def baseEnd_1793187 : Nat := 920766834393980881315789

theorem tailTrace_1793187 : CollatzResearch.WordTrace tailWord_1793187 prefixEnd_1793187 920766834393980881315789 := by
  unfold tailWord_1793187
  simp only [CollatzResearch.WordTrace]
  refine ⟨65402902954597225802745815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43601935303064817201830543 65402902954597225802745815)
  ·
    refine ⟨98104354431895838704118723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65402902954597225802745815 98104354431895838704118723)
    ·
      refine ⟨147156531647843758056178085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98104354431895838704118723 147156531647843758056178085)
      ·
        refine ⟨27591849683970704635533391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147156531647843758056178085 27591849683970704635533391)
        ·
          refine ⟨41387774525956056953300087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27591849683970704635533391 41387774525956056953300087)
          ·
            refine ⟨62081661788934085429950131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41387774525956056953300087 62081661788934085429950131)
            ·
              refine ⟨93122492683401128144925197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62081661788934085429950131 93122492683401128144925197)
              ·
                refine ⟨34920934756275423054346949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93122492683401128144925197 34920934756275423054346949)
                ·
                  refine ⟨6547675266801641822690053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34920934756275423054346949 6547675266801641822690053)
                  ·
                    refine ⟨1227689112525307841754385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547675266801641822690053 1227689112525307841754385)
                    ·
                      refine ⟨920766834393980881315789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227689112525307841754385 920766834393980881315789)
                      ·
                        rfl

theorem cell23_1793187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_1793187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793187 prefixEnd_1793187 := by exact prefixLift 1793187
  have htrace : WordTrace (prefixWord ++ tailWord_1793187) baseStart_1793187 baseEnd_1793187 := by
    simpa [prefixWord, tailWord_1793187, baseEnd_1793187] using wordTrace_append hprefix tailTrace_1793187
  have hstable : (prefixWord ++ tailWord_1793187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793187).length < 2 ^ (prefixWord ++ tailWord_1793187).sum := by decide
  have hdescent : baseEnd_1793187 < baseStart_1793187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793194 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1793194 : Nat := 118140960795 + 1793194 * 2 ^ 59
def prefixEnd_1793194 : Nat := 4983230072969 + 3 ^ 40 * 1793194 * 2
def baseEnd_1793194 : Nat := 920770428758562353928257

theorem tailTrace_1793194 : CollatzResearch.WordTrace tailWord_1793194 prefixEnd_1793194 920770428758562353928257 := by
  unfold tailWord_1793194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350789566392966499562659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43602105510381243998833757 16350789566392966499562659)
  ·
    refine ⟨24526184349589449749343989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350789566392966499562659 24526184349589449749343989)
    ·
      refine ⟨2299329782774010914000999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24526184349589449749343989 2299329782774010914000999)
      ·
        refine ⟨3448994674161016371001499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299329782774010914000999 3448994674161016371001499)
        ·
          refine ⟨5173492011241524556502249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448994674161016371001499 5173492011241524556502249)
          ·
            refine ⟨3880119008431143417376687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5173492011241524556502249 3880119008431143417376687)
            ·
              refine ⟨5820178512646715126065031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880119008431143417376687 5820178512646715126065031)
              ·
                refine ⟨8730267768970072689097547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820178512646715126065031 8730267768970072689097547)
                ·
                  refine ⟨13095401653455109033646321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730267768970072689097547 13095401653455109033646321)
                  ·
                    refine ⟨9821551240091331775234741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13095401653455109033646321 9821551240091331775234741)
                    ·
                      refine ⟨920770428758562353928257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9821551240091331775234741 920770428758562353928257)
                      ·
                        rfl

theorem cell23_1793194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1793194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793194 prefixEnd_1793194 := by exact prefixLift 1793194
  have htrace : WordTrace (prefixWord ++ tailWord_1793194) baseStart_1793194 baseEnd_1793194 := by
    simpa [prefixWord, tailWord_1793194, baseEnd_1793194] using wordTrace_append hprefix tailTrace_1793194
  have hstable : (prefixWord ++ tailWord_1793194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793194).length < 2 ^ (prefixWord ++ tailWord_1793194).sum := by decide
  have hdescent : baseEnd_1793194 < baseStart_1793194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793207 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1793207 : Nat := 118140960795 + 1793207 * 2 ^ 59
def prefixEnd_1793207 : Nat := 4983230072969 + 3 ^ 40 * 1793207 * 2
def baseEnd_1793207 : Nat := 920777104007070803065697

theorem tailTrace_1793207 : CollatzResearch.WordTrace tailWord_1793207 prefixEnd_1793207 920777104007070803065697 := by
  unfold tailWord_1793207
  simp only [CollatzResearch.WordTrace]
  refine ⟨65403632414524769218473875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43602421609683179478982583 65403632414524769218473875)
  ·
    refine ⟨98105448621787153827710813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65403632414524769218473875 98105448621787153827710813)
    ·
      refine ⟨36789543233170182685391555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98105448621787153827710813 36789543233170182685391555)
      ·
        refine ⟨55184314849755274028087333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36789543233170182685391555 55184314849755274028087333)
        ·
          refine ⟨10347059034329113880266375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55184314849755274028087333 10347059034329113880266375)
          ·
            refine ⟨15520588551493670820399563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347059034329113880266375 15520588551493670820399563)
            ·
              refine ⟨23280882827240506230599345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15520588551493670820399563 23280882827240506230599345)
              ·
                refine ⟨17460662120430379672949509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23280882827240506230599345 17460662120430379672949509)
                ·
                  refine ⟨3273874147580696188678033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17460662120430379672949509 3273874147580696188678033)
                  ·
                    refine ⟨2455405610685522141508525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3273874147580696188678033 2455405610685522141508525)
                    ·
                      refine ⟨920777104007070803065697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455405610685522141508525 920777104007070803065697)
                      ·
                        rfl

theorem cell23_1793207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1793207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793207 prefixEnd_1793207 := by exact prefixLift 1793207
  have htrace : WordTrace (prefixWord ++ tailWord_1793207) baseStart_1793207 baseEnd_1793207 := by
    simpa [prefixWord, tailWord_1793207, baseEnd_1793207] using wordTrace_append hprefix tailTrace_1793207
  have hstable : (prefixWord ++ tailWord_1793207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793207).length < 2 ^ (prefixWord ++ tailWord_1793207).sum := by decide
  have hdescent : baseEnd_1793207 < baseStart_1793207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793218 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1793218 : Nat := 118140960795 + 1793218 * 2 ^ 59
def prefixEnd_1793218 : Nat := 4983230072969 + 3 ^ 40 * 1793218 * 2
def baseEnd_1793218 : Nat := 306927584098090086676049

theorem tailTrace_1793218 : CollatzResearch.WordTrace tailWord_1793218 prefixEnd_1793218 306927584098090086676049 := by
  unfold tailWord_1793218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351008404371229524281077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43602689078323278731416205 16351008404371229524281077)
  ·
    refine ⟨1532907037909802767901351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16351008404371229524281077 1532907037909802767901351)
    ·
      refine ⟨2299360556864704151852027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532907037909802767901351 2299360556864704151852027)
      ·
        refine ⟨3449040835297056227778041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299360556864704151852027 3449040835297056227778041)
        ·
          refine ⟨2586780626472792170833531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3449040835297056227778041 2586780626472792170833531)
          ·
            refine ⟨3880170939709188256250297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586780626472792170833531 3880170939709188256250297)
            ·
              refine ⟨2910128204781891192187723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880170939709188256250297 2910128204781891192187723)
              ·
                refine ⟨4365192307172836788281585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910128204781891192187723 4365192307172836788281585)
                ·
                  refine ⟨3273894230379627591211189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4365192307172836788281585 3273894230379627591211189)
                  ·
                    refine ⟨306927584098090086676049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3273894230379627591211189 306927584098090086676049)
                    ·
                      rfl

theorem cell23_1793218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1793218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793218 prefixEnd_1793218 := by exact prefixLift 1793218
  have htrace : WordTrace (prefixWord ++ tailWord_1793218) baseStart_1793218 baseEnd_1793218 := by
    simpa [prefixWord, tailWord_1793218, baseEnd_1793218] using wordTrace_append hprefix tailTrace_1793218
  have hstable : (prefixWord ++ tailWord_1793218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793218).length < 2 ^ (prefixWord ++ tailWord_1793218).sum := by decide
  have hdescent : baseEnd_1793218 < baseStart_1793218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793248 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 1, 4]
def baseStart_1793248 : Nat := 118140960795 + 1793248 * 2 ^ 59
def prefixEnd_1793248 : Nat := 4983230072969 + 3 ^ 40 * 1793248 * 2
def baseEnd_1793248 : Nat := 306932718904635047551003

theorem tailTrace_1793248 : CollatzResearch.WordTrace tailWord_1793248 prefixEnd_1793248 306932718904635047551003 := by
  unfold tailWord_1793248
  simp only [CollatzResearch.WordTrace]
  refine ⟨32702563903688116610358199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43603418538250822147144265 32702563903688116610358199)
  ·
    refine ⟨49053845855532174915537299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32702563903688116610358199 49053845855532174915537299)
    ·
      refine ⟨73580768783298262373305949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49053845855532174915537299 73580768783298262373305949)
      ·
        refine ⟨27592788293736848389989731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73580768783298262373305949 27592788293736848389989731)
        ·
          refine ⟨41389182440605272584984597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27592788293736848389989731 41389182440605272584984597)
          ·
            refine ⟨1940117926903372152421153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41389182440605272584984597 1940117926903372152421153)
            ·
              refine ⟨1455088445177529114315865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940117926903372152421153 1455088445177529114315865)
              ·
                refine ⟨1091316333883146835736899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455088445177529114315865 1091316333883146835736899)
                ·
                  refine ⟨1636974500824720253605349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091316333883146835736899 1636974500824720253605349)
                  ·
                    refine ⟨306932718904635047551003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636974500824720253605349 306932718904635047551003)
                    ·
                      rfl

theorem cell23_1793248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 4].length) (baseStart_1793248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793248 prefixEnd_1793248 := by exact prefixLift 1793248
  have htrace : WordTrace (prefixWord ++ tailWord_1793248) baseStart_1793248 baseEnd_1793248 := by
    simpa [prefixWord, tailWord_1793248, baseEnd_1793248] using wordTrace_append hprefix tailTrace_1793248
  have hstable : (prefixWord ++ tailWord_1793248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793248).length < 2 ^ (prefixWord ++ tailWord_1793248).sum := by decide
  have hdescent : baseEnd_1793248 < baseStart_1793248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793281 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_1793281 : Nat := 118140960795 + 1793281 * 2 ^ 59
def prefixEnd_1793281 : Nat := 4983230072969 + 3 ^ 40 * 1793281 * 2
def baseEnd_1793281 : Nat := 920815101575503513540357

theorem tailTrace_1793281 : CollatzResearch.WordTrace tailWord_1793281 prefixEnd_1793281 920815101575503513540357 := by
  unfold tailWord_1793281
  simp only [CollatzResearch.WordTrace]
  refine ⟨65406331416256679856667697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43604220944171119904445131 65406331416256679856667697)
  ·
    refine ⟨49054748562192509892500773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65406331416256679856667697 49054748562192509892500773)
    ·
      refine ⟨9197765355411095604843895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49054748562192509892500773 9197765355411095604843895)
      ·
        refine ⟨13796648033116643407265843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197765355411095604843895 13796648033116643407265843)
        ·
          refine ⟨20694972049674965110898765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796648033116643407265843 20694972049674965110898765)
          ·
            refine ⟨7760614518628111916587037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20694972049674965110898765 7760614518628111916587037)
            ·
              refine ⟨2910230444485541968720139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7760614518628111916587037 2910230444485541968720139)
              ·
                refine ⟨4365345666728312953080209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910230444485541968720139 4365345666728312953080209)
                ·
                  refine ⟨3274009250046234714810157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4365345666728312953080209 3274009250046234714810157)
                  ·
                    refine ⟨1227753468767338018053809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274009250046234714810157 1227753468767338018053809)
                    ·
                      refine ⟨920815101575503513540357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227753468767338018053809 920815101575503513540357)
                      ·
                        rfl

theorem cell23_1793281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_1793281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793281 prefixEnd_1793281 := by exact prefixLift 1793281
  have htrace : WordTrace (prefixWord ++ tailWord_1793281) baseStart_1793281 baseEnd_1793281 := by
    simpa [prefixWord, tailWord_1793281, baseEnd_1793281] using wordTrace_append hprefix tailTrace_1793281
  have hstable : (prefixWord ++ tailWord_1793281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793281).length < 2 ^ (prefixWord ++ tailWord_1793281).sum := by decide
  have hdescent : baseEnd_1793281 < baseStart_1793281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793291 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 1, 5]
def baseStart_1793291 : Nat := 118140960795 + 1793291 * 2 ^ 59
def prefixEnd_1793291 : Nat := 4983230072969 + 3 ^ 40 * 1793291 * 2
def baseEnd_1793291 : Nat := 306940078794016158138437

theorem tailTrace_1793291 : CollatzResearch.WordTrace tailWord_1793291 prefixEnd_1793291 306940078794016158138437 := by
  unfold tailWord_1793291
  simp only [CollatzResearch.WordTrace]
  refine ⟨65406696146220451564531727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43604464097480301043021151 65406696146220451564531727)
  ·
    refine ⟨98110044219330677346797591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65406696146220451564531727 98110044219330677346797591)
    ·
      refine ⟨147165066328996016020196387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98110044219330677346797591 147165066328996016020196387)
      ·
        refine ⟨220747599493494024030294581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147165066328996016020196387 220747599493494024030294581)
        ·
          refine ⟨20695087452515064752840117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220747599493494024030294581 20695087452515064752840117)
          ·
            refine ⟨1940164448673287320578761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20695087452515064752840117 1940164448673287320578761)
            ·
              refine ⟨1455123336504965490434071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940164448673287320578761 1455123336504965490434071)
              ·
                refine ⟨2182685004757448235651107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455123336504965490434071 2182685004757448235651107)
                ·
                  refine ⟨3274027507136172353476661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182685004757448235651107 3274027507136172353476661)
                  ·
                    refine ⟨306940078794016158138437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3274027507136172353476661 306940078794016158138437)
                    ·
                      rfl

theorem cell23_1793291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 5].length) (baseStart_1793291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793291 prefixEnd_1793291 := by exact prefixLift 1793291
  have htrace : WordTrace (prefixWord ++ tailWord_1793291) baseStart_1793291 baseEnd_1793291 := by
    simpa [prefixWord, tailWord_1793291, baseEnd_1793291] using wordTrace_append hprefix tailTrace_1793291
  have hstable : (prefixWord ++ tailWord_1793291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793291).length < 2 ^ (prefixWord ++ tailWord_1793291).sum := by decide
  have hdescent : baseEnd_1793291 < baseStart_1793291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793297 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1793297 : Nat := 118140960795 + 1793297 * 2 ^ 59
def prefixEnd_1793297 : Nat := 4983230072969 + 3 ^ 40 * 1793297 * 2
def baseEnd_1793297 : Nat := 920823317265975450940283

theorem tailTrace_1793297 : CollatzResearch.WordTrace tailWord_1793297 prefixEnd_1793297 920823317265975450940283 := by
  unfold tailWord_1793297
  simp only [CollatzResearch.WordTrace]
  refine ⟨65406914984198714589250145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43604609989465809726166763 65406914984198714589250145)
  ·
    refine ⟨49055186238149035941937609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65406914984198714589250145 49055186238149035941937609)
    ·
      refine ⟨36791389678611776956453207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49055186238149035941937609 36791389678611776956453207)
      ·
        refine ⟨55187084517917665434679811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36791389678611776956453207 55187084517917665434679811)
        ·
          refine ⟨82780626776876498152019717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55187084517917665434679811 82780626776876498152019717)
          ·
            refine ⟨15521367520664343403503697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82780626776876498152019717 15521367520664343403503697)
            ·
              refine ⟨11641025640498257552627773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15521367520664343403503697 11641025640498257552627773)
              ·
                refine ⟨4365384615186846582235415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11641025640498257552627773 4365384615186846582235415)
                ·
                  refine ⟨6548076922780269873353123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365384615186846582235415 6548076922780269873353123)
                  ·
                    refine ⟨9822115384170404810029685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6548076922780269873353123 9822115384170404810029685)
                    ·
                      refine ⟨920823317265975450940283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9822115384170404810029685 920823317265975450940283)
                      ·
                        rfl

theorem cell23_1793297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1793297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793297 prefixEnd_1793297 := by exact prefixLift 1793297
  have htrace : WordTrace (prefixWord ++ tailWord_1793297) baseStart_1793297 baseEnd_1793297 := by
    simpa [prefixWord, tailWord_1793297, baseEnd_1793297] using wordTrace_append hprefix tailTrace_1793297
  have hstable : (prefixWord ++ tailWord_1793297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793297).length < 2 ^ (prefixWord ++ tailWord_1793297).sum := by decide
  have hdescent : baseEnd_1793297 < baseStart_1793297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793304 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_1793304 : Nat := 118140960795 + 1793304 * 2 ^ 59
def prefixEnd_1793304 : Nat := 4983230072969 + 3 ^ 40 * 1793304 * 2
def baseEnd_1793304 : Nat := 306942303876852307850917

theorem tailTrace_1793304 : CollatzResearch.WordTrace tailWord_1793304 prefixEnd_1793304 306942303876852307850917 := by
  unfold tailWord_1793304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703585147586677392377483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43604780196782236523169977 32703585147586677392377483)
  ·
    refine ⟨49055377721380016088566225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32703585147586677392377483 49055377721380016088566225)
    ·
      refine ⟨36791533291035012066424669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49055377721380016088566225 36791533291035012066424669)
      ·
        refine ⟨13796824984138129524909251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36791533291035012066424669 13796824984138129524909251)
        ·
          refine ⟨20695237476207194287363877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796824984138129524909251 20695237476207194287363877)
          ·
            refine ⟨3880357026788848928880727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20695237476207194287363877 3880357026788848928880727)
            ·
              refine ⟨5820535540183273393321091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880357026788848928880727 5820535540183273393321091)
              ·
                refine ⟨8730803310274910089981637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820535540183273393321091 8730803310274910089981637)
                ·
                  refine ⟨1637025620676545641871557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8730803310274910089981637 1637025620676545641871557)
                  ·
                    refine ⟨306942303876852307850917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1637025620676545641871557 306942303876852307850917)
                    ·
                      rfl

theorem cell23_1793304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_1793304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793304 prefixEnd_1793304 := by exact prefixLift 1793304
  have htrace : WordTrace (prefixWord ++ tailWord_1793304) baseStart_1793304 baseEnd_1793304 := by
    simpa [prefixWord, tailWord_1793304, baseEnd_1793304] using wordTrace_append hprefix tailTrace_1793304
  have hstable : (prefixWord ++ tailWord_1793304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793304).length < 2 ^ (prefixWord ++ tailWord_1793304).sum := by decide
  have hdescent : baseEnd_1793304 < baseStart_1793304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793331 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 3]
def baseStart_1793331 : Nat := 118140960795 + 1793331 * 2 ^ 59
def prefixEnd_1793331 : Nat := 4983230072969 + 3 ^ 40 * 1793331 * 2
def baseEnd_1793331 : Nat := 920840775608228317915127

theorem tailTrace_1793331 : CollatzResearch.WordTrace tailWord_1793331 prefixEnd_1793331 920840775608228317915127 := by
  unfold tailWord_1793331
  simp only [CollatzResearch.WordTrace]
  refine ⟨65408155066075538395987847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43605436710717025597325231 65408155066075538395987847)
  ·
    refine ⟨98112232599113307593981771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65408155066075538395987847 98112232599113307593981771)
    ·
      refine ⟨147168348898669961390972657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98112232599113307593981771 147168348898669961390972657)
      ·
        refine ⟨110376261674002471043229493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147168348898669961390972657 110376261674002471043229493)
        ·
          refine ⟨10347774531937731660302765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110376261674002471043229493 10347774531937731660302765)
          ·
            refine ⟨3880415449476649372613537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10347774531937731660302765 3880415449476649372613537)
            ·
              refine ⟨2910311587107487029460153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880415449476649372613537 2910311587107487029460153)
              ·
                refine ⟨2182733690330615272095115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910311587107487029460153 2182733690330615272095115)
                ·
                  refine ⟨3274100535495922908142673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182733690330615272095115 3274100535495922908142673)
                  ·
                    refine ⟨2455575401621942181107005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274100535495922908142673 2455575401621942181107005)
                    ·
                      refine ⟨920840775608228317915127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455575401621942181107005 920840775608228317915127)
                      ·
                        rfl

theorem cell23_1793331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_1793331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793331 prefixEnd_1793331 := by exact prefixLift 1793331
  have htrace : WordTrace (prefixWord ++ tailWord_1793331) baseStart_1793331 baseEnd_1793331 := by
    simpa [prefixWord, tailWord_1793331, baseEnd_1793331] using wordTrace_append hprefix tailTrace_1793331
  have hstable : (prefixWord ++ tailWord_1793331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793331).length < 2 ^ (prefixWord ++ tailWord_1793331).sum := by decide
  have hdescent : baseEnd_1793331 < baseStart_1793331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793344 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3]
def baseStart_1793344 : Nat := 118140960795 + 1793344 * 2 ^ 59
def prefixEnd_1793344 : Nat := 4983230072969 + 3 ^ 40 * 1793344 * 2
def baseEnd_1793344 : Nat := 920847450856736767052567

theorem tailTrace_1793344 : CollatzResearch.WordTrace tailWord_1793344 prefixEnd_1793344 920847450856736767052567 := by
  unfold tailWord_1793344
  simp only [CollatzResearch.WordTrace]
  refine ⟨32704314607514220808105543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43605752810018961077474057 32704314607514220808105543)
  ·
    refine ⟨49056471911271331212158315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32704314607514220808105543 49056471911271331212158315)
    ·
      refine ⟨73584707866906996818237473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49056471911271331212158315 73584707866906996818237473)
      ·
        refine ⟨55188530900180247613678105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73584707866906996818237473 55188530900180247613678105)
        ·
          refine ⟨41391398175135185710258579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55188530900180247613678105 41391398175135185710258579)
          ·
            refine ⟨62087097262702778565387869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41391398175135185710258579 62087097262702778565387869)
            ·
              refine ⟨23282661473513541962020451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62087097262702778565387869 23282661473513541962020451)
              ·
                refine ⟨34923992210270312943030677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23282661473513541962020451 34923992210270312943030677)
                ·
                  refine ⟨1637062134856420919204563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34923992210270312943030677 1637062134856420919204563)
                  ·
                    refine ⟨2455593202284631378806845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637062134856420919204563 2455593202284631378806845)
                    ·
                      refine ⟨920847450856736767052567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455593202284631378806845 920847450856736767052567)
                      ·
                        rfl

theorem cell23_1793344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_1793344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793344 prefixEnd_1793344 := by exact prefixLift 1793344
  have htrace : WordTrace (prefixWord ++ tailWord_1793344) baseStart_1793344 baseEnd_1793344 := by
    simpa [prefixWord, tailWord_1793344, baseEnd_1793344] using wordTrace_append hprefix tailTrace_1793344
  have hstable : (prefixWord ++ tailWord_1793344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793344).length < 2 ^ (prefixWord ++ tailWord_1793344).sum := by decide
  have hdescent : baseEnd_1793344 < baseStart_1793344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793348 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1793348 : Nat := 118140960795 + 1793348 * 2 ^ 59
def prefixEnd_1793348 : Nat := 4983230072969 + 3 ^ 40 * 1793348 * 2
def baseEnd_1793348 : Nat := 920849504779354751402549

theorem tailTrace_1793348 : CollatzResearch.WordTrace tailWord_1793348 prefixEnd_1793348 920849504779354751402549 := by
  unfold tailWord_1793348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32704387553506975149678349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43605850071342633532904465 32704387553506975149678349)
  ·
    refine ⟨12264145332565115681129381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32704387553506975149678349 12264145332565115681129381)
    ·
      refine ⟨2299527249855959190211759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12264145332565115681129381 2299527249855959190211759)
      ·
        refine ⟨3449290874783938785317639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299527249855959190211759 3449290874783938785317639)
        ·
          refine ⟨5173936312175908177976459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449290874783938785317639 5173936312175908177976459)
          ·
            refine ⟨7760904468263862266964689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173936312175908177976459 7760904468263862266964689)
            ·
              refine ⟨5820678351197896700223517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760904468263862266964689 5820678351197896700223517)
              ·
                refine ⟨2182754381699211262583819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820678351197896700223517 2182754381699211262583819)
                ·
                  refine ⟨3274131572548816893875729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182754381699211262583819 3274131572548816893875729)
                  ·
                    refine ⟨2455598679411612670406797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274131572548816893875729 2455598679411612670406797)
                    ·
                      refine ⟨920849504779354751402549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455598679411612670406797 920849504779354751402549)
                      ·
                        rfl

theorem cell23_1793348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1793348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793348 prefixEnd_1793348 := by exact prefixLift 1793348
  have htrace : WordTrace (prefixWord ++ tailWord_1793348) baseStart_1793348 baseEnd_1793348 := by
    simpa [prefixWord, tailWord_1793348, baseEnd_1793348] using wordTrace_append hprefix tailTrace_1793348
  have hstable : (prefixWord ++ tailWord_1793348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793348).length < 2 ^ (prefixWord ++ tailWord_1793348).sum := by decide
  have hdescent : baseEnd_1793348 < baseStart_1793348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793361 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_1793361 : Nat := 118140960795 + 1793361 * 2 ^ 59
def prefixEnd_1793361 : Nat := 4983230072969 + 3 ^ 40 * 1793361 * 2
def baseEnd_1793361 : Nat := 920856180027863200539989

theorem tailTrace_1793361 : CollatzResearch.WordTrace tailWord_1793361 prefixEnd_1793361 920856180027863200539989 := by
  unfold tailWord_1793361
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409249255966853519579937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43606166170644569013053291 65409249255966853519579937)
  ·
    refine ⟨49056936941975140139684953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65409249255966853519579937 49056936941975140139684953)
    ·
      refine ⟨36792702706481355104763715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49056936941975140139684953 36792702706481355104763715)
      ·
        refine ⟨55189054059722032657145573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36792702706481355104763715 55189054059722032657145573)
        ·
          refine ⟨10347947636197881123214795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55189054059722032657145573 10347947636197881123214795)
          ·
            refine ⟨15521921454296821684822193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347947636197881123214795 15521921454296821684822193)
            ·
              refine ⟨11641441090722616263616645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15521921454296821684822193 11641441090722616263616645)
              ·
                refine ⟨2182770204510490549428121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11641441090722616263616645 2182770204510490549428121)
                ·
                  refine ⟨1637077653382867912071091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2182770204510490549428121 1637077653382867912071091)
                  ·
                    refine ⟨2455616480074301868106637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637077653382867912071091 2455616480074301868106637)
                    ·
                      refine ⟨920856180027863200539989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455616480074301868106637 920856180027863200539989)
                      ·
                        rfl

theorem cell23_1793361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_1793361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793361 prefixEnd_1793361 := by exact prefixLift 1793361
  have htrace : WordTrace (prefixWord ++ tailWord_1793361) baseStart_1793361 baseEnd_1793361 := by
    simpa [prefixWord, tailWord_1793361, baseEnd_1793361] using wordTrace_append hprefix tailTrace_1793361
  have hstable : (prefixWord ++ tailWord_1793361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793361).length < 2 ^ (prefixWord ++ tailWord_1793361).sum := by decide
  have hdescent : baseEnd_1793361 < baseStart_1793361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793377 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1793377 : Nat := 118140960795 + 1793377 * 2 ^ 59
def prefixEnd_1793377 : Nat := 4983230072969 + 3 ^ 40 * 1793377 * 2
def baseEnd_1793377 : Nat := 306954798572778379313305

theorem tailTrace_1793377 : CollatzResearch.WordTrace tailWord_1793377 prefixEnd_1793377 306954798572778379313305 := by
  unfold tailWord_1793377
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409832823908888252162385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43606555215939258834774923 65409832823908888252162385)
  ·
    refine ⟨49057374617931666189121789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65409832823908888252162385 49057374617931666189121789)
    ·
      refine ⟨18396515481724374820920671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49057374617931666189121789 18396515481724374820920671)
      ·
        refine ⟨27594773222586562231381007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18396515481724374820920671 27594773222586562231381007)
        ·
          refine ⟨41392159833879843347071511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27594773222586562231381007 41392159833879843347071511)
          ·
            refine ⟨62088239750819765020607267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41392159833879843347071511 62088239750819765020607267)
            ·
              refine ⟨93132359626229647530910901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62088239750819765020607267 93132359626229647530910901)
              ·
                refine ⟨8731158714959029456022897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93132359626229647530910901 8731158714959029456022897)
                ·
                  refine ⟨6548369036219272092017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8731158714959029456022897 6548369036219272092017173)
                  ·
                    refine ⟨306954798572778379313305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6548369036219272092017173 306954798572778379313305)
                    ·
                      rfl

theorem cell23_1793377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1793377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793377 prefixEnd_1793377 := by exact prefixLift 1793377
  have htrace : WordTrace (prefixWord ++ tailWord_1793377) baseStart_1793377 baseEnd_1793377 := by
    simpa [prefixWord, tailWord_1793377, baseEnd_1793377] using wordTrace_append hprefix tailTrace_1793377
  have hstable : (prefixWord ++ tailWord_1793377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793377).length < 2 ^ (prefixWord ++ tailWord_1793377).sum := by decide
  have hdescent : baseEnd_1793377 < baseStart_1793377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793378 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1793378 : Nat := 118140960795 + 1793378 * 2 ^ 59
def prefixEnd_1793378 : Nat := 4983230072969 + 3 ^ 40 * 1793378 * 2
def baseEnd_1793378 : Nat := 920864909198989634027411

theorem tailTrace_1793378 : CollatzResearch.WordTrace tailWord_1793378 prefixEnd_1793378 920864909198989634027411 := by
  unfold tailWord_1793378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16352467324226316355737197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43606579531270176948632525 16352467324226316355737197)
  ·
    refine ⟨6132175246584868633401449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16352467324226316355737197 6132175246584868633401449)
    ·
      refine ⟨4599131434938651475051087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6132175246584868633401449 4599131434938651475051087)
      ·
        refine ⟨6898697152407977212576631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599131434938651475051087 6898697152407977212576631)
        ·
          refine ⟨10348045728611965818864947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898697152407977212576631 10348045728611965818864947)
          ·
            refine ⟨15522068592917948728297421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10348045728611965818864947 15522068592917948728297421)
            ·
              refine ⟨5820775722344230773111533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15522068592917948728297421 5820775722344230773111533)
              ·
                refine ⟨2182790895879086539916825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820775722344230773111533 2182790895879086539916825)
                ·
                  refine ⟨1637093171909314904937619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2182790895879086539916825 1637093171909314904937619)
                  ·
                    refine ⟨2455639757863972357406429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637093171909314904937619 2455639757863972357406429)
                    ·
                      refine ⟨920864909198989634027411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455639757863972357406429 920864909198989634027411)
                      ·
                        rfl

theorem cell23_1793378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1793378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793378 prefixEnd_1793378 := by exact prefixLift 1793378
  have htrace : WordTrace (prefixWord ++ tailWord_1793378) baseStart_1793378 baseEnd_1793378 := by
    simpa [prefixWord, tailWord_1793378, baseEnd_1793378] using wordTrace_append hprefix tailTrace_1793378
  have hstable : (prefixWord ++ tailWord_1793378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793378).length < 2 ^ (prefixWord ++ tailWord_1793378).sum := by decide
  have hdescent : baseEnd_1793378 < baseStart_1793378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793388 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_1793388 : Nat := 118140960795 + 1793388 * 2 ^ 59
def prefixEnd_1793388 : Nat := 4983230072969 + 3 ^ 40 * 1793388 * 2
def baseEnd_1793388 : Nat := 920870044005534594902365

theorem tailTrace_1793388 : CollatzResearch.WordTrace tailWord_1793388 prefixEnd_1793388 920870044005534594902365 := by
  unfold tailWord_1793388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32705117013434518565406409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43606822684579358087208545 32705117013434518565406409)
  ·
    refine ⟨24528837760075888924054807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32705117013434518565406409 24528837760075888924054807)
    ·
      refine ⟨36793256640113833386082211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24528837760075888924054807 36793256640113833386082211)
      ·
        refine ⟨55189884960170750079123317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36793256640113833386082211 55189884960170750079123317)
        ·
          refine ⟨5174051715016007819917811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55189884960170750079123317 5174051715016007819917811)
          ·
            refine ⟨7761077572524011729876717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174051715016007819917811 7761077572524011729876717)
            ·
              refine ⟨2910404089696504398703769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7761077572524011729876717 2910404089696504398703769)
              ·
                refine ⟨2182803067272378299027827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910404089696504398703769 2182803067272378299027827)
                ·
                  refine ⟨3274204600908567448541741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182803067272378299027827 3274204600908567448541741)
                  ·
                    refine ⟨1227826725340712793203153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274204600908567448541741 1227826725340712793203153)
                    ·
                      refine ⟨920870044005534594902365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227826725340712793203153 920870044005534594902365)
                      ·
                        rfl

theorem cell23_1793388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_1793388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793388 prefixEnd_1793388 := by exact prefixLift 1793388
  have htrace : WordTrace (prefixWord ++ tailWord_1793388) baseStart_1793388 baseEnd_1793388 := by
    simpa [prefixWord, tailWord_1793388, baseEnd_1793388] using wordTrace_append hprefix tailTrace_1793388
  have hstable : (prefixWord ++ tailWord_1793388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793388).length < 2 ^ (prefixWord ++ tailWord_1793388).sum := by decide
  have hdescent : baseEnd_1793388 < baseStart_1793388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793401 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 6, 2, 2]
def baseStart_1793401 : Nat := 118140960795 + 1793401 * 2 ^ 59
def prefixEnd_1793401 : Nat := 4983230072969 + 3 ^ 40 * 1793401 * 2
def baseEnd_1793401 : Nat := 920876719254043044039805

theorem tailTrace_1793401 : CollatzResearch.WordTrace tailWord_1793401 prefixEnd_1793401 920876719254043044039805 := by
  unfold tailWord_1793401
  simp only [CollatzResearch.WordTrace]
  refine ⟨65410708175821940351036057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43607138783881293567357371 65410708175821940351036057)
  ·
    refine ⟨49058031131866455263277043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65410708175821940351036057 49058031131866455263277043)
    ·
      refine ⟨73587046697799682894915565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49058031131866455263277043 73587046697799682894915565)
      ·
        refine ⟨27595142511674881085593337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73587046697799682894915565 27595142511674881085593337)
        ·
          refine ⟨20696356883756160814195003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27595142511674881085593337 20696356883756160814195003)
          ·
            refine ⟨31044535325634241221292505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20696356883756160814195003 31044535325634241221292505)
            ·
              refine ⟨23283401494225680915969379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31044535325634241221292505 23283401494225680915969379)
              ·
                refine ⟨34925102241338521373954069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23283401494225680915969379 34925102241338521373954069)
                ·
                  refine ⟨1637114167562743189404097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34925102241338521373954069 1637114167562743189404097)
                  ·
                    refine ⟨1227835625672057392053073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1637114167562743189404097 1227835625672057392053073)
                    ·
                      refine ⟨920876719254043044039805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1227835625672057392053073 920876719254043044039805)
                      ·
                        rfl

theorem cell23_1793401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_1793401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793401 prefixEnd_1793401 := by exact prefixLift 1793401
  have htrace : WordTrace (prefixWord ++ tailWord_1793401) baseStart_1793401 baseEnd_1793401 := by
    simpa [prefixWord, tailWord_1793401, baseEnd_1793401] using wordTrace_append hprefix tailTrace_1793401
  have hstable : (prefixWord ++ tailWord_1793401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793401).length < 2 ^ (prefixWord ++ tailWord_1793401).sum := by decide
  have hdescent : baseEnd_1793401 < baseStart_1793401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793511 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1793511 : Nat := 118140960795 + 1793511 * 2 ^ 59
def prefixEnd_1793511 : Nat := 4983230072969 + 3 ^ 40 * 1793511 * 2
def baseEnd_1793511 : Nat := 920933202126037613664299

theorem tailTrace_1793511 : CollatzResearch.WordTrace tailWord_1793511 prefixEnd_1793511 920933202126037613664299 := by
  unfold tailWord_1793511
  simp only [CollatzResearch.WordTrace]
  refine ⟨65414720205423429137540387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43609813470282286091693591 65414720205423429137540387)
  ·
    refine ⟨98122080308135143706310581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65414720205423429137540387 98122080308135143706310581)
    ·
      refine ⟨9198945028887669722466617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98122080308135143706310581 9198945028887669722466617)
      ·
        refine ⟨6899208771665752291849963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9198945028887669722466617 6899208771665752291849963)
        ·
          refine ⟨10348813157498628437774945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899208771665752291849963 10348813157498628437774945)
          ·
            refine ⟨7761609868123971328331209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10348813157498628437774945 7761609868123971328331209)
            ·
              refine ⟨5821207401092978496248407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761609868123971328331209 5821207401092978496248407)
              ·
                refine ⟨8731811101639467744372611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821207401092978496248407 8731811101639467744372611)
                ·
                  refine ⟨13097716652459201616558917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8731811101639467744372611 13097716652459201616558917)
                  ·
                    refine ⟨2455821872336100303104797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13097716652459201616558917 2455821872336100303104797)
                    ·
                      refine ⟨920933202126037613664299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455821872336100303104797 920933202126037613664299)
                      ·
                        rfl

theorem cell23_1793511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1793511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793511 prefixEnd_1793511 := by exact prefixLift 1793511
  have htrace : WordTrace (prefixWord ++ tailWord_1793511) baseStart_1793511 baseEnd_1793511 := by
    simpa [prefixWord, tailWord_1793511, baseEnd_1793511] using wordTrace_append hprefix tailTrace_1793511
  have hstable : (prefixWord ++ tailWord_1793511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793511).length < 2 ^ (prefixWord ++ tailWord_1793511).sum := by decide
  have hdescent : baseEnd_1793511 < baseStart_1793511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793592 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 1, 1, 3]
def baseStart_1793592 : Nat := 118140960795 + 1793592 * 2 ^ 59
def prefixEnd_1793592 : Nat := 4983230072969 + 3 ^ 40 * 1793592 * 2
def baseEnd_1793592 : Nat := 920974794059051796751427

theorem tailTrace_1793592 : CollatzResearch.WordTrace tailWord_1793592 prefixEnd_1793592 920974794059051796751427 := by
  unfold tailWord_1793592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32708837259064989985619515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43611783012086653314159353 32708837259064989985619515)
  ·
    refine ⟨49063255888597484978429273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32708837259064989985619515 49063255888597484978429273)
    ·
      refine ⟨36797441916448113733821955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49063255888597484978429273 36797441916448113733821955)
      ·
        refine ⟨55196162874672170600732933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797441916448113733821955 55196162874672170600732933)
        ·
          refine ⟨10349280539001031987637425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55196162874672170600732933 10349280539001031987637425)
          ·
            refine ⟨7761960404250773990728069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10349280539001031987637425 7761960404250773990728069)
            ·
              refine ⟨1455367575797020123261513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7761960404250773990728069 1455367575797020123261513)
              ·
                refine ⟨1091525681847765092446135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455367575797020123261513 1091525681847765092446135)
                ·
                  refine ⟨1637288522771647638669203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091525681847765092446135 1637288522771647638669203)
                  ·
                    refine ⟨2455932784157471458003805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637288522771647638669203 2455932784157471458003805)
                    ·
                      refine ⟨920974794059051796751427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455932784157471458003805 920974794059051796751427)
                      ·
                        rfl

theorem cell23_1793592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_1793592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793592 prefixEnd_1793592 := by exact prefixLift 1793592
  have htrace : WordTrace (prefixWord ++ tailWord_1793592) baseStart_1793592 baseEnd_1793592 := by
    simpa [prefixWord, tailWord_1793592, baseEnd_1793592] using wordTrace_append hprefix tailTrace_1793592
  have hstable : (prefixWord ++ tailWord_1793592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793592).length < 2 ^ (prefixWord ++ tailWord_1793592).sum := by decide
  have hdescent : baseEnd_1793592 < baseStart_1793592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793601 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1793601 : Nat := 118140960795 + 1793601 * 2 ^ 59
def prefixEnd_1793601 : Nat := 4983230072969 + 3 ^ 40 * 1793601 * 2
def baseEnd_1793601 : Nat := 920979415384942261538885

theorem tailTrace_1793601 : CollatzResearch.WordTrace tailWord_1793601 prefixEnd_1793601 920979415384942261538885 := by
  unfold tailWord_1793601
  simp only [CollatzResearch.WordTrace]
  refine ⟨65418002775097374508316657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43612001850064916338877771 65418002775097374508316657)
  ·
    refine ⟨49063502081323030881237493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65418002775097374508316657 49063502081323030881237493)
    ·
      refine ⟨4599703320124034145116015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49063502081323030881237493 4599703320124034145116015)
      ·
        refine ⟨6899554980186051217674023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599703320124034145116015 6899554980186051217674023)
        ·
          refine ⟨10349332470279076826511035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899554980186051217674023 10349332470279076826511035)
          ·
            refine ⟨15523998705418615239766553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10349332470279076826511035 15523998705418615239766553)
            ·
              refine ⟨11642999029063961429824915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15523998705418615239766553 11642999029063961429824915)
              ·
                refine ⟨17464498543595942144737373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11642999029063961429824915 17464498543595942144737373)
                ·
                  refine ⟨6549186953848478304276515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17464498543595942144737373 6549186953848478304276515)
                  ·
                    refine ⟨9823780430772717456414773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549186953848478304276515 9823780430772717456414773)
                    ·
                      refine ⟨920979415384942261538885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9823780430772717456414773 920979415384942261538885)
                      ·
                        rfl

theorem cell23_1793601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1793601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793601 prefixEnd_1793601 := by exact prefixLift 1793601
  have htrace : WordTrace (prefixWord ++ tailWord_1793601) baseStart_1793601 baseEnd_1793601 := by
    simpa [prefixWord, tailWord_1793601, baseEnd_1793601] using wordTrace_append hprefix tailTrace_1793601
  have hstable : (prefixWord ++ tailWord_1793601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793601).length < 2 ^ (prefixWord ++ tailWord_1793601).sum := by decide
  have hdescent : baseEnd_1793601 < baseStart_1793601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793618 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1793618 : Nat := 118140960795 + 1793618 * 2 ^ 59
def prefixEnd_1793618 : Nat := 4983230072969 + 3 ^ 40 * 1793618 * 2
def baseEnd_1793618 : Nat := 920988144556068695026307

theorem tailTrace_1793618 : CollatzResearch.WordTrace tailWord_1793618 prefixEnd_1793618 920988144556068695026307 := by
  unfold tailWord_1793618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354655704008946602921377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43612415210690524274457005 16354655704008946602921377)
  ·
    refine ⟨12265991778006709952191033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16354655704008946602921377 12265991778006709952191033)
    ·
      refine ⟨9199493833505032464143275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12265991778006709952191033 9199493833505032464143275)
      ·
        refine ⟨13799240750257548696214913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199493833505032464143275 13799240750257548696214913)
        ·
          refine ⟨10349430562693161522161185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799240750257548696214913 10349430562693161522161185)
          ·
            refine ⟨7762072922019871141620889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10349430562693161522161185 7762072922019871141620889)
            ·
              refine ⟨5821554691514903356215667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762072922019871141620889 5821554691514903356215667)
              ·
                refine ⟨8732332037272355034323501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821554691514903356215667 8732332037272355034323501)
                ·
                  refine ⟨3274624513977133137871313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8732332037272355034323501 3274624513977133137871313)
                  ·
                    refine ⟨2455968385482849853403485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274624513977133137871313 2455968385482849853403485)
                    ·
                      refine ⟨920988144556068695026307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455968385482849853403485 920988144556068695026307)
                      ·
                        rfl

theorem cell23_1793618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1793618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793618 prefixEnd_1793618 := by exact prefixLift 1793618
  have htrace : WordTrace (prefixWord ++ tailWord_1793618) baseStart_1793618 baseEnd_1793618 := by
    simpa [prefixWord, tailWord_1793618, baseEnd_1793618] using wordTrace_append hprefix tailTrace_1793618
  have hstable : (prefixWord ++ tailWord_1793618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793618).length < 2 ^ (prefixWord ++ tailWord_1793618).sum := by decide
  have hdescent : baseEnd_1793618 < baseStart_1793618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793628 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1793628 : Nat := 118140960795 + 1793628 * 2 ^ 59
def prefixEnd_1793628 : Nat := 4983230072969 + 3 ^ 40 * 1793628 * 2
def baseEnd_1793628 : Nat := 920993279362613655901261

theorem tailTrace_1793628 : CollatzResearch.WordTrace tailWord_1793628 prefixEnd_1793628 920993279362613655901261 := by
  unfold tailWord_1793628
  simp only [CollatzResearch.WordTrace]
  refine ⟨32709493772999779059774769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43612658363999705413033025 32709493772999779059774769)
  ·
    refine ⟨24532120329749834294831077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32709493772999779059774769 24532120329749834294831077)
    ·
      refine ⟨4599772561828093930280827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24532120329749834294831077 4599772561828093930280827)
      ·
        refine ⟨6899658842742140895421241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599772561828093930280827 6899658842742140895421241)
        ·
          refine ⟨5174744132056605671565931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899658842742140895421241 5174744132056605671565931)
          ·
            refine ⟨7762116198084908507348897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174744132056605671565931 7762116198084908507348897)
            ·
              refine ⟨5821587148563681380511673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762116198084908507348897 5821587148563681380511673)
              ·
                refine ⟨4366190361422761035383755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5821587148563681380511673 4366190361422761035383755)
                ·
                  refine ⟨6549285542134141553075633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366190361422761035383755 6549285542134141553075633)
                  ·
                    refine ⟨4911964156600606164806725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549285542134141553075633 4911964156600606164806725)
                    ·
                      refine ⟨920993279362613655901261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4911964156600606164806725 920993279362613655901261)
                      ·
                        rfl

theorem cell23_1793628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1793628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793628 prefixEnd_1793628 := by exact prefixLift 1793628
  have htrace : WordTrace (prefixWord ++ tailWord_1793628) baseStart_1793628 baseEnd_1793628 := by
    simpa [prefixWord, tailWord_1793628, baseEnd_1793628] using wordTrace_append hprefix tailTrace_1793628
  have hstable : (prefixWord ++ tailWord_1793628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793628).length < 2 ^ (prefixWord ++ tailWord_1793628).sum := by decide
  have hdescent : baseEnd_1793628 < baseStart_1793628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793629 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1793629 : Nat := 118140960795 + 1793629 * 2 ^ 59
def prefixEnd_1793629 : Nat := 4983230072969 + 3 ^ 40 * 1793629 * 2
def baseEnd_1793629 : Nat := 306997930947756050662919

theorem tailTrace_1793629 : CollatzResearch.WordTrace tailWord_1793629 prefixEnd_1793629 306997930947756050662919 := by
  unfold tailWord_1793629
  simp only [CollatzResearch.WordTrace]
  refine ⟨65419024018995935290335941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43612682679330623526890627 65419024018995935290335941)
  ·
    refine ⟨12266067003561737866937989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65419024018995935290335941 12266067003561737866937989)
    ·
      refine ⟨2299887563167825850050873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12266067003561737866937989 2299887563167825850050873)
      ·
        refine ⟨1724915672375869387538155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299887563167825850050873 1724915672375869387538155)
        ·
          refine ⟨2587373508563804081307233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724915672375869387538155 2587373508563804081307233)
          ·
            refine ⟨1940530131422853060980425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2587373508563804081307233 1940530131422853060980425)
            ·
              refine ⟨1455397598567139795735319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940530131422853060980425 1455397598567139795735319)
              ·
                refine ⟨2183096397850709693602979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455397598567139795735319 2183096397850709693602979)
                ·
                  refine ⟨3274644596776064540404469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183096397850709693602979 3274644596776064540404469)
                  ·
                    refine ⟨306997930947756050662919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3274644596776064540404469 306997930947756050662919)
                    ·
                      rfl

theorem cell23_1793629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1793629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793629 prefixEnd_1793629 := by exact prefixLift 1793629
  have htrace : WordTrace (prefixWord ++ tailWord_1793629) baseStart_1793629 baseEnd_1793629 := by
    simpa [prefixWord, tailWord_1793629, baseEnd_1793629] using wordTrace_append hprefix tailTrace_1793629
  have hstable : (prefixWord ++ tailWord_1793629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793629).length < 2 ^ (prefixWord ++ tailWord_1793629).sum := by decide
  have hdescent : baseEnd_1793629 < baseStart_1793629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793635 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1793635 : Nat := 118140960795 + 1793635 * 2 ^ 59
def prefixEnd_1793635 : Nat := 4983230072969 + 3 ^ 40 * 1793635 * 2
def baseEnd_1793635 : Nat := 920996873727195128513729

theorem tailTrace_1793635 : CollatzResearch.WordTrace tailWord_1793635 prefixEnd_1793635 920996873727195128513729 := by
  unfold tailWord_1793635
  simp only [CollatzResearch.WordTrace]
  refine ⟨65419242856974198315054359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43612828571316132210036239 65419242856974198315054359)
  ·
    refine ⟨98128864285461297472581539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65419242856974198315054359 98128864285461297472581539)
    ·
      refine ⟨147193296428191946208872309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98128864285461297472581539 147193296428191946208872309)
      ·
        refine ⟨13799371540142994957081779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147193296428191946208872309 13799371540142994957081779)
        ·
          refine ⟨20699057310214492435622669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13799371540142994957081779 20699057310214492435622669)
          ·
            refine ⟨7762146491330434663358501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20699057310214492435622669 7762146491330434663358501)
            ·
              refine ⟨1455402467124456499379719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7762146491330434663358501 1455402467124456499379719)
              ·
                refine ⟨2183103700686684749069579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455402467124456499379719 2183103700686684749069579)
                ·
                  refine ⟨3274655551030027123604369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183103700686684749069579 3274655551030027123604369)
                  ·
                    refine ⟨2455991663272520342703277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3274655551030027123604369 2455991663272520342703277)
                    ·
                      refine ⟨920996873727195128513729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2455991663272520342703277 920996873727195128513729)
                      ·
                        rfl

theorem cell23_1793635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1793635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793635 prefixEnd_1793635 := by exact prefixLift 1793635
  have htrace : WordTrace (prefixWord ++ tailWord_1793635) baseStart_1793635 baseEnd_1793635 := by
    simpa [prefixWord, tailWord_1793635, baseEnd_1793635] using wordTrace_append hprefix tailTrace_1793635
  have hstable : (prefixWord ++ tailWord_1793635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793635).length < 2 ^ (prefixWord ++ tailWord_1793635).sum := by decide
  have hdescent : baseEnd_1793635 < baseStart_1793635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793658 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_1793658 : Nat := 118140960795 + 1793658 * 2 ^ 59
def prefixEnd_1793658 : Nat := 4983230072969 + 3 ^ 40 * 1793658 * 2
def baseEnd_1793658 : Nat := 921008683782248538526123

theorem tailTrace_1793658 : CollatzResearch.WordTrace tailWord_1793658 prefixEnd_1793658 921008683782248538526123 := by
  unfold tailWord_1793658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355020433972718310785407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43613387823927248828761085 16355020433972718310785407)
  ·
    refine ⟨24532530650959077466178111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16355020433972718310785407 24532530650959077466178111)
    ·
      refine ⟨36798795976438616199267167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24532530650959077466178111 36798795976438616199267167)
      ·
        refine ⟨55198193964657924298900751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36798795976438616199267167 55198193964657924298900751)
        ·
          refine ⟨82797290946986886448351127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55198193964657924298900751 82797290946986886448351127)
          ·
            refine ⟨124195936420480329672526691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82797290946986886448351127 124195936420480329672526691)
            ·
              refine ⟨186293904630720494508790037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124195936420480329672526691 186293904630720494508790037)
              ·
                refine ⟨8732526779565023180099533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186293904630720494508790037 8732526779565023180099533)
                ·
                  refine ⟨3274697542336883692537325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8732526779565023180099533 3274697542336883692537325)
                  ·
                    refine ⟨1228011578376331384701497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274697542336883692537325 1228011578376331384701497)
                    ·
                      refine ⟨921008683782248538526123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228011578376331384701497 921008683782248538526123)
                      ·
                        rfl

theorem cell23_1793658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_1793658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793658 prefixEnd_1793658 := by exact prefixLift 1793658
  have htrace : WordTrace (prefixWord ++ tailWord_1793658) baseStart_1793658 baseEnd_1793658 := by
    simpa [prefixWord, tailWord_1793658, baseEnd_1793658] using wordTrace_append hprefix tailTrace_1793658
  have hstable : (prefixWord ++ tailWord_1793658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793658).length < 2 ^ (prefixWord ++ tailWord_1793658).sum := by decide
  have hdescent : baseEnd_1793658 < baseStart_1793658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793665 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1793665 : Nat := 118140960795 + 1793665 * 2 ^ 59
def prefixEnd_1793665 : Nat := 4983230072969 + 3 ^ 40 * 1793665 * 2
def baseEnd_1793665 : Nat := 921012278146830011138591

theorem tailTrace_1793665 : CollatzResearch.WordTrace tailWord_1793665 prefixEnd_1793665 921012278146830011138591 := by
  unfold tailWord_1793665
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420337046865513438646449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43613558031243675625764299 65420337046865513438646449)
  ·
    refine ⟨49065252785149135078984837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65420337046865513438646449 49065252785149135078984837)
    ·
      refine ⟨9199734897215462827309657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49065252785149135078984837 9199734897215462827309657)
      ·
        refine ⟨6899801172911597120482243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9199734897215462827309657 6899801172911597120482243)
        ·
          refine ⟨10349701759367395680723365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899801172911597120482243 10349701759367395680723365)
          ·
            refine ⟨1940569079881386690135631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10349701759367395680723365 1940569079881386690135631)
            ·
              refine ⟨2910853619822080035203447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940569079881386690135631 2910853619822080035203447)
              ·
                refine ⟨4366280429733120052805171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910853619822080035203447 4366280429733120052805171)
                ·
                  refine ⟨6549420644599680079207757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366280429733120052805171 6549420644599680079207757)
                  ·
                    refine ⟨2456032741724880029702909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6549420644599680079207757 2456032741724880029702909)
                    ·
                      refine ⟨921012278146830011138591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456032741724880029702909 921012278146830011138591)
                      ·
                        rfl

theorem cell23_1793665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1793665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793665 prefixEnd_1793665 := by exact prefixLift 1793665
  have htrace : WordTrace (prefixWord ++ tailWord_1793665) baseStart_1793665 baseEnd_1793665 := by
    simpa [prefixWord, tailWord_1793665, baseEnd_1793665] using wordTrace_append hprefix tailTrace_1793665
  have hstable : (prefixWord ++ tailWord_1793665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793665).length < 2 ^ (prefixWord ++ tailWord_1793665).sum := by decide
  have hdescent : baseEnd_1793665 < baseStart_1793665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793672 : List Nat := [2, 1, 3, 5, 2, 1, 2, 7]
def baseStart_1793672 : Nat := 118140960795 + 1793672 * 2 ^ 59
def prefixEnd_1793672 : Nat := 4983230072969 + 3 ^ 40 * 1793672 * 2
def baseEnd_1793672 : Nat := 34111698981904129027817

theorem tailTrace_1793672 : CollatzResearch.WordTrace tailWord_1793672 prefixEnd_1793672 34111698981904129027817 := by
  unfold tailWord_1793672
  simp only [CollatzResearch.WordTrace]
  refine ⟨32710296178920076817075635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43613728238560102422767513 32710296178920076817075635)
  ·
    refine ⟨49065444268380115225613453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32710296178920076817075635 49065444268380115225613453)
    ·
      refine ⟨18399541600642543209605045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49065444268380115225613453 18399541600642543209605045)
      ·
        refine ⟨1724957025060238425900473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18399541600642543209605045 1724957025060238425900473)
        ·
          refine ⟨1293717768795178819425355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724957025060238425900473 1293717768795178819425355)
          ·
            refine ⟨1940576653192768229138033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293717768795178819425355 1940576653192768229138033)
            ·
              refine ⟨1455432489894576171853525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940576653192768229138033 1455432489894576171853525)
              ·
                refine ⟨34111698981904129027817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1455432489894576171853525 34111698981904129027817)
                ·
                  rfl

theorem cell23_1793672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 7].length) (baseStart_1793672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793672 prefixEnd_1793672 := by exact prefixLift 1793672
  have htrace : WordTrace (prefixWord ++ tailWord_1793672) baseStart_1793672 baseEnd_1793672 := by
    simpa [prefixWord, tailWord_1793672, baseEnd_1793672] using wordTrace_append hprefix tailTrace_1793672
  have hstable : (prefixWord ++ tailWord_1793672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793672).length < 2 ^ (prefixWord ++ tailWord_1793672).sum := by decide
  have hdescent : baseEnd_1793672 < baseStart_1793672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793675 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 1, 3, 2]
def baseStart_1793675 : Nat := 118140960795 + 1793675 * 2 ^ 59
def prefixEnd_1793675 : Nat := 4983230072969 + 3 ^ 40 * 1793675 * 2
def baseEnd_1793675 : Nat := 921017412953374972013545

theorem tailTrace_1793675 : CollatzResearch.WordTrace tailWord_1793675 prefixEnd_1793675 921017412953374972013545 := by
  unfold tailWord_1793675
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420701776829285146510479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43613801184552856764340319 65420701776829285146510479)
  ·
    refine ⟨98131052665243927719765719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65420701776829285146510479 98131052665243927719765719)
    ·
      refine ⟨147196578997865891579648579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98131052665243927719765719 147196578997865891579648579)
      ·
        refine ⟨220794868496798837369472869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147196578997865891579648579 220794868496798837369472869)
        ·
          refine ⟨41399037843149782006776163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220794868496798837369472869 41399037843149782006776163)
          ·
            refine ⟨62098556764724673010164245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41399037843149782006776163 62098556764724673010164245)
            ·
              refine ⟨2910869848346469047351449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62098556764724673010164245 2910869848346469047351449)
              ·
                refine ⟨2183152386259851785513587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910869848346469047351449 2183152386259851785513587)
                ·
                  refine ⟨3274728579389777678270381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183152386259851785513587 3274728579389777678270381)
                  ·
                    refine ⟨1228023217271166629351393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274728579389777678270381 1228023217271166629351393)
                    ·
                      refine ⟨921017412953374972013545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228023217271166629351393 921017412953374972013545)
                      ·
                        rfl

theorem cell23_1793675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3, 2].length) (baseStart_1793675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793675 prefixEnd_1793675 := by exact prefixLift 1793675
  have htrace : WordTrace (prefixWord ++ tailWord_1793675) baseStart_1793675 baseEnd_1793675 := by
    simpa [prefixWord, tailWord_1793675, baseEnd_1793675] using wordTrace_append hprefix tailTrace_1793675
  have hstable : (prefixWord ++ tailWord_1793675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793675).length < 2 ^ (prefixWord ++ tailWord_1793675).sum := by decide
  have hdescent : baseEnd_1793675 < baseStart_1793675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793701 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1793701 : Nat := 118140960795 + 1793701 * 2 ^ 59
def prefixEnd_1793701 : Nat := 4983230072969 + 3 ^ 40 * 1793701 * 2
def baseEnd_1793701 : Nat := 921030763450391870288425

theorem tailTrace_1793701 : CollatzResearch.WordTrace tailWord_1793701 prefixEnd_1793701 921030763450391870288425 := by
  unfold tailWord_1793701
  simp only [CollatzResearch.WordTrace]
  refine ⟨65421650074735091586956957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43614433383156727724637971 65421650074735091586956957)
  ·
    refine ⟨24533118778025659345108859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65421650074735091586956957 24533118778025659345108859)
    ·
      refine ⟨36799678167038489017663289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24533118778025659345108859 36799678167038489017663289)
      ·
        refine ⟨27599758625278866763247467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36799678167038489017663289 27599758625278866763247467)
        ·
          refine ⟨41399637937918300144871201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27599758625278866763247467 41399637937918300144871201)
          ·
            refine ⟨31049728453438725108653401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41399637937918300144871201 31049728453438725108653401)
            ·
              refine ⟨23287296340079043831490051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31049728453438725108653401 23287296340079043831490051)
              ·
                refine ⟨34930944510118565747235077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23287296340079043831490051 34930944510118565747235077)
                ·
                  refine ⟨6549552095647231077606577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34930944510118565747235077 6549552095647231077606577)
                  ·
                    refine ⟨4912164071735423308204933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549552095647231077606577 4912164071735423308204933)
                    ·
                      refine ⟨921030763450391870288425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4912164071735423308204933 921030763450391870288425)
                      ·
                        rfl

theorem cell23_1793701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1793701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793701 prefixEnd_1793701 := by exact prefixLift 1793701
  have htrace : WordTrace (prefixWord ++ tailWord_1793701) baseStart_1793701 baseEnd_1793701 := by
    simpa [prefixWord, tailWord_1793701, baseEnd_1793701] using wordTrace_append hprefix tailTrace_1793701
  have hstable : (prefixWord ++ tailWord_1793701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793701).length < 2 ^ (prefixWord ++ tailWord_1793701).sum := by decide
  have hdescent : baseEnd_1793701 < baseStart_1793701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793722 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_1793722 : Nat := 118140960795 + 1793722 * 2 ^ 59
def prefixEnd_1793722 : Nat := 4983230072969 + 3 ^ 40 * 1793722 * 2
def baseEnd_1793722 : Nat := 921041546544136288125829

theorem tailTrace_1793722 : CollatzResearch.WordTrace tailWord_1793722 prefixEnd_1793722 921041546544136288125829 := by
  unfold tailWord_1793722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355604001914753043367855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43614944005106008115647613 16355604001914753043367855)
  ·
    refine ⟨24533406002872129565051783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16355604001914753043367855 24533406002872129565051783)
    ·
      refine ⟨36800109004308194347577675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24533406002872129565051783 36800109004308194347577675)
      ·
        refine ⟨55200163506462291521366513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36800109004308194347577675 55200163506462291521366513)
        ·
          refine ⟨41400122629846718641024885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55200163506462291521366513 41400122629846718641024885)
          ·
            refine ⟨3881261496548129872596083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41400122629846718641024885 3881261496548129872596083)
            ·
              refine ⟨5821892244822194808894125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881261496548129872596083 5821892244822194808894125)
              ·
                refine ⟨2183209591808323053335297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821892244822194808894125 2183209591808323053335297)
                ·
                  refine ⟨1637407193856242290001473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183209591808323053335297 1637407193856242290001473)
                  ·
                    refine ⟨1228055395392181717501105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1637407193856242290001473 1228055395392181717501105)
                    ·
                      refine ⟨921041546544136288125829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228055395392181717501105 921041546544136288125829)
                      ·
                        rfl

theorem cell23_1793722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_1793722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793722 prefixEnd_1793722 := by exact prefixLift 1793722
  have htrace : WordTrace (prefixWord ++ tailWord_1793722) baseStart_1793722 baseEnd_1793722 := by
    simpa [prefixWord, tailWord_1793722, baseEnd_1793722] using wordTrace_append hprefix tailTrace_1793722
  have hstable : (prefixWord ++ tailWord_1793722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793722).length < 2 ^ (prefixWord ++ tailWord_1793722).sum := by decide
  have hdescent : baseEnd_1793722 < baseStart_1793722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793751 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1793751 : Nat := 118140960795 + 1793751 * 2 ^ 59
def prefixEnd_1793751 : Nat := 4983230072969 + 3 ^ 40 * 1793751 * 2
def baseEnd_1793751 : Nat := 921056437483116674663195

theorem tailTrace_1793751 : CollatzResearch.WordTrace tailWord_1793751 prefixEnd_1793751 921056437483116674663195 := by
  unfold tailWord_1793751
  simp only [CollatzResearch.WordTrace]
  refine ⟨65423473724553950126277107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43615649149702633417518071 65423473724553950126277107)
  ·
    refine ⟨98135210586830925189415661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65423473724553950126277107 98135210586830925189415661)
    ·
      refine ⟨36800703970061596946030873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98135210586830925189415661 36800703970061596946030873)
      ·
        refine ⟨27600527977546197709523155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36800703970061596946030873 27600527977546197709523155)
        ·
          refine ⟨41400791966319296564284733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27600527977546197709523155 41400791966319296564284733)
          ·
            refine ⟨15525296987369736211606775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41400791966319296564284733 15525296987369736211606775)
            ·
              refine ⟨23287945481054604317410163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15525296987369736211606775 23287945481054604317410163)
              ·
                refine ⟨34931918221581906476115245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23287945481054604317410163 34931918221581906476115245)
                ·
                  refine ⟨13099469333093214928543217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34931918221581906476115245 13099469333093214928543217)
                  ·
                    refine ⟨9824601999819911196407413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13099469333093214928543217 9824601999819911196407413)
                    ·
                      refine ⟨921056437483116674663195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9824601999819911196407413 921056437483116674663195)
                      ·
                        rfl

theorem cell23_1793751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1793751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793751 prefixEnd_1793751 := by exact prefixLift 1793751
  have htrace : WordTrace (prefixWord ++ tailWord_1793751) baseStart_1793751 baseEnd_1793751 := by
    simpa [prefixWord, tailWord_1793751, baseEnd_1793751] using wordTrace_append hprefix tailTrace_1793751
  have hstable : (prefixWord ++ tailWord_1793751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793751).length < 2 ^ (prefixWord ++ tailWord_1793751).sum := by decide
  have hdescent : baseEnd_1793751 < baseStart_1793751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793756 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1793756 : Nat := 118140960795 + 1793756 * 2 ^ 59
def prefixEnd_1793756 : Nat := 4983230072969 + 3 ^ 40 * 1793756 * 2
def baseEnd_1793756 : Nat := 921059004886389155100673

theorem tailTrace_1793756 : CollatzResearch.WordTrace tailWord_1793756 prefixEnd_1793756 921059004886389155100673 := by
  unfold tailWord_1793756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32711828044767917990104561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43615770726357223986806081 32711828044767917990104561)
  ·
    refine ⟨24533871033575938492578421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32711828044767917990104561 24533871033575938492578421)
    ·
      refine ⟨2300050409397744233679227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24533871033575938492578421 2300050409397744233679227)
      ·
        refine ⟨3450075614096616350518841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300050409397744233679227 3450075614096616350518841)
        ·
          refine ⟨2587556710572462262889131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450075614096616350518841 2587556710572462262889131)
          ·
            refine ⟨3881335065858693394333697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587556710572462262889131 3881335065858693394333697)
            ·
              refine ⟨2911001299394020045750273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881335065858693394333697 2911001299394020045750273)
              ·
                refine ⟨2183250974545515034312705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911001299394020045750273 2183250974545515034312705)
                ·
                  refine ⟨1637438230909136275734529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183250974545515034312705 1637438230909136275734529)
                  ·
                    refine ⟨1228078673181852206800897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1637438230909136275734529 1228078673181852206800897)
                    ·
                      refine ⟨921059004886389155100673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228078673181852206800897 921059004886389155100673)
                      ·
                        rfl

theorem cell23_1793756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1793756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793756 prefixEnd_1793756 := by exact prefixLift 1793756
  have htrace : WordTrace (prefixWord ++ tailWord_1793756) baseStart_1793756 baseEnd_1793756 := by
    simpa [prefixWord, tailWord_1793756, baseEnd_1793756] using wordTrace_append hprefix tailTrace_1793756
  have hstable : (prefixWord ++ tailWord_1793756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793756).length < 2 ^ (prefixWord ++ tailWord_1793756).sum := by decide
  have hdescent : baseEnd_1793756 < baseStart_1793756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793768 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1793768 : Nat := 118140960795 + 1793768 * 2 ^ 59
def prefixEnd_1793768 : Nat := 4983230072969 + 3 ^ 40 * 1793768 * 2
def baseEnd_1793768 : Nat := 921065166654243108150617

theorem tailTrace_1793768 : CollatzResearch.WordTrace tailWord_1793768 prefixEnd_1793768 921065166654243108150617 := by
  unfold tailWord_1793768
  simp only [CollatzResearch.WordTrace]
  refine ⟨32712046882746181014822979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43616062510328241353097305 32712046882746181014822979)
  ·
    refine ⟨49068070324119271522234469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32712046882746181014822979 49068070324119271522234469)
    ·
      refine ⟨9200263185772363410418963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49068070324119271522234469 9200263185772363410418963)
      ·
        refine ⟨13800394778658545115628445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200263185772363410418963 13800394778658545115628445)
        ·
          refine ⟨5175148041996954418360667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13800394778658545115628445 5175148041996954418360667)
          ·
            refine ⟨7762722062995431627541001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175148041996954418360667 7762722062995431627541001)
            ·
              refine ⟨5822041547246573720655751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762722062995431627541001 5822041547246573720655751)
              ·
                refine ⟨8733062320869860580983627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822041547246573720655751 8733062320869860580983627)
                ·
                  refine ⟨13099593481304790871475441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733062320869860580983627 13099593481304790871475441)
                  ·
                    refine ⟨9824695110978593153606581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13099593481304790871475441 9824695110978593153606581)
                    ·
                      refine ⟨921065166654243108150617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9824695110978593153606581 921065166654243108150617)
                      ·
                        rfl

theorem cell23_1793768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1793768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793768 prefixEnd_1793768 := by exact prefixLift 1793768
  have htrace : WordTrace (prefixWord ++ tailWord_1793768) baseStart_1793768 baseEnd_1793768 := by
    simpa [prefixWord, tailWord_1793768, baseEnd_1793768] using wordTrace_append hprefix tailTrace_1793768
  have hstable : (prefixWord ++ tailWord_1793768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793768).length < 2 ^ (prefixWord ++ tailWord_1793768).sum := by decide
  have hdescent : baseEnd_1793768 < baseStart_1793768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793778 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1793778 : Nat := 118140960795 + 1793778 * 2 ^ 59
def prefixEnd_1793778 : Nat := 4983230072969 + 3 ^ 40 * 1793778 * 2
def baseEnd_1793778 : Nat := 921070301460788069025571

theorem tailTrace_1793778 : CollatzResearch.WordTrace tailWord_1793778 prefixEnd_1793778 921070301460788069025571 := by
  unfold tailWord_1793778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356114623864033434377497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43616305663637422491673325 16356114623864033434377497)
  ·
    refine ⟨12267085967898025075783123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16356114623864033434377497 12267085967898025075783123)
    ·
      refine ⟨18400628951847037613674685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12267085967898025075783123 18400628951847037613674685)
      ·
        refine ⟨6900235856942639105128007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18400628951847037613674685 6900235856942639105128007)
        ·
          refine ⟨10350353785413958657692011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900235856942639105128007 10350353785413958657692011)
          ·
            refine ⟨15525530678120937986538017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350353785413958657692011 15525530678120937986538017)
            ·
              refine ⟨11644148008590703489903513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15525530678120937986538017 11644148008590703489903513)
              ·
                refine ⟨8733111006443027617427635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11644148008590703489903513 8733111006443027617427635)
                ·
                  refine ⟨13099666509664541426141453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733111006443027617427635 13099666509664541426141453)
                  ·
                    refine ⟨4912374941124203034803045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13099666509664541426141453 4912374941124203034803045)
                    ·
                      refine ⟨921070301460788069025571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4912374941124203034803045 921070301460788069025571)
                      ·
                        rfl

theorem cell23_1793778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1793778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793778 prefixEnd_1793778 := by exact prefixLift 1793778
  have htrace : WordTrace (prefixWord ++ tailWord_1793778) baseStart_1793778 baseEnd_1793778 := by
    simpa [prefixWord, tailWord_1793778, baseEnd_1793778] using wordTrace_append hprefix tailTrace_1793778
  have hstable : (prefixWord ++ tailWord_1793778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793778).length < 2 ^ (prefixWord ++ tailWord_1793778).sum := by decide
  have hdescent : baseEnd_1793778 < baseStart_1793778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793801 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 8]
def baseStart_1793801 : Nat := 118140960795 + 1793801 * 2 ^ 59
def prefixEnd_1793801 : Nat := 4983230072969 + 3 ^ 40 * 1793801 * 2
def baseEnd_1793801 : Nat := 102342456835093497670885

theorem tailTrace_1793801 : CollatzResearch.WordTrace tailWord_1793801 prefixEnd_1793801 102342456835093497670885 := by
  unfold tailWord_1793801
  simp only [CollatzResearch.WordTrace]
  refine ⟨65425297374372808665597257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43616864916248539110398171 65425297374372808665597257)
  ·
    refine ⟨49068973030779606499197943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65425297374372808665597257 49068973030779606499197943)
    ·
      refine ⟨73603459546169409748796915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49068973030779606499197943 73603459546169409748796915)
      ·
        refine ⟨110405189319254114623195373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73603459546169409748796915 110405189319254114623195373)
        ·
          refine ⟨41401945994720292983698265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110405189319254114623195373 41401945994720292983698265)
          ·
            refine ⟨31051459496040219737773699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41401945994720292983698265 31051459496040219737773699)
            ·
              refine ⟨46577189244060329606660549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31051459496040219737773699 46577189244060329606660549)
              ·
                refine ⟨8733222983261311801248853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46577189244060329606660549 8733222983261311801248853)
                ·
                  refine ⟨102342456835093497670885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8733222983261311801248853 102342456835093497670885)
                  ·
                    rfl

theorem cell23_1793801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_1793801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793801 prefixEnd_1793801 := by exact prefixLift 1793801
  have htrace : WordTrace (prefixWord ++ tailWord_1793801) baseStart_1793801 baseEnd_1793801 := by
    simpa [prefixWord, tailWord_1793801, baseEnd_1793801] using wordTrace_append hprefix tailTrace_1793801
  have hstable : (prefixWord ++ tailWord_1793801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793801).length < 2 ^ (prefixWord ++ tailWord_1793801).sum := by decide
  have hdescent : baseEnd_1793801 < baseStart_1793801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793818 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_1793818 : Nat := 118140960795 + 1793818 * 2 ^ 59
def prefixEnd_1793818 : Nat := 4983230072969 + 3 ^ 40 * 1793818 * 2
def baseEnd_1793818 : Nat := 102343426742996434725043

theorem tailTrace_1793818 : CollatzResearch.WordTrace tailWord_1793818 prefixEnd_1793818 102343426742996434725043 := by
  unfold tailWord_1793818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356479353827805142241527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43617278276874147045977405 16356479353827805142241527)
  ·
    refine ⟨24534719030741707713362291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16356479353827805142241527 24534719030741707713362291)
    ·
      refine ⟨36802078546112561570043437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24534719030741707713362291 36802078546112561570043437)
      ·
        refine ⟨13800779454792210588766289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36802078546112561570043437 13800779454792210588766289)
        ·
          refine ⟨10350584591094157941574717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13800779454792210588766289 10350584591094157941574717)
          ·
            refine ⟨3881469221660309228090519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10350584591094157941574717 3881469221660309228090519)
            ·
              refine ⟨5822203832490463842135779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881469221660309228090519 5822203832490463842135779)
              ·
                refine ⟨8733305748735695763203669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822203832490463842135779 8733305748735695763203669)
                ·
                  refine ⟨102343426742996434725043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8733305748735695763203669 102343426742996434725043)
                  ·
                    rfl

theorem cell23_1793818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_1793818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793818 prefixEnd_1793818 := by exact prefixLift 1793818
  have htrace : WordTrace (prefixWord ++ tailWord_1793818) baseStart_1793818 baseEnd_1793818 := by
    simpa [prefixWord, tailWord_1793818, baseEnd_1793818] using wordTrace_append hprefix tailTrace_1793818
  have hstable : (prefixWord ++ tailWord_1793818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793818).length < 2 ^ (prefixWord ++ tailWord_1793818).sum := by decide
  have hdescent : baseEnd_1793818 < baseStart_1793818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793879 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1793879 : Nat := 118140960795 + 1793879 * 2 ^ 59
def prefixEnd_1793879 : Nat := 4983230072969 + 3 ^ 40 * 1793879 * 2
def baseEnd_1793879 : Nat := 921122163006892173862607

theorem tailTrace_1793879 : CollatzResearch.WordTrace tailWord_1793879 prefixEnd_1793879 921122163006892173862607 := by
  unfold tailWord_1793879
  simp only [CollatzResearch.WordTrace]
  refine ⟨65428142268090227986936691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43618761512060151991291127 65428142268090227986936691)
  ·
    refine ⟨98142213402135341980405037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65428142268090227986936691 98142213402135341980405037)
    ·
      refine ⟨36803330025800753242651889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98142213402135341980405037 36803330025800753242651889)
      ·
        refine ⟨27602497519350564931988917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36803330025800753242651889 27602497519350564931988917)
        ·
          refine ⟨2587734142439115462373961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27602497519350564931988917 2587734142439115462373961)
          ·
            refine ⟨1940800606829336596780471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2587734142439115462373961 1940800606829336596780471)
            ·
              refine ⟨2911200910244004895170707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940800606829336596780471 2911200910244004895170707)
              ·
                refine ⟨4366801365366007342756061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911200910244004895170707 4366801365366007342756061)
                ·
                  refine ⟨1637550512012252753533523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4366801365366007342756061 1637550512012252753533523)
                  ·
                    refine ⟨2456325768018379130300285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637550512012252753533523 2456325768018379130300285)
                    ·
                      refine ⟨921122163006892173862607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456325768018379130300285 921122163006892173862607)
                      ·
                        rfl

theorem cell23_1793879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1793879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793879 prefixEnd_1793879 := by exact prefixLift 1793879
  have htrace : WordTrace (prefixWord ++ tailWord_1793879) baseStart_1793879 baseEnd_1793879 := by
    simpa [prefixWord, tailWord_1793879, baseEnd_1793879] using wordTrace_append hprefix tailTrace_1793879
  have hstable : (prefixWord ++ tailWord_1793879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793879).length < 2 ^ (prefixWord ++ tailWord_1793879).sum := by decide
  have hdescent : baseEnd_1793879 < baseStart_1793879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793902 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1793902 : Nat := 118140960795 + 1793902 * 2 ^ 59
def prefixEnd_1793902 : Nat := 4983230072969 + 3 ^ 40 * 1793902 * 2
def baseEnd_1793902 : Nat := 921133973061945583875001

theorem tailTrace_1793902 : CollatzResearch.WordTrace tailWord_1793902 prefixEnd_1793902 921133973061945583875001 := by
  unfold tailWord_1793902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178622643375862864377995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43619320764671268610015973 8178622643375862864377995)
  ·
    refine ⟨12267933965063794296566993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8178622643375862864377995 12267933965063794296566993)
    ·
      refine ⟨9200950473797845722425245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12267933965063794296566993 9200950473797845722425245)
      ·
        refine ⟨3450356427674192145909467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9200950473797845722425245 3450356427674192145909467)
        ·
          refine ⟨5175534641511288218864201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450356427674192145909467 5175534641511288218864201)
          ·
            refine ⟨3881650981133466164148151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175534641511288218864201 3881650981133466164148151)
            ·
              refine ⟨5822476471700199246222227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881650981133466164148151 5822476471700199246222227)
              ·
                refine ⟨8733714707550298869333341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822476471700199246222227 8733714707550298869333341)
                ·
                  refine ⟨3275143015331362076000003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8733714707550298869333341 3275143015331362076000003)
                  ·
                    refine ⟨4912714522997043114000005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3275143015331362076000003 4912714522997043114000005)
                    ·
                      refine ⟨921133973061945583875001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4912714522997043114000005 921133973061945583875001)
                      ·
                        rfl

theorem cell23_1793902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1793902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793902 prefixEnd_1793902 := by exact prefixLift 1793902
  have htrace : WordTrace (prefixWord ++ tailWord_1793902) baseStart_1793902 baseEnd_1793902 := by
    simpa [prefixWord, tailWord_1793902, baseEnd_1793902] using wordTrace_append hprefix tailTrace_1793902
  have hstable : (prefixWord ++ tailWord_1793902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793902).length < 2 ^ (prefixWord ++ tailWord_1793902).sum := by decide
  have hdescent : baseEnd_1793902 < baseStart_1793902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793905 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_1793905 : Nat := 118140960795 + 1793905 * 2 ^ 59
def prefixEnd_1793905 : Nat := 4983230072969 + 3 ^ 40 * 1793905 * 2
def baseEnd_1793905 : Nat := 921135513503909072137487

theorem tailTrace_1793905 : CollatzResearch.WordTrace tailWord_1793905 prefixEnd_1793905 921135513503909072137487 := by
  unfold tailWord_1793905
  simp only [CollatzResearch.WordTrace]
  refine ⟨65429090565996034427383169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43619393710664022951588779 65429090565996034427383169)
  ·
    refine ⟨49071817924497025820537377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65429090565996034427383169 49071817924497025820537377)
    ·
      refine ⟨36803863443372769365403033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49071817924497025820537377 36803863443372769365403033)
      ·
        refine ⟨27602897582529577024052275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36803863443372769365403033 27602897582529577024052275)
        ·
          refine ⟨41404346373794365536078413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27602897582529577024052275 41404346373794365536078413)
          ·
            refine ⟨15526629890172887076029405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41404346373794365536078413 15526629890172887076029405)
            ·
              refine ⟨5822486208814832653511027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15526629890172887076029405 5822486208814832653511027)
              ·
                refine ⟨8733729313222248980266541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822486208814832653511027 8733729313222248980266541)
                ·
                  refine ⟨3275148492458343367599953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8733729313222248980266541 3275148492458343367599953)
                  ·
                    refine ⟨2456361369343757525699965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3275148492458343367599953 2456361369343757525699965)
                    ·
                      refine ⟨921135513503909072137487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456361369343757525699965 921135513503909072137487)
                      ·
                        rfl

theorem cell23_1793905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_1793905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793905 prefixEnd_1793905 := by exact prefixLift 1793905
  have htrace : WordTrace (prefixWord ++ tailWord_1793905) baseStart_1793905 baseEnd_1793905 := by
    simpa [prefixWord, tailWord_1793905, baseEnd_1793905] using wordTrace_append hprefix tailTrace_1793905
  have hstable : (prefixWord ++ tailWord_1793905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793905).length < 2 ^ (prefixWord ++ tailWord_1793905).sum := by decide
  have hdescent : baseEnd_1793905 < baseStart_1793905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793919 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 1, 2, 2]
def baseStart_1793919 : Nat := 118140960795 + 1793919 * 2 ^ 59
def prefixEnd_1793919 : Nat := 4983230072969 + 3 ^ 40 * 1793919 * 2
def baseEnd_1793919 : Nat := 921142702233072017362423

theorem tailTrace_1793919 : CollatzResearch.WordTrace tailWord_1793919 prefixEnd_1793919 921142702233072017362423 := by
  unfold tailWord_1793919
  simp only [CollatzResearch.WordTrace]
  refine ⟨65429601187945314818392811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43619734125296876545595207 65429601187945314818392811)
  ·
    refine ⟨98144401781917972227589217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65429601187945314818392811 98144401781917972227589217)
    ·
      refine ⟨73608301336438479170691913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98144401781917972227589217 73608301336438479170691913)
      ·
        refine ⟨55206226002328859378018935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73608301336438479170691913 55206226002328859378018935)
        ·
          refine ⟨82809339003493289067028403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55206226002328859378018935 82809339003493289067028403)
          ·
            refine ⟨124214008505239933600542605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82809339003493289067028403 124214008505239933600542605)
            ·
              refine ⟨46580253189464975100203477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124214008505239933600542605 46580253189464975100203477)
              ·
                refine ⟨1091724684128085353911019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46580253189464975100203477 1091724684128085353911019)
                ·
                  refine ⟨1637587026192128030866529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091724684128085353911019 1637587026192128030866529)
                  ·
                    refine ⟨1228190269644096023149897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1637587026192128030866529 1228190269644096023149897)
                    ·
                      refine ⟨921142702233072017362423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228190269644096023149897 921142702233072017362423)
                      ·
                        rfl

theorem cell23_1793919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_1793919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793919 prefixEnd_1793919 := by exact prefixLift 1793919
  have htrace : WordTrace (prefixWord ++ tailWord_1793919) baseStart_1793919 baseEnd_1793919 := by
    simpa [prefixWord, tailWord_1793919, baseEnd_1793919] using wordTrace_append hprefix tailTrace_1793919
  have hstable : (prefixWord ++ tailWord_1793919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793919).length < 2 ^ (prefixWord ++ tailWord_1793919).sum := by decide
  have hdescent : baseEnd_1793919 < baseStart_1793919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793930 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1793930 : Nat := 118140960795 + 1793930 * 2 ^ 59
def prefixEnd_1793930 : Nat := 4983230072969 + 3 ^ 40 * 1793930 * 2
def baseEnd_1793930 : Nat := 921148350520271474324873

theorem tailTrace_1793930 : CollatzResearch.WordTrace tailWord_1793930 prefixEnd_1793930 921148350520271474324873 := by
  unfold tailWord_1793930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357500597726365924260811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43620001593936975798028829 16357500597726365924260811)
  ·
    refine ⟨24536250896589548886391217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16357500597726365924260811 24536250896589548886391217)
    ·
      refine ⟨18402188172442161664793413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24536250896589548886391217 18402188172442161664793413)
      ·
        refine ⟨3450410282332905312148765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18402188172442161664793413 3450410282332905312148765)
        ·
          refine ⟨1293903855874839492055787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3450410282332905312148765 1293903855874839492055787)
          ·
            refine ⟨1940855783812259238083681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293903855874839492055787 1940855783812259238083681)
            ·
              refine ⟨1455641837859194428562761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940855783812259238083681 1455641837859194428562761)
              ·
                refine ⟨1091731378394395821422071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455641837859194428562761 1091731378394395821422071)
                ·
                  refine ⟨1637597067591593732133107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091731378394395821422071 1637597067591593732133107)
                  ·
                    refine ⟨2456395601387390598199661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637597067591593732133107 2456395601387390598199661)
                    ·
                      refine ⟨921148350520271474324873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456395601387390598199661 921148350520271474324873)
                      ·
                        rfl

theorem cell23_1793930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1793930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793930 prefixEnd_1793930 := by exact prefixLift 1793930
  have htrace : WordTrace (prefixWord ++ tailWord_1793930) baseStart_1793930 baseEnd_1793930 := by
    simpa [prefixWord, tailWord_1793930, baseEnd_1793930] using wordTrace_append hprefix tailTrace_1793930
  have hstable : (prefixWord ++ tailWord_1793930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793930).length < 2 ^ (prefixWord ++ tailWord_1793930).sum := by decide
  have hdescent : baseEnd_1793930 < baseStart_1793930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1793935 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 3]
def baseStart_1793935 : Nat := 118140960795 + 1793935 * 2 ^ 59
def prefixEnd_1793935 : Nat := 4983230072969 + 3 ^ 40 * 1793935 * 2
def baseEnd_1793935 : Nat := 921150917923543954762349

theorem tailTrace_1793935 : CollatzResearch.WordTrace tailWord_1793935 prefixEnd_1793935 921150917923543954762349 := by
  unfold tailWord_1793935
  simp only [CollatzResearch.WordTrace]
  refine ⟨65430184755887349550975259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43620123170591566367316839 65430184755887349550975259)
  ·
    refine ⟨98145277133831024326462889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65430184755887349550975259 98145277133831024326462889)
    ·
      refine ⟨73608957850373268244847167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98145277133831024326462889 73608957850373268244847167)
      ·
        refine ⟨110413436775559902367270751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73608957850373268244847167 110413436775559902367270751)
        ·
          refine ⟨165620155163339853550906127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110413436775559902367270751 165620155163339853550906127)
          ·
            refine ⟨248430232745009780326359191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165620155163339853550906127 248430232745009780326359191)
            ·
              refine ⟨372645349117514670489538787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248430232745009780326359191 372645349117514670489538787)
              ·
                refine ⟨558968023676272005734308181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372645349117514670489538787 558968023676272005734308181)
                ·
                  refine ⟨1637601631864078141799731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 558968023676272005734308181 1637601631864078141799731)
                  ·
                    refine ⟨2456402447796117212699597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637601631864078141799731 2456402447796117212699597)
                    ·
                      refine ⟨921150917923543954762349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456402447796117212699597 921150917923543954762349)
                      ·
                        rfl

theorem cell23_1793935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_1793935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1793935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1793935 prefixEnd_1793935 := by exact prefixLift 1793935
  have htrace : WordTrace (prefixWord ++ tailWord_1793935) baseStart_1793935 baseEnd_1793935 := by
    simpa [prefixWord, tailWord_1793935, baseEnd_1793935] using wordTrace_append hprefix tailTrace_1793935
  have hstable : (prefixWord ++ tailWord_1793935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1793935).length < 2 ^ (prefixWord ++ tailWord_1793935).sum := by decide
  have hdescent : baseEnd_1793935 < baseStart_1793935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1793935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794015 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 7]
def baseStart_1794015 : Nat := 118140960795 + 1794015 * 2 ^ 59
def prefixEnd_1794015 : Nat := 4983230072969 + 3 ^ 40 * 1794015 * 2
def baseEnd_1794015 : Nat := 102354666263989293529109

theorem tailTrace_1794015 : CollatzResearch.WordTrace tailWord_1794015 prefixEnd_1794015 102354666263989293529109 := by
  unfold tailWord_1794015
  simp only [CollatzResearch.WordTrace]
  refine ⟨65433102595597523213887499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43622068397065015475924999 65433102595597523213887499)
  ·
    refine ⟨98149653893396284820831249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65433102595597523213887499 98149653893396284820831249)
    ·
      refine ⟨73612240420047213615623437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98149653893396284820831249 73612240420047213615623437)
      ·
        refine ⟨27604590157517705105858789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73612240420047213615623437 27604590157517705105858789)
        ·
          refine ⟨5175860654534569707348523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27604590157517705105858789 5175860654534569707348523)
          ·
            refine ⟨7763790981801854561022785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175860654534569707348523 7763790981801854561022785)
            ·
              refine ⟨5822843236351390920767089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7763790981801854561022785 5822843236351390920767089)
              ·
                refine ⟨4367132427263543190575317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5822843236351390920767089 4367132427263543190575317)
                ·
                  refine ⟨102354666263989293529109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4367132427263543190575317 102354666263989293529109)
                  ·
                    rfl

theorem cell23_1794015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 7].length) (baseStart_1794015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794015 prefixEnd_1794015 := by exact prefixLift 1794015
  have htrace : WordTrace (prefixWord ++ tailWord_1794015) baseStart_1794015 baseEnd_1794015 := by
    simpa [prefixWord, tailWord_1794015, baseEnd_1794015] using wordTrace_append hprefix tailTrace_1794015
  have hstable : (prefixWord ++ tailWord_1794015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794015).length < 2 ^ (prefixWord ++ tailWord_1794015).sum := by decide
  have hdescent : baseEnd_1794015 < baseStart_1794015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794029 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1794029 : Nat := 118140960795 + 1794029 * 2 ^ 59
def prefixEnd_1794029 : Nat := 4983230072969 + 3 ^ 40 * 1794029 * 2
def baseEnd_1794029 : Nat := 921199185105066586986917

theorem tailTrace_1794029 : CollatzResearch.WordTrace tailWord_1794029 prefixEnd_1794029 921199185105066586986917 := by
  unfold tailWord_1794029
  simp only [CollatzResearch.WordTrace]
  refine ⟨65433613217546803604897141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43622408811697869069931427 65433613217546803604897141)
  ·
    refine ⟨6134401239145012837959107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65433613217546803604897141 6134401239145012837959107)
    ·
      refine ⟨9201601858717519256938661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134401239145012837959107 9201601858717519256938661)
      ·
        refine ⟨1725300348509534860675999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9201601858717519256938661 1725300348509534860675999)
        ·
          refine ⟨2587950522764302291013999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725300348509534860675999 2587950522764302291013999)
          ·
            refine ⟨3881925784146453436520999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587950522764302291013999 3881925784146453436520999)
            ·
              refine ⟨5822888676219680154781499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881925784146453436520999 5822888676219680154781499)
              ·
                refine ⟨8734333014329520232172249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822888676219680154781499 8734333014329520232172249)
                ·
                  refine ⟨6550749760747140174129187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734333014329520232172249 6550749760747140174129187)
                  ·
                    refine ⟨9826124641120710261193781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6550749760747140174129187 9826124641120710261193781)
                    ·
                      refine ⟨921199185105066586986917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9826124641120710261193781 921199185105066586986917)
                      ·
                        rfl

theorem cell23_1794029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1794029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794029 prefixEnd_1794029 := by exact prefixLift 1794029
  have htrace : WordTrace (prefixWord ++ tailWord_1794029) baseStart_1794029 baseEnd_1794029 := by
    simpa [prefixWord, tailWord_1794029, baseEnd_1794029] using wordTrace_append hprefix tailTrace_1794029
  have hstable : (prefixWord ++ tailWord_1794029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794029).length < 2 ^ (prefixWord ++ tailWord_1794029).sum := by decide
  have hdescent : baseEnd_1794029 < baseStart_1794029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794032 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 5]
def baseStart_1794032 : Nat := 118140960795 + 1794032 * 2 ^ 59
def prefixEnd_1794032 : Nat := 4983230072969 + 3 ^ 40 * 1794032 * 2
def baseEnd_1794032 : Nat := 102355636171892230583267

theorem tailTrace_1794032 : CollatzResearch.WordTrace tailWord_1794032 prefixEnd_1794032 102355636171892230583267 := by
  unfold tailWord_1794032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32716861318267967558628175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43622481757690623411504233 32716861318267967558628175)
  ·
    refine ⟨49075291977401951337942263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32716861318267967558628175 49075291977401951337942263)
    ·
      refine ⟨73612937966102927006913395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49075291977401951337942263 73612937966102927006913395)
      ·
        refine ⟨110419406949154390510370093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73612937966102927006913395 110419406949154390510370093)
        ·
          refine ⟨41407277605932896441388785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110419406949154390510370093 41407277605932896441388785)
          ·
            refine ⟨31055458204449672331041589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41407277605932896441388785 31055458204449672331041589)
            ·
              refine ⟨2911449206667156781035149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31055458204449672331041589 2911449206667156781035149)
              ·
                refine ⟨1091793452500183792888181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2911449206667156781035149 1091793452500183792888181)
                ·
                  refine ⟨102355636171892230583267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1091793452500183792888181 102355636171892230583267)
                  ·
                    rfl

theorem cell23_1794032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 5].length) (baseStart_1794032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794032 prefixEnd_1794032 := by exact prefixLift 1794032
  have htrace : WordTrace (prefixWord ++ tailWord_1794032) baseStart_1794032 baseEnd_1794032 := by
    simpa [prefixWord, tailWord_1794032, baseEnd_1794032] using wordTrace_append hprefix tailTrace_1794032
  have hstable : (prefixWord ++ tailWord_1794032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794032).length < 2 ^ (prefixWord ++ tailWord_1794032).sum := by decide
  have hdescent : baseEnd_1794032 < baseStart_1794032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794045 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1794045 : Nat := 118140960795 + 1794045 * 2 ^ 59
def prefixEnd_1794045 : Nat := 4983230072969 + 3 ^ 40 * 1794045 * 2
def baseEnd_1794045 : Nat := 307069133598512841462281

theorem tailTrace_1794045 : CollatzResearch.WordTrace tailWord_1794045 prefixEnd_1794045 307069133598512841462281 := by
  unfold tailWord_1794045
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434196785488838337479589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43622797856992558891653059 65434196785488838337479589)
  ·
    refine ⟨12268911897279157188277423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65434196785488838337479589 12268911897279157188277423)
    ·
      refine ⟨18403367845918735782416135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12268911897279157188277423 18403367845918735782416135)
      ·
        refine ⟨27605051768878103673624203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403367845918735782416135 27605051768878103673624203)
        ·
          refine ⟨41407577653317155510436305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27605051768878103673624203 41407577653317155510436305)
          ·
            refine ⟨31055683239987866632827229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41407577653317155510436305 31055683239987866632827229)
            ·
              refine ⟨11645881214995449987310211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31055683239987866632827229 11645881214995449987310211)
              ·
                refine ⟨17468821822493174980965317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645881214995449987310211 17468821822493174980965317)
                ·
                  refine ⟨3275404091717470308930997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17468821822493174980965317 3275404091717470308930997)
                  ·
                    refine ⟨307069133598512841462281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3275404091717470308930997 307069133598512841462281)
                    ·
                      rfl

theorem cell23_1794045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1794045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794045 prefixEnd_1794045 := by exact prefixLift 1794045
  have htrace : WordTrace (prefixWord ++ tailWord_1794045) baseStart_1794045 baseEnd_1794045 := by
    simpa [prefixWord, tailWord_1794045, baseEnd_1794045] using wordTrace_append hprefix tailTrace_1794045
  have hstable : (prefixWord ++ tailWord_1794045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794045).length < 2 ^ (prefixWord ++ tailWord_1794045).sum := by decide
  have hdescent : baseEnd_1794045 < baseStart_1794045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794049 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 5]
def baseStart_1794049 : Nat := 118140960795 + 1794049 * 2 ^ 59
def prefixEnd_1794049 : Nat := 4983230072969 + 3 ^ 40 * 1794049 * 2
def baseEnd_1794049 : Nat := 102356606079795167637425

theorem tailTrace_1794049 : CollatzResearch.WordTrace tailWord_1794049 prefixEnd_1794049 102356606079795167637425 := by
  unfold tailWord_1794049
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434342677474347020625201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43622895118316231347083467 65434342677474347020625201)
  ·
    refine ⟨49075757008105760265468901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65434342677474347020625201 49075757008105760265468901)
    ·
      refine ⟨9201704439019830049775419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49075757008105760265468901 9201704439019830049775419)
      ·
        refine ⟨13802556658529745074663129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201704439019830049775419 13802556658529745074663129)
        ·
          refine ⟨10351917493897308805997347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13802556658529745074663129 10351917493897308805997347)
          ·
            refine ⟨15527876240845963208996021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351917493897308805997347 15527876240845963208996021)
            ·
              refine ⟨1455738397579309050843377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15527876240845963208996021 1455738397579309050843377)
              ·
                refine ⟨1091803798184481788132533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455738397579309050843377 1091803798184481788132533)
                ·
                  refine ⟨102356606079795167637425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1091803798184481788132533 102356606079795167637425)
                  ·
                    rfl

theorem cell23_1794049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 5].length) (baseStart_1794049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794049 prefixEnd_1794049 := by exact prefixLift 1794049
  have htrace : WordTrace (prefixWord ++ tailWord_1794049) baseStart_1794049 baseEnd_1794049 := by
    simpa [prefixWord, tailWord_1794049, baseEnd_1794049] using wordTrace_append hprefix tailTrace_1794049
  have hstable : (prefixWord ++ tailWord_1794049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794049).length < 2 ^ (prefixWord ++ tailWord_1794049).sum := by decide
  have hdescent : baseEnd_1794049 < baseStart_1794049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794054 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1794054 : Nat := 118140960795 + 1794054 * 2 ^ 59
def prefixEnd_1794054 : Nat := 4983230072969 + 3 ^ 40 * 1794054 * 2
def baseEnd_1794054 : Nat := 921212022121428989174303

theorem tailTrace_1794054 : CollatzResearch.WordTrace tailWord_1794054 prefixEnd_1794054 921212022121428989174303 := by
  unfold tailWord_1794054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044828907576757277329913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43623016694970821916371477 2044828907576757277329913)
  ·
    refine ⟨1533621680682567957997435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2044828907576757277329913 1533621680682567957997435)
    ·
      refine ⟨2300432521023851936996153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533621680682567957997435 2300432521023851936996153)
      ·
        refine ⟨1725324390767888952747115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2300432521023851936996153 1725324390767888952747115)
        ·
          refine ⟨2587986586151833429120673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725324390767888952747115 2587986586151833429120673)
          ·
            refine ⟨1940989939613875071840505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2587986586151833429120673 1940989939613875071840505)
            ·
              refine ⟨1455742454710406303880379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940989939613875071840505 1455742454710406303880379)
              ·
                refine ⟨2183613682065609455820569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455742454710406303880379 2183613682065609455820569)
                ·
                  refine ⟨1637710261549207091865427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2183613682065609455820569 1637710261549207091865427)
                  ·
                    refine ⟨2456565392323810637798141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637710261549207091865427 2456565392323810637798141)
                    ·
                      refine ⟨921212022121428989174303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456565392323810637798141 921212022121428989174303)
                      ·
                        rfl

theorem cell23_1794054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1794054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794054 prefixEnd_1794054 := by exact prefixLift 1794054
  have htrace : WordTrace (prefixWord ++ tailWord_1794054) baseStart_1794054 baseEnd_1794054 := by
    simpa [prefixWord, tailWord_1794054, baseEnd_1794054] using wordTrace_append hprefix tailTrace_1794054
  have hstable : (prefixWord ++ tailWord_1794054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794054).length < 2 ^ (prefixWord ++ tailWord_1794054).sum := by decide
  have hdescent : baseEnd_1794054 < baseStart_1794054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794055 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1794055 : Nat := 118140960795 + 1794055 * 2 ^ 59
def prefixEnd_1794055 : Nat := 4983230072969 + 3 ^ 40 * 1794055 * 2
def baseEnd_1794055 : Nat := 921212535602083485261797

theorem tailTrace_1794055 : CollatzResearch.WordTrace tailWord_1794055 prefixEnd_1794055 921212535602083485261797 := by
  unfold tailWord_1794055
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434561515452610045343619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43623041010301740030229079 65434561515452610045343619)
  ·
    refine ⟨98151842273178915068015429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65434561515452610045343619 98151842273178915068015429)
    ·
      refine ⟨18403470426221046575252893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98151842273178915068015429 18403470426221046575252893)
      ·
        refine ⟨6901301409832892465719835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18403470426221046575252893 6901301409832892465719835)
        ·
          refine ⟨10351952114749338698579753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901301409832892465719835 10351952114749338698579753)
          ·
            refine ⟨7763964086062004023934815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10351952114749338698579753 7763964086062004023934815)
            ·
              refine ⟨11645946129093006035902223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763964086062004023934815 11645946129093006035902223)
              ·
                refine ⟨17468919193639509053853335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645946129093006035902223 17468919193639509053853335)
                ·
                  refine ⟨26203378790459263580780003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17468919193639509053853335 26203378790459263580780003)
                  ·
                    refine ⟨39305068185688895371170005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26203378790459263580780003 39305068185688895371170005)
                    ·
                      refine ⟨921212535602083485261797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39305068185688895371170005 921212535602083485261797)
                      ·
                        rfl

theorem cell23_1794055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1794055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794055 prefixEnd_1794055 := by exact prefixLift 1794055
  have htrace : WordTrace (prefixWord ++ tailWord_1794055) baseStart_1794055 baseEnd_1794055 := by
    simpa [prefixWord, tailWord_1794055, baseEnd_1794055] using wordTrace_append hprefix tailTrace_1794055
  have hstable : (prefixWord ++ tailWord_1794055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794055).length < 2 ^ (prefixWord ++ tailWord_1794055).sum := by decide
  have hdescent : baseEnd_1794055 < baseStart_1794055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794100 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1794100 : Nat := 118140960795 + 1794100 * 2 ^ 59
def prefixEnd_1794100 : Nat := 4983230072969 + 3 ^ 40 * 1794100 * 2
def baseEnd_1794100 : Nat := 102359515803503978799899

theorem tailTrace_1794100 : CollatzResearch.WordTrace tailWord_1794100 prefixEnd_1794100 102359515803503978799899 := by
  unfold tailWord_1794100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32718101400144791365365877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43624135200193055153821169 32718101400144791365365877)
  ·
    refine ⟨3067322006263574190503051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32718101400144791365365877 3067322006263574190503051)
    ·
      refine ⟨4600983009395361285754577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067322006263574190503051 4600983009395361285754577)
      ·
        refine ⟨3450737257046520964315933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4600983009395361285754577 3450737257046520964315933)
        ·
          refine ⟨1294026471392445361618475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3450737257046520964315933 1294026471392445361618475)
          ·
            refine ⟨1941039707088668042427713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294026471392445361618475 1941039707088668042427713)
            ·
              refine ⟨1455779780316501031820785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941039707088668042427713 1455779780316501031820785)
              ·
                refine ⟨1091834835237375773865589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455779780316501031820785 1091834835237375773865589)
                ·
                  refine ⟨102359515803503978799899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1091834835237375773865589 102359515803503978799899)
                  ·
                    rfl

theorem cell23_1794100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1794100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794100 prefixEnd_1794100 := by exact prefixLift 1794100
  have htrace : WordTrace (prefixWord ++ tailWord_1794100) baseStart_1794100 baseEnd_1794100 := by
    simpa [prefixWord, tailWord_1794100, baseEnd_1794100] using wordTrace_append hprefix tailTrace_1794100
  have hstable : (prefixWord ++ tailWord_1794100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794100).length < 2 ^ (prefixWord ++ tailWord_1794100).sum := by decide
  have hdescent : baseEnd_1794100 < baseStart_1794100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794102 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1794102 : Nat := 118140960795 + 1794102 * 2 ^ 59
def prefixEnd_1794102 : Nat := 4983230072969 + 3 ^ 40 * 1794102 * 2
def baseEnd_1794102 : Nat := 921236669192844801374081

theorem tailTrace_1794102 : CollatzResearch.WordTrace tailWord_1794102 prefixEnd_1794102 921236669192844801374081 := by
  unfold tailWord_1794102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089767234142646067019035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43624183830854891381536373 4089767234142646067019035)
  ·
    refine ⟨6134650851213969100528553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089767234142646067019035 6134650851213969100528553)
    ·
      refine ⟨4600988138410476825396415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6134650851213969100528553 4600988138410476825396415)
      ·
        refine ⟨6901482207615715238094623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600988138410476825396415 6901482207615715238094623)
        ·
          refine ⟨10352223311423572857141935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901482207615715238094623 10352223311423572857141935)
          ·
            refine ⟨15528334967135359285712903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10352223311423572857141935 15528334967135359285712903)
            ·
              refine ⟨23292502450703038928569355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15528334967135359285712903 23292502450703038928569355)
              ·
                refine ⟨34938753676054558392854033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23292502450703038928569355 34938753676054558392854033)
                ·
                  refine ⟨26204065257040918794640525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34938753676054558392854033 26204065257040918794640525)
                  ·
                    refine ⟨9826524471390344547990197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26204065257040918794640525 9826524471390344547990197)
                    ·
                      refine ⟨921236669192844801374081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9826524471390344547990197 921236669192844801374081)
                      ·
                        rfl

theorem cell23_1794102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1794102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794102 prefixEnd_1794102 := by exact prefixLift 1794102
  have htrace : WordTrace (prefixWord ++ tailWord_1794102) baseStart_1794102 baseEnd_1794102 := by
    simpa [prefixWord, tailWord_1794102, baseEnd_1794102] using wordTrace_append hprefix tailTrace_1794102
  have hstable : (prefixWord ++ tailWord_1794102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794102).length < 2 ^ (prefixWord ++ tailWord_1794102).sum := by decide
  have hdescent : baseEnd_1794102 < baseStart_1794102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794145 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1794145 : Nat := 118140960795 + 1794145 * 2 ^ 59
def prefixEnd_1794145 : Nat := 4983230072969 + 3 ^ 40 * 1794145 * 2
def baseEnd_1794145 : Nat := 921258748860988133136383

theorem tailTrace_1794145 : CollatzResearch.WordTrace tailWord_1794145 prefixEnd_1794145 921258748860988133136383 := by
  unfold tailWord_1794145
  simp only [CollatzResearch.WordTrace]
  refine ⟨65437844085126555416119889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43625229390084370277413259 65437844085126555416119889)
  ·
    refine ⟨49078383063844916562089917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65437844085126555416119889 49078383063844916562089917)
    ·
      refine ⟨18404393648941843710783719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49078383063844916562089917 18404393648941843710783719)
      ·
        refine ⟨27606590473412765566175579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18404393648941843710783719 27606590473412765566175579)
        ·
          refine ⟨41409885710119148349263369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27606590473412765566175579 41409885710119148349263369)
          ·
            refine ⟨31057414282589361261947527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41409885710119148349263369 31057414282589361261947527)
            ·
              refine ⟨46586121423884041892921291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31057414282589361261947527 46586121423884041892921291)
              ·
                refine ⟨69879182135826062839381937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46586121423884041892921291 69879182135826062839381937)
                ·
                  refine ⟨52409386601869547129536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69879182135826062839381937 52409386601869547129536453)
                  ·
                    refine ⟨9826759987850540086788085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52409386601869547129536453 9826759987850540086788085)
                    ·
                      refine ⟨921258748860988133136383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9826759987850540086788085 921258748860988133136383)
                      ·
                        rfl

theorem cell23_1794145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1794145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794145 prefixEnd_1794145 := by exact prefixLift 1794145
  have htrace : WordTrace (prefixWord ++ tailWord_1794145) baseStart_1794145 baseEnd_1794145 := by
    simpa [prefixWord, tailWord_1794145, baseEnd_1794145] using wordTrace_append hprefix tailTrace_1794145
  have hstable : (prefixWord ++ tailWord_1794145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794145).length < 2 ^ (prefixWord ++ tailWord_1794145).sum := by decide
  have hdescent : baseEnd_1794145 < baseStart_1794145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794166 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1794166 : Nat := 118140960795 + 1794166 * 2 ^ 59
def prefixEnd_1794166 : Nat := 4983230072969 + 3 ^ 40 * 1794166 * 2
def baseEnd_1794166 : Nat := 921269531954732550973787

theorem tailTrace_1794166 : CollatzResearch.WordTrace tailWord_1794166 prefixEnd_1794166 921269531954732550973787 := by
  unfold tailWord_1794166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089913126128154750164647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43625740012033650668422901 4089913126128154750164647)
  ·
    refine ⟨6134869689192232125246971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4089913126128154750164647 6134869689192232125246971)
    ·
      refine ⟨9202304533788348187870457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6134869689192232125246971 9202304533788348187870457)
      ·
        refine ⟨6901728400341261140902843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9202304533788348187870457 6901728400341261140902843)
        ·
          refine ⟨10352592600511891711354265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901728400341261140902843 10352592600511891711354265)
          ·
            refine ⟨7764444450383918783515699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352592600511891711354265 7764444450383918783515699)
            ·
              refine ⟨11646666675575878175273549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764444450383918783515699 11646666675575878175273549)
              ·
                refine ⟨4367500003340954315727581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11646666675575878175273549 4367500003340954315727581)
                ·
                  refine ⟨1637812501252857868397843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4367500003340954315727581 1637812501252857868397843)
                  ·
                    refine ⟨2456718751879286802596765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637812501252857868397843 2456718751879286802596765)
                    ·
                      refine ⟨921269531954732550973787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456718751879286802596765 921269531954732550973787)
                      ·
                        rfl

theorem cell23_1794166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1794166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794166 prefixEnd_1794166 := by exact prefixLift 1794166
  have htrace : WordTrace (prefixWord ++ tailWord_1794166) baseStart_1794166 baseEnd_1794166 := by
    simpa [prefixWord, tailWord_1794166, baseEnd_1794166] using wordTrace_append hprefix tailTrace_1794166
  have hstable : (prefixWord ++ tailWord_1794166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794166).length < 2 ^ (prefixWord ++ tailWord_1794166).sum := by decide
  have hdescent : baseEnd_1794166 < baseStart_1794166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794200 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 1, 1, 3]
def baseStart_1794200 : Nat := 118140960795 + 1794200 * 2 ^ 59
def prefixEnd_1794200 : Nat := 4983230072969 + 3 ^ 40 * 1794200 * 2
def baseEnd_1794200 : Nat := 921286990296985417948631

theorem tailTrace_1794200 : CollatzResearch.WordTrace tailWord_1794200 prefixEnd_1794200 921286990296985417948631 := by
  unfold tailWord_1794200
  simp only [CollatzResearch.WordTrace]
  refine ⟨32719925049963649904686027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43626566733284866539581369 32719925049963649904686027)
  ·
    refine ⟨49079887574945474857029041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32719925049963649904686027 49079887574945474857029041)
    ·
      refine ⟨36809915681209106142771781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49079887574945474857029041 36809915681209106142771781)
      ·
        refine ⟨6901859190226707401769709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36809915681209106142771781 6901859190226707401769709)
        ·
          refine ⟨2588197196335015275663641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6901859190226707401769709 2588197196335015275663641)
          ·
            refine ⟨1941147897251261456747731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2588197196335015275663641 1941147897251261456747731)
            ·
              refine ⟨2911721845876892185121597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941147897251261456747731 2911721845876892185121597)
              ·
                refine ⟨1091895692203834569420599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2911721845876892185121597 1091895692203834569420599)
                ·
                  refine ⟨1637843538305751854130899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091895692203834569420599 1637843538305751854130899)
                  ·
                    refine ⟨2456765307458627781196349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1637843538305751854130899 2456765307458627781196349)
                    ·
                      refine ⟨921286990296985417948631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2456765307458627781196349 921286990296985417948631)
                      ·
                        rfl

theorem cell23_1794200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_1794200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794200 prefixEnd_1794200 := by exact prefixLift 1794200
  have htrace : WordTrace (prefixWord ++ tailWord_1794200) baseStart_1794200 baseEnd_1794200 := by
    simpa [prefixWord, tailWord_1794200, baseEnd_1794200] using wordTrace_append hprefix tailTrace_1794200
  have hstable : (prefixWord ++ tailWord_1794200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794200).length < 2 ^ (prefixWord ++ tailWord_1794200).sum := by decide
  have hdescent : baseEnd_1794200 < baseStart_1794200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794209 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1794209 : Nat := 118140960795 + 1794209 * 2 ^ 59
def prefixEnd_1794209 : Nat := 4983230072969 + 3 ^ 40 * 1794209 * 2
def baseEnd_1794209 : Nat := 921291611622875882736089

theorem tailTrace_1794209 : CollatzResearch.WordTrace tailWord_1794209 prefixEnd_1794209 921291611622875882736089 := by
  unfold tailWord_1794209
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440178356894694346449681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43626785571263129564299787 65440178356894694346449681)
  ·
    refine ⟨49080133767671020759837261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65440178356894694346449681 49080133767671020759837261)
    ·
      refine ⟨18405050162876632784938973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49080133767671020759837261 18405050162876632784938973)
      ·
        refine ⟨6901893811078737294352115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18405050162876632784938973 6901893811078737294352115)
        ·
          refine ⟨10352840716618105941528173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901893811078737294352115 10352840716618105941528173)
          ·
            refine ⟨3882315268731789728073065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10352840716618105941528173 3882315268731789728073065)
            ·
              refine ⟨2911736451548842296054799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3882315268731789728073065 2911736451548842296054799)
              ·
                refine ⟨4367604677323263444082199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911736451548842296054799 4367604677323263444082199)
                ·
                  refine ⟨6551407015984895166123299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367604677323263444082199 6551407015984895166123299)
                  ·
                    refine ⟨9827110523977342749184949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6551407015984895166123299 9827110523977342749184949)
                    ·
                      refine ⟨921291611622875882736089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9827110523977342749184949 921291611622875882736089)
                      ·
                        rfl

theorem cell23_1794209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1794209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794209 prefixEnd_1794209 := by exact prefixLift 1794209
  have htrace : WordTrace (prefixWord ++ tailWord_1794209) baseStart_1794209 baseEnd_1794209 := by
    simpa [prefixWord, tailWord_1794209, baseEnd_1794209] using wordTrace_append hprefix tailTrace_1794209
  have hstable : (prefixWord ++ tailWord_1794209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794209).length < 2 ^ (prefixWord ++ tailWord_1794209).sum := by decide
  have hdescent : baseEnd_1794209 < baseStart_1794209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794266 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_1794266 : Nat := 118140960795 + 1794266 * 2 ^ 59
def prefixEnd_1794266 : Nat := 4983230072969 + 3 ^ 40 * 1794266 * 2
def baseEnd_1794266 : Nat := 921320880020182159723327

theorem tailTrace_1794266 : CollatzResearch.WordTrace tailWord_1794266 prefixEnd_1794266 921320880020182159723327 := by
  unfold tailWord_1794266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16360564329422048270318663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43628171545125462054183101 16360564329422048270318663)
  ·
    refine ⟨24540846494133072405477995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16360564329422048270318663 24540846494133072405477995)
    ·
      refine ⟨36811269741199608608216993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24540846494133072405477995 36811269741199608608216993)
      ·
        refine ⟨27608452305899706456162745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36811269741199608608216993 27608452305899706456162745)
        ·
          refine ⟨20706339229424779842122059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27608452305899706456162745 20706339229424779842122059)
          ·
            refine ⟨31059508844137169763183089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20706339229424779842122059 31059508844137169763183089)
            ·
              refine ⟨23294631633102877322387317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31059508844137169763183089 23294631633102877322387317)
              ·
                refine ⟨2183871715603394748973811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23294631633102877322387317 2183871715603394748973811)
                ·
                  refine ⟨3275807573405092123460717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183871715603394748973811 3275807573405092123460717)
                  ·
                    refine ⟨1228427840026909546297769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275807573405092123460717 1228427840026909546297769)
                    ·
                      refine ⟨921320880020182159723327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228427840026909546297769 921320880020182159723327)
                      ·
                        rfl

theorem cell23_1794266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_1794266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794266 prefixEnd_1794266 := by exact prefixLift 1794266
  have htrace : WordTrace (prefixWord ++ tailWord_1794266) baseStart_1794266 baseEnd_1794266 := by
    simpa [prefixWord, tailWord_1794266, baseEnd_1794266] using wordTrace_append hprefix tailTrace_1794266
  have hstable : (prefixWord ++ tailWord_1794266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794266).length < 2 ^ (prefixWord ++ tailWord_1794266).sum := by decide
  have hdescent : baseEnd_1794266 < baseStart_1794266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794272 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_1794272 : Nat := 118140960795 + 1794272 * 2 ^ 59
def prefixEnd_1794272 : Nat := 4983230072969 + 3 ^ 40 * 1794272 * 2
def baseEnd_1794272 : Nat := 307107986968036378749433

theorem tailTrace_1794272 : CollatzResearch.WordTrace tailWord_1794272 prefixEnd_1794272 307107986968036378749433 := by
  unfold tailWord_1794272
  simp only [CollatzResearch.WordTrace]
  refine ⟨32721238077833228052996535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43628317437110970737328713 32721238077833228052996535)
  ·
    refine ⟨49081857116749842079494803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32721238077833228052996535 49081857116749842079494803)
    ·
      refine ⟨73622785675124763119242205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49081857116749842079494803 73622785675124763119242205)
      ·
        refine ⟨27608544628171786169715827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73622785675124763119242205 27608544628171786169715827)
        ·
          refine ⟨41412816942257679254573741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27608544628171786169715827 41412816942257679254573741)
          ·
            refine ⟨15529806353346629720465153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41412816942257679254573741 15529806353346629720465153)
            ·
              refine ⟨11647354765009972290348865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15529806353346629720465153 11647354765009972290348865)
              ·
                refine ⟨8735516073757479217761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11647354765009972290348865 8735516073757479217761649)
                ·
                  refine ⟨6551637055318109413321237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735516073757479217761649 6551637055318109413321237)
                  ·
                    refine ⟨307107986968036378749433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6551637055318109413321237 307107986968036378749433)
                    ·
                      rfl

theorem cell23_1794272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_1794272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794272 prefixEnd_1794272 := by exact prefixLift 1794272
  have htrace : WordTrace (prefixWord ++ tailWord_1794272) baseStart_1794272 baseEnd_1794272 := by
    simpa [prefixWord, tailWord_1794272, baseEnd_1794272] using wordTrace_append hprefix tailTrace_1794272
  have hstable : (prefixWord ++ tailWord_1794272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794272).length < 2 ^ (prefixWord ++ tailWord_1794272).sum := by decide
  have hdescent : baseEnd_1794272 < baseStart_1794272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794279 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1794279 : Nat := 118140960795 + 1794279 * 2 ^ 59
def prefixEnd_1794279 : Nat := 4983230072969 + 3 ^ 40 * 1794279 * 2
def baseEnd_1794279 : Nat := 921327555268690608860767

theorem tailTrace_1794279 : CollatzResearch.WordTrace tailWord_1794279 prefixEnd_1794279 921327555268690608860767 := by
  unfold tailWord_1794279
  simp only [CollatzResearch.WordTrace]
  refine ⟨65442731466641096301497891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43628487644427397534331927 65442731466641096301497891)
  ·
    refine ⟨98164097199961644452246837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65442731466641096301497891 98164097199961644452246837)
    ·
      refine ⟨9202884112496404167398141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98164097199961644452246837 9202884112496404167398141)
      ·
        refine ⟨3451081542186151562774303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9202884112496404167398141 3451081542186151562774303)
        ·
          refine ⟨5176622313279227344161455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451081542186151562774303 5176622313279227344161455)
          ·
            refine ⟨7764933469918841016242183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176622313279227344161455 7764933469918841016242183)
            ·
              refine ⟨11647400204878261524363275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764933469918841016242183 11647400204878261524363275)
              ·
                refine ⟨17471100307317392286544913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11647400204878261524363275 17471100307317392286544913)
                ·
                  refine ⟨13103325230488044214908685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17471100307317392286544913 13103325230488044214908685)
                  ·
                    refine ⟨4913746961433016580590757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13103325230488044214908685 4913746961433016580590757)
                    ·
                      refine ⟨921327555268690608860767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4913746961433016580590757 921327555268690608860767)
                      ·
                        rfl

theorem cell23_1794279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1794279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794279 prefixEnd_1794279 := by exact prefixLift 1794279
  have htrace : WordTrace (prefixWord ++ tailWord_1794279) baseStart_1794279 baseEnd_1794279 := by
    simpa [prefixWord, tailWord_1794279, baseEnd_1794279] using wordTrace_append hprefix tailTrace_1794279
  have hstable : (prefixWord ++ tailWord_1794279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794279).length < 2 ^ (prefixWord ++ tailWord_1794279).sum := by decide
  have hdescent : baseEnd_1794279 < baseStart_1794279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794336 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 5]
def baseStart_1794336 : Nat := 118140960795 + 1794336 * 2 ^ 59
def prefixEnd_1794336 : Nat := 4983230072969 + 3 ^ 40 * 1794336 * 2
def baseEnd_1794336 : Nat := 102372980407332987316445

theorem tailTrace_1794336 : CollatzResearch.WordTrace tailWord_1794336 prefixEnd_1794336 102372980407332987316445 := by
  unfold tailWord_1794336
  simp only [CollatzResearch.WordTrace]
  refine ⟨32722405213717297518161431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43629873618289730024215241 32722405213717297518161431)
  ·
    refine ⟨49083607820575946277242147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32722405213717297518161431 49083607820575946277242147)
    ·
      refine ⟨73625411730863919415863221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49083607820575946277242147 73625411730863919415863221)
      ·
        refine ⟨6902382349768492445237177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73625411730863919415863221 6902382349768492445237177)
        ·
          refine ⟨5176786762326369333927883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6902382349768492445237177 5176786762326369333927883)
          ·
            refine ⟨7765180143489554000891825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176786762326369333927883 7765180143489554000891825)
            ·
              refine ⟨5823885107617165500668869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7765180143489554000891825 5823885107617165500668869)
              ·
                refine ⟨1091978457678218531375413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5823885107617165500668869 1091978457678218531375413)
                ·
                  refine ⟨102372980407332987316445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1091978457678218531375413 102372980407332987316445)
                  ·
                    rfl

theorem cell23_1794336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 5].length) (baseStart_1794336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794336 prefixEnd_1794336 := by exact prefixLift 1794336
  have htrace : WordTrace (prefixWord ++ tailWord_1794336) baseStart_1794336 baseEnd_1794336 := by
    simpa [prefixWord, tailWord_1794336, baseEnd_1794336] using wordTrace_append hprefix tailTrace_1794336
  have hstable : (prefixWord ++ tailWord_1794336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794336).length < 2 ^ (prefixWord ++ tailWord_1794336).sum := by decide
  have hdescent : baseEnd_1794336 < baseStart_1794336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794386 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_1794386 : Nat := 118140960795 + 1794386 * 2 ^ 59
def prefixEnd_1794386 : Nat := 4983230072969 + 3 ^ 40 * 1794386 * 2
def baseEnd_1794386 : Nat := 921382497698721690222775

theorem tailTrace_1794386 : CollatzResearch.WordTrace tailWord_1794386 prefixEnd_1794386 921382497698721690222775 := by
  unfold tailWord_1794386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16361658519313363393910753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43631089384835635717095341 16361658519313363393910753)
  ·
    refine ⟨12271243889485022545433065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16361658519313363393910753 12271243889485022545433065)
    ·
      refine ⟨9203432917113766909074799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12271243889485022545433065 9203432917113766909074799)
      ·
        refine ⟨13805149375670650363612199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9203432917113766909074799 13805149375670650363612199)
        ·
          refine ⟨20707724063505975545418299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13805149375670650363612199 20707724063505975545418299)
          ·
            refine ⟨31061586095258963318127449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20707724063505975545418299 31061586095258963318127449)
            ·
              refine ⟨23296189571444222488595587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31061586095258963318127449 23296189571444222488595587)
              ·
                refine ⟨34944284357166333732893381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23296189571444222488595587 34944284357166333732893381)
                ·
                  refine ⟨6552053316968687574917509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34944284357166333732893381 6552053316968687574917509)
                  ·
                    refine ⟨1228509996931628920297033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552053316968687574917509 1228509996931628920297033)
                    ·
                      refine ⟨921382497698721690222775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228509996931628920297033 921382497698721690222775)
                      ·
                        rfl

theorem cell23_1794386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_1794386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794386 prefixEnd_1794386 := by exact prefixLift 1794386
  have htrace : WordTrace (prefixWord ++ tailWord_1794386) baseStart_1794386 baseEnd_1794386 := by
    simpa [prefixWord, tailWord_1794386, baseEnd_1794386] using wordTrace_append hprefix tailTrace_1794386
  have hstable : (prefixWord ++ tailWord_1794386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794386).length < 2 ^ (prefixWord ++ tailWord_1794386).sum := by decide
  have hdescent : baseEnd_1794386 < baseStart_1794386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794409 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 6]
def baseStart_1794409 : Nat := 118140960795 + 1794409 * 2 ^ 59
def prefixEnd_1794409 : Nat := 4983230072969 + 3 ^ 40 * 1794409 * 2
def baseEnd_1794409 : Nat := 102377145305975011137241

theorem tailTrace_1794409 : CollatzResearch.WordTrace tailWord_1794409 prefixEnd_1794409 102377145305975011137241 := by
  unfold tailWord_1794409
  simp only [CollatzResearch.WordTrace]
  refine ⟨65447472956170128503730281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43631648637446752335820187 65447472956170128503730281)
  ·
    refine ⟨49085604717127596377797711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65447472956170128503730281 49085604717127596377797711)
    ·
      refine ⟨73628407075691394566696567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49085604717127596377797711 73628407075691394566696567)
      ·
        refine ⟨110442610613537091850044851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73628407075691394566696567 110442610613537091850044851)
        ·
          refine ⟨165663915920305637775067277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110442610613537091850044851 165663915920305637775067277)
          ·
            refine ⟨62123968470114614165650229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165663915920305637775067277 62123968470114614165650229)
            ·
              refine ⟨5824122044073245078029709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62123968470114614165650229 5824122044073245078029709)
              ·
                refine ⟨2184045766527466904261141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5824122044073245078029709 2184045766527466904261141)
                ·
                  refine ⟨102377145305975011137241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2184045766527466904261141 102377145305975011137241)
                  ·
                    rfl

theorem cell23_1794409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_1794409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794409 prefixEnd_1794409 := by exact prefixLift 1794409
  have htrace : WordTrace (prefixWord ++ tailWord_1794409) baseStart_1794409 baseEnd_1794409 := by
    simpa [prefixWord, tailWord_1794409, baseEnd_1794409] using wordTrace_append hprefix tailTrace_1794409
  have hstable : (prefixWord ++ tailWord_1794409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794409).length < 2 ^ (prefixWord ++ tailWord_1794409).sum := by decide
  have hdescent : baseEnd_1794409 < baseStart_1794409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794454 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1794454 : Nat := 118140960795 + 1794454 * 2 ^ 59
def prefixEnd_1794454 : Nat := 4983230072969 + 3 ^ 40 * 1794454 * 2
def baseEnd_1794454 : Nat := 921417414383227424172463

theorem tailTrace_1794454 : CollatzResearch.WordTrace tailWord_1794454 prefixEnd_1794454 921417414383227424172463 := by
  unfold tailWord_1794454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090569640062943824319901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43632742827338067459412277 4090569640062943824319901)
  ·
    refine ⟨1533963615023603934119963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4090569640062943824319901 1533963615023603934119963)
    ·
      refine ⟨2300945422535405901179945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533963615023603934119963 2300945422535405901179945)
      ·
        refine ⟨1725709066901554425884959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2300945422535405901179945 1725709066901554425884959)
        ·
          refine ⟨2588563600352331638827439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725709066901554425884959 2588563600352331638827439)
          ·
            refine ⟨3882845400528497458241159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588563600352331638827439 3882845400528497458241159)
            ·
              refine ⟨5824268100792746187361739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882845400528497458241159 5824268100792746187361739)
              ·
                refine ⟨8736402151189119281042609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824268100792746187361739 8736402151189119281042609)
                ·
                  refine ⟨6552301613391839460781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8736402151189119281042609 6552301613391839460781957)
                  ·
                    refine ⟨1228556552510969898896617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552301613391839460781957 1228556552510969898896617)
                    ·
                      refine ⟨921417414383227424172463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228556552510969898896617 921417414383227424172463)
                      ·
                        rfl

theorem cell23_1794454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1794454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794454 prefixEnd_1794454 := by exact prefixLift 1794454
  have htrace : WordTrace (prefixWord ++ tailWord_1794454) baseStart_1794454 baseEnd_1794454 := by
    simpa [prefixWord, tailWord_1794454, baseEnd_1794454] using wordTrace_append hprefix tailTrace_1794454
  have hstable : (prefixWord ++ tailWord_1794454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794454).length < 2 ^ (prefixWord ++ tailWord_1794454).sum := by decide
  have hdescent : baseEnd_1794454 < baseStart_1794454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794456 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1794456 : Nat := 118140960795 + 1794456 * 2 ^ 59
def prefixEnd_1794456 : Nat := 4983230072969 + 3 ^ 40 * 1794456 * 2
def baseEnd_1794456 : Nat := 307139480448178805449151

theorem tailTrace_1794456 : CollatzResearch.WordTrace tailWord_1794456 prefixEnd_1794456 307139480448178805449151 := by
  unfold tailWord_1794456
  simp only [CollatzResearch.WordTrace]
  refine ⟨32724593593499927765345611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43632791457999903687127481 32724593593499927765345611)
  ·
    refine ⟨49086890390249891648018417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32724593593499927765345611 49086890390249891648018417)
    ·
      refine ⟨36815167792687418736013813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49086890390249891648018417 36815167792687418736013813)
      ·
        refine ⟨3451421980564445506501295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36815167792687418736013813 3451421980564445506501295)
        ·
          refine ⟨5177132970846668259751943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451421980564445506501295 5177132970846668259751943)
          ·
            refine ⟨7765699456270002389627915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177132970846668259751943 7765699456270002389627915)
            ·
              refine ⟨11648549184405003584441873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765699456270002389627915 11648549184405003584441873)
              ·
                refine ⟨8736411888303752688331405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11648549184405003584441873 8736411888303752688331405)
                ·
                  refine ⟨3276154458113907258124277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8736411888303752688331405 3276154458113907258124277)
                  ·
                    refine ⟨307139480448178805449151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3276154458113907258124277 307139480448178805449151)
                    ·
                      rfl

theorem cell23_1794456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1794456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794456 prefixEnd_1794456 := by exact prefixLift 1794456
  have htrace : WordTrace (prefixWord ++ tailWord_1794456) baseStart_1794456 baseEnd_1794456 := by
    simpa [prefixWord, tailWord_1794456, baseEnd_1794456] using wordTrace_append hprefix tailTrace_1794456
  have hstable : (prefixWord ++ tailWord_1794456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794456).length < 2 ^ (prefixWord ++ tailWord_1794456).sum := by decide
  have hdescent : baseEnd_1794456 < baseStart_1794456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794474 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1794474 : Nat := 118140960795 + 1794474 * 2 ^ 59
def prefixEnd_1794474 : Nat := 4983230072969 + 3 ^ 40 * 1794474 * 2
def baseEnd_1794474 : Nat := 921427683996317345922371

theorem tailTrace_1794474 : CollatzResearch.WordTrace tailWord_1794474 prefixEnd_1794474 921427683996317345922371 := by
  unfold tailWord_1794474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16362460925233661151211619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43633229133956429736564317 16362460925233661151211619)
  ·
    refine ⟨24543691387850491726817429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16362460925233661151211619 24543691387850491726817429)
    ·
      refine ⟨1150485533805491799694567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24543691387850491726817429 1150485533805491799694567)
      ·
        refine ⟨1725728300708237699541851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150485533805491799694567 1725728300708237699541851)
        ·
          refine ⟨2588592451062356549312777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725728300708237699541851 2588592451062356549312777)
          ·
            refine ⟨1941444338296767411984583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2588592451062356549312777 1941444338296767411984583)
            ·
              refine ⟨2912166507445151117976875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941444338296767411984583 2912166507445151117976875)
              ·
                refine ⟨4368249761167726676965313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912166507445151117976875 4368249761167726676965313)
                ·
                  refine ⟨3276187320875795007723985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368249761167726676965313 3276187320875795007723985)
                  ·
                    refine ⟨2457140490656846255792989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3276187320875795007723985 2457140490656846255792989)
                    ·
                      refine ⟨921427683996317345922371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2457140490656846255792989 921427683996317345922371)
                      ·
                        rfl

theorem cell23_1794474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1794474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794474 prefixEnd_1794474 := by exact prefixLift 1794474
  have htrace : WordTrace (prefixWord ++ tailWord_1794474) baseStart_1794474 baseEnd_1794474 := by
    simpa [prefixWord, tailWord_1794474, baseEnd_1794474] using wordTrace_append hprefix tailTrace_1794474
  have hstable : (prefixWord ++ tailWord_1794474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794474).length < 2 ^ (prefixWord ++ tailWord_1794474).sum := by decide
  have hdescent : baseEnd_1794474 < baseStart_1794474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794476 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_1794476 : Nat := 118140960795 + 1794476 * 2 ^ 59
def prefixEnd_1794476 : Nat := 4983230072969 + 3 ^ 40 * 1794476 * 2
def baseEnd_1794476 : Nat := 921428710957626338097361

theorem tailTrace_1794476 : CollatzResearch.WordTrace tailWord_1794476 prefixEnd_1794476 921428710957626338097361 := by
  unfold tailWord_1794476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32724958323463699473209641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43633277764618265964279521 32724958323463699473209641)
  ·
    refine ⟨24543718742597774604907231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32724958323463699473209641 24543718742597774604907231)
    ·
      refine ⟨36815578113896661907360847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24543718742597774604907231 36815578113896661907360847)
      ·
        refine ⟨55223367170844992861041271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36815578113896661907360847 55223367170844992861041271)
        ·
          refine ⟨82835050756267489291561907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55223367170844992861041271 82835050756267489291561907)
          ·
            refine ⟨124252576134401233937342861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82835050756267489291561907 124252576134401233937342861)
            ·
              refine ⟨46594716050400462726503573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124252576134401233937342861 46594716050400462726503573)
              ·
                refine ⟨2184127314862521690304855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46594716050400462726503573 2184127314862521690304855)
                ·
                  refine ⟨3276190972293782535457283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184127314862521690304855 3276190972293782535457283)
                  ·
                    refine ⟨4914286458440673803185925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276190972293782535457283 4914286458440673803185925)
                    ·
                      refine ⟨921428710957626338097361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4914286458440673803185925 921428710957626338097361)
                      ·
                        rfl

theorem cell23_1794476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_1794476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794476 prefixEnd_1794476 := by exact prefixLift 1794476
  have htrace : WordTrace (prefixWord ++ tailWord_1794476) baseStart_1794476 baseEnd_1794476 := by
    simpa [prefixWord, tailWord_1794476, baseEnd_1794476] using wordTrace_append hprefix tailTrace_1794476
  have hstable : (prefixWord ++ tailWord_1794476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794476).length < 2 ^ (prefixWord ++ tailWord_1794476).sum := by decide
  have hdescent : baseEnd_1794476 < baseStart_1794476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794493 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1794493 : Nat := 118140960795 + 1794493 * 2 ^ 59
def prefixEnd_1794493 : Nat := 4983230072969 + 3 ^ 40 * 1794493 * 2
def baseEnd_1794493 : Nat := 921437440128752771584783

theorem tailTrace_1794493 : CollatzResearch.WordTrace tailWord_1794493 prefixEnd_1794493 921437440128752771584783 := by
  unfold tailWord_1794493
  simp only [CollatzResearch.WordTrace]
  refine ⟨65450536687865810849788133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43633691125243873899858755 65450536687865810849788133)
  ·
    refine ⟨12271975628974839534335275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65450536687865810849788133 12271975628974839534335275)
    ·
      refine ⟨18407963443462259301502913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12271975628974839534335275 18407963443462259301502913)
      ·
        refine ⟨13805972582596694476127185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18407963443462259301502913 13805972582596694476127185)
        ·
          refine ⟨10354479436947520857095389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13805972582596694476127185 10354479436947520857095389)
          ·
            refine ⟨3882929788855320321410771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10354479436947520857095389 3882929788855320321410771)
            ·
              refine ⟨5824394683282980482116157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882929788855320321410771 5824394683282980482116157)
              ·
                refine ⟨2184148006231117680793559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5824394683282980482116157 2184148006231117680793559)
                ·
                  refine ⟨3276222009346676521190339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184148006231117680793559 3276222009346676521190339)
                  ·
                    refine ⟨4914333014020014781785509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3276222009346676521190339 4914333014020014781785509)
                    ·
                      refine ⟨921437440128752771584783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4914333014020014781785509 921437440128752771584783)
                      ·
                        rfl

theorem cell23_1794493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1794493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794493 prefixEnd_1794493 := by exact prefixLift 1794493
  have htrace : WordTrace (prefixWord ++ tailWord_1794493) baseStart_1794493 baseEnd_1794493 := by
    simpa [prefixWord, tailWord_1794493, baseEnd_1794493] using wordTrace_append hprefix tailTrace_1794493
  have hstable : (prefixWord ++ tailWord_1794493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794493).length < 2 ^ (prefixWord ++ tailWord_1794493).sum := by decide
  have hdescent : baseEnd_1794493 < baseStart_1794493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794503 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1794503 : Nat := 118140960795 + 1794503 * 2 ^ 59
def prefixEnd_1794503 : Nat := 4983230072969 + 3 ^ 40 * 1794503 * 2
def baseEnd_1794503 : Nat := 307147524978432577486579

theorem tailTrace_1794503 : CollatzResearch.WordTrace tailWord_1794503 prefixEnd_1794503 307147524978432577486579 := by
  unfold tailWord_1794503
  simp only [CollatzResearch.WordTrace]
  refine ⟨65450901417829582557652163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43633934278553055038434775 65450901417829582557652163)
  ·
    refine ⟨98176352126744373836478245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65450901417829582557652163 98176352126744373836478245)
    ·
      refine ⟨18408066023764570094339671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98176352126744373836478245 18408066023764570094339671)
      ·
        refine ⟨27612099035646855141509507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18408066023764570094339671 27612099035646855141509507)
        ·
          refine ⟨41418148553470282712264261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27612099035646855141509507 41418148553470282712264261)
          ·
            refine ⟨7765902853775678008549549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41418148553470282712264261 7765902853775678008549549)
            ·
              refine ⟨2912213570165879253206081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7765902853775678008549549 2912213570165879253206081)
              ·
                refine ⟨2184160177624409439904561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912213570165879253206081 2184160177624409439904561)
                ·
                  refine ⟨1638120133218307079928421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2184160177624409439904561 1638120133218307079928421)
                  ·
                    refine ⟨307147524978432577486579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638120133218307079928421 307147524978432577486579)
                    ·
                      rfl

theorem cell23_1794503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1794503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794503 prefixEnd_1794503 := by exact prefixLift 1794503
  have htrace : WordTrace (prefixWord ++ tailWord_1794503) baseStart_1794503 baseEnd_1794503 := by
    simpa [prefixWord, tailWord_1794503, baseEnd_1794503] using wordTrace_append hprefix tailTrace_1794503
  have hstable : (prefixWord ++ tailWord_1794503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794503).length < 2 ^ (prefixWord ++ tailWord_1794503).sum := by decide
  have hdescent : baseEnd_1794503 < baseStart_1794503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794539 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_1794539 : Nat := 118140960795 + 1794539 * 2 ^ 59
def prefixEnd_1794539 : Nat := 4983230072969 + 3 ^ 40 * 1794539 * 2
def baseEnd_1794539 : Nat := 921461060238859591609571

theorem tailTrace_1794539 : CollatzResearch.WordTrace tailWord_1794539 prefixEnd_1794539 921461060238859591609571 := by
  unfold tailWord_1794539
  simp only [CollatzResearch.WordTrace]
  refine ⟨65452214445699160705962671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43634809630466107137308447 65452214445699160705962671)
  ·
    refine ⟨98178321668548741058944007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65452214445699160705962671 98178321668548741058944007)
    ·
      refine ⟨147267482502823111588416011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98178321668548741058944007 147267482502823111588416011)
      ·
        refine ⟨220901223754234667382624017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147267482502823111588416011 220901223754234667382624017)
        ·
          refine ⟨165675917815676000536968013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220901223754234667382624017 165675917815676000536968013)
          ·
            refine ⟨62128469180878500201363005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165675917815676000536968013 62128469180878500201363005)
            ·
              refine ⟨23298175942829437575511127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62128469180878500201363005 23298175942829437575511127)
              ·
                refine ⟨34947263914244156363266691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23298175942829437575511127 34947263914244156363266691)
                ·
                  refine ⟨52420895871366234544900037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34947263914244156363266691 52420895871366234544900037)
                  ·
                    refine ⟨9828917975881168977168757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52420895871366234544900037 9828917975881168977168757)
                    ·
                      refine ⟨921461060238859591609571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9828917975881168977168757 921461060238859591609571)
                      ·
                        rfl

theorem cell23_1794539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_1794539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794539 prefixEnd_1794539 := by exact prefixLift 1794539
  have htrace : WordTrace (prefixWord ++ tailWord_1794539) baseStart_1794539 baseEnd_1794539 := by
    simpa [prefixWord, tailWord_1794539, baseEnd_1794539] using wordTrace_append hprefix tailTrace_1794539
  have hstable : (prefixWord ++ tailWord_1794539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794539).length < 2 ^ (prefixWord ++ tailWord_1794539).sum := by decide
  have hdescent : baseEnd_1794539 < baseStart_1794539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794586 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1794586 : Nat := 118140960795 + 1794586 * 2 ^ 59
def prefixEnd_1794586 : Nat := 4983230072969 + 3 ^ 40 * 1794586 * 2
def baseEnd_1794586 : Nat := 921485193829620907721855

theorem tailTrace_1794586 : CollatzResearch.WordTrace tailWord_1794586 prefixEnd_1794586 921485193829620907721855 := by
  unfold tailWord_1794586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363482169132221933230903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43635952451019258488615741 16363482169132221933230903)
  ·
    refine ⟨24545223253698332899846355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16363482169132221933230903 24545223253698332899846355)
    ·
      refine ⟨36817834880547499349769533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24545223253698332899846355 36817834880547499349769533)
      ·
        refine ⟨13806688080205312256163575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36817834880547499349769533 13806688080205312256163575)
        ·
          refine ⟨20710032120307968384245363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13806688080205312256163575 20710032120307968384245363)
          ·
            refine ⟨31065048180461952576368045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20710032120307968384245363 31065048180461952576368045)
            ·
              refine ⟨11649393067673232216138017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31065048180461952576368045 11649393067673232216138017)
              ·
                refine ⟨8737044800754924162103513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11649393067673232216138017 8737044800754924162103513)
                ·
                  refine ⟨6552783600566193121577635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8737044800754924162103513 6552783600566193121577635)
                  ·
                    refine ⟨9829175400849289682366453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552783600566193121577635 9829175400849289682366453)
                    ·
                      refine ⟨921485193829620907721855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9829175400849289682366453 921485193829620907721855)
                      ·
                        rfl

theorem cell23_1794586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1794586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794586 prefixEnd_1794586 := by exact prefixLift 1794586
  have htrace : WordTrace (prefixWord ++ tailWord_1794586) baseStart_1794586 baseEnd_1794586 := by
    simpa [prefixWord, tailWord_1794586, baseEnd_1794586] using wordTrace_append hprefix tailTrace_1794586
  have hstable : (prefixWord ++ tailWord_1794586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794586).length < 2 ^ (prefixWord ++ tailWord_1794586).sum := by decide
  have hdescent : baseEnd_1794586 < baseStart_1794586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794600 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1794600 : Nat := 118140960795 + 1794600 * 2 ^ 59
def prefixEnd_1794600 : Nat := 4983230072969 + 3 ^ 40 * 1794600 * 2
def baseEnd_1794600 : Nat := 921492382558783852946791

theorem tailTrace_1794600 : CollatzResearch.WordTrace tailWord_1794600 prefixEnd_1794600 921492382558783852946791 := by
  unfold tailWord_1794600
  simp only [CollatzResearch.WordTrace]
  refine ⟨32727219649239084061966627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43636292865652112082622169 32727219649239084061966627)
  ·
    refine ⟨49090829473858626092949941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32727219649239084061966627 49090829473858626092949941)
    ·
      refine ⟨4602265263174246196214057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49090829473858626092949941 4602265263174246196214057)
      ·
        refine ⟨3451698947380684647160543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4602265263174246196214057 3451698947380684647160543)
        ·
          refine ⟨5177548421071026970740815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451698947380684647160543 5177548421071026970740815)
          ·
            refine ⟨7766322631606540456111223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177548421071026970740815 7766322631606540456111223)
            ·
              refine ⟨11649483947409810684166835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766322631606540456111223 11649483947409810684166835)
              ·
                refine ⟨17474225921114716026250253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649483947409810684166835 17474225921114716026250253)
                ·
                  refine ⟨6552834720418018509843845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17474225921114716026250253 6552834720418018509843845)
                  ·
                    refine ⟨1228656510078378470595721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552834720418018509843845 1228656510078378470595721)
                    ·
                      refine ⟨921492382558783852946791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228656510078378470595721 921492382558783852946791)
                      ·
                        rfl

theorem cell23_1794600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1794600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794600 prefixEnd_1794600 := by exact prefixLift 1794600
  have htrace : WordTrace (prefixWord ++ tailWord_1794600) baseStart_1794600 baseEnd_1794600 := by
    simpa [prefixWord, tailWord_1794600, baseEnd_1794600] using wordTrace_append hprefix tailTrace_1794600
  have hstable : (prefixWord ++ tailWord_1794600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794600).length < 2 ^ (prefixWord ++ tailWord_1794600).sum := by decide
  have hdescent : baseEnd_1794600 < baseStart_1794600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794617 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1794617 : Nat := 118140960795 + 1794617 * 2 ^ 59
def prefixEnd_1794617 : Nat := 4983230072969 + 3 ^ 40 * 1794617 * 2
def baseEnd_1794617 : Nat := 921501111729910286434213

theorem tailTrace_1794617 : CollatzResearch.WordTrace tailWord_1794617 prefixEnd_1794617 921501111729910286434213 := by
  unfold tailWord_1794617
  simp only [CollatzResearch.WordTrace]
  refine ⟨65455059339416580027302105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43636706226277720018201403 65455059339416580027302105)
  ·
    refine ⟨49091294504562435020476579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65455059339416580027302105 49091294504562435020476579)
    ·
      refine ⟨73636941756843652530714869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49091294504562435020476579 73636941756843652530714869)
      ·
        refine ⟨6903463289704092424754519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73636941756843652530714869 6903463289704092424754519)
        ·
          refine ⟨10355194934556138637131779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903463289704092424754519 10355194934556138637131779)
          ·
            refine ⟨15532792401834207955697669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355194934556138637131779 15532792401834207955697669)
            ·
              refine ⟨2912398575343913991693313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15532792401834207955697669 2912398575343913991693313)
              ·
                refine ⟨2184298931507935493769985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912398575343913991693313 2184298931507935493769985)
                ·
                  refine ⟨1638224198630951620327489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2184298931507935493769985 1638224198630951620327489)
                  ·
                    refine ⟨1228668148973213715245617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638224198630951620327489 1228668148973213715245617)
                    ·
                      refine ⟨921501111729910286434213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228668148973213715245617 921501111729910286434213)
                      ·
                        rfl

theorem cell23_1794617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1794617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794617 prefixEnd_1794617 := by exact prefixLift 1794617
  have htrace : WordTrace (prefixWord ++ tailWord_1794617) baseStart_1794617 baseEnd_1794617 := by
    simpa [prefixWord, tailWord_1794617, baseEnd_1794617] using wordTrace_append hprefix tailTrace_1794617
  have hstable : (prefixWord ++ tailWord_1794617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794617).length < 2 ^ (prefixWord ++ tailWord_1794617).sum := by decide
  have hdescent : baseEnd_1794617 < baseStart_1794617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794623 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 5]
def baseStart_1794623 : Nat := 118140960795 + 1794623 * 2 ^ 59
def prefixEnd_1794623 : Nat := 4983230072969 + 3 ^ 40 * 1794623 * 2
def baseEnd_1794623 : Nat := 102389354734870806995465

theorem tailTrace_1794623 : CollatzResearch.WordTrace tailWord_1794623 prefixEnd_1794623 102389354734870806995465 := by
  unfold tailWord_1794623
  simp only [CollatzResearch.WordTrace]
  refine ⟨65455278177394843052020523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43636852118263228701347015 65455278177394843052020523)
  ·
    refine ⟨98182917266092264578030785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65455278177394843052020523 98182917266092264578030785)
    ·
      refine ⟨73637187949569198433523089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98182917266092264578030785 73637187949569198433523089)
      ·
        refine ⟨55227890962176898825142317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73637187949569198433523089 55227890962176898825142317)
        ·
          refine ⟨20710459110816337059428369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55227890962176898825142317 20710459110816337059428369)
          ·
            refine ⟨15532844333112252794571277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20710459110816337059428369 15532844333112252794571277)
            ·
              refine ⟨5824816624917094797964229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15532844333112252794571277 5824816624917094797964229)
              ·
                refine ⟨1092153117171955274618293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5824816624917094797964229 1092153117171955274618293)
                ·
                  refine ⟨102389354734870806995465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092153117171955274618293 102389354734870806995465)
                  ·
                    rfl

theorem cell23_1794623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 5].length) (baseStart_1794623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794623 prefixEnd_1794623 := by exact prefixLift 1794623
  have htrace : WordTrace (prefixWord ++ tailWord_1794623) baseStart_1794623 baseEnd_1794623 := by
    simpa [prefixWord, tailWord_1794623, baseEnd_1794623] using wordTrace_append hprefix tailTrace_1794623
  have hstable : (prefixWord ++ tailWord_1794623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794623).length < 2 ^ (prefixWord ++ tailWord_1794623).sum := by decide
  have hdescent : baseEnd_1794623 < baseStart_1794623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794630 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1794630 : Nat := 118140960795 + 1794630 * 2 ^ 59
def prefixEnd_1794630 : Nat := 4983230072969 + 3 ^ 40 * 1794630 * 2
def baseEnd_1794630 : Nat := 921507786978418735571653

theorem tailTrace_1794630 : CollatzResearch.WordTrace tailWord_1794630 prefixEnd_1794630 921507786978418735571653 := by
  unfold tailWord_1794630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045485421511546351485167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43637022325579655498350229 2045485421511546351485167)
  ·
    refine ⟨3068228132267319527227751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045485421511546351485167 3068228132267319527227751)
    ·
      refine ⟨4602342198400979290841627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068228132267319527227751 4602342198400979290841627)
      ·
        refine ⟨6903513297601468936262441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602342198400979290841627 6903513297601468936262441)
        ·
          refine ⟨5177634973201101702196831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903513297601468936262441 5177634973201101702196831)
          ·
            refine ⟨7766452459801652553295247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177634973201101702196831 7766452459801652553295247)
            ·
              refine ⟨11649678689702478829942871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766452459801652553295247 11649678689702478829942871)
              ·
                refine ⟨17474518034553718244914307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649678689702478829942871 17474518034553718244914307)
                ·
                  refine ⟨26211777051830577367371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17474518034553718244914307 26211777051830577367371461)
                  ·
                    refine ⟨4914708197218233256382149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26211777051830577367371461 4914708197218233256382149)
                    ·
                      refine ⟨921507786978418735571653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4914708197218233256382149 921507786978418735571653)
                      ·
                        rfl

theorem cell23_1794630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1794630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794630 prefixEnd_1794630 := by exact prefixLift 1794630
  have htrace : WordTrace (prefixWord ++ tailWord_1794630) baseStart_1794630 baseEnd_1794630 := by
    simpa [prefixWord, tailWord_1794630, baseEnd_1794630] using wordTrace_append hprefix tailTrace_1794630
  have hstable : (prefixWord ++ tailWord_1794630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794630).length < 2 ^ (prefixWord ++ tailWord_1794630).sum := by decide
  have hdescent : baseEnd_1794630 < baseStart_1794630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794636 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_1794636 : Nat := 118140960795 + 1794636 * 2 ^ 59
def prefixEnd_1794636 : Nat := 4983230072969 + 3 ^ 40 * 1794636 * 2
def baseEnd_1794636 : Nat := 307170289287448570698875

theorem tailTrace_1794636 : CollatzResearch.WordTrace tailWord_1794636 prefixEnd_1794636 307170289287448570698875 := by
  unfold tailWord_1794636
  simp only [CollatzResearch.WordTrace]
  refine ⟨32727876163173873136121881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43637168217565164181495841 32727876163173873136121881)
  ·
    refine ⟨24545907122380404852091411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32727876163173873136121881 24545907122380404852091411)
    ·
      refine ⟨36818860683570607278137117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24545907122380404852091411 36818860683570607278137117)
      ·
        refine ⟨13807072756338977729301419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36818860683570607278137117 13807072756338977729301419)
        ·
          refine ⟨20710609134508466593952129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807072756338977729301419 20710609134508466593952129)
          ·
            refine ⟨15532956850881349945464097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20710609134508466593952129 15532956850881349945464097)
            ·
              refine ⟨11649717638161012459098073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15532956850881349945464097 11649717638161012459098073)
              ·
                refine ⟨8737288228620759344323555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11649717638161012459098073 8737288228620759344323555)
                ·
                  refine ⟨13105932342931139016485333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737288228620759344323555 13105932342931139016485333)
                  ·
                    refine ⟨307170289287448570698875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13105932342931139016485333 307170289287448570698875)
                    ·
                      rfl

theorem cell23_1794636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_1794636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794636 prefixEnd_1794636 := by exact prefixLift 1794636
  have htrace : WordTrace (prefixWord ++ tailWord_1794636) baseStart_1794636 baseEnd_1794636 := by
    simpa [prefixWord, tailWord_1794636, baseEnd_1794636] using wordTrace_append hprefix tailTrace_1794636
  have hstable : (prefixWord ++ tailWord_1794636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794636).length < 2 ^ (prefixWord ++ tailWord_1794636).sum := by decide
  have hdescent : baseEnd_1794636 < baseStart_1794636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794693 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_1794693 : Nat := 118140960795 + 1794693 * 2 ^ 59
def prefixEnd_1794693 : Nat := 4983230072969 + 3 ^ 40 * 1794693 * 2
def baseEnd_1794693 : Nat := 921540136259651989083863

theorem tailTrace_1794693 : CollatzResearch.WordTrace tailWord_1794693 prefixEnd_1794693 921540136259651989083863 := by
  unfold tailWord_1794693
  simp only [CollatzResearch.WordTrace]
  refine ⟨65457831287141245007068733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43638554191427496671379155 65457831287141245007068733)
  ·
    refine ⟨24546686732677966877650775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65457831287141245007068733 24546686732677966877650775)
    ·
      refine ⟨36820030099016950316476163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24546686732677966877650775 36820030099016950316476163)
      ·
        refine ⟨55230045148525425474714245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36820030099016950316476163 55230045148525425474714245)
        ·
          refine ⟨10355633465348517276508921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55230045148525425474714245 10355633465348517276508921)
          ·
            refine ⟨7766725099011387957381691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10355633465348517276508921 7766725099011387957381691)
            ·
              refine ⟨11650087648517081936072537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766725099011387957381691 11650087648517081936072537)
              ·
                refine ⟨8737565736387811452054403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11650087648517081936072537 8737565736387811452054403)
                ·
                  refine ⟨13106348604581717178081605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737565736387811452054403 13106348604581717178081605)
                  ·
                    refine ⟨2457440363359071970890301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13106348604581717178081605 2457440363359071970890301)
                    ·
                      refine ⟨921540136259651989083863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2457440363359071970890301 921540136259651989083863)
                      ·
                        rfl

theorem cell23_1794693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_1794693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794693 prefixEnd_1794693 := by exact prefixLift 1794693
  have htrace : WordTrace (prefixWord ++ tailWord_1794693) baseStart_1794693 baseEnd_1794693 := by
    simpa [prefixWord, tailWord_1794693, baseEnd_1794693] using wordTrace_append hprefix tailTrace_1794693
  have hstable : (prefixWord ++ tailWord_1794693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794693).length < 2 ^ (prefixWord ++ tailWord_1794693).sum := by decide
  have hdescent : baseEnd_1794693 < baseStart_1794693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794717 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1794717 : Nat := 118140960795 + 1794717 * 2 ^ 59
def prefixEnd_1794717 : Nat := 4983230072969 + 3 ^ 40 * 1794717 * 2
def baseEnd_1794717 : Nat := 307184153265119965061251

theorem tailTrace_1794717 : CollatzResearch.WordTrace tailWord_1794717 prefixEnd_1794717 307184153265119965061251 := by
  unfold tailWord_1794717
  simp only [CollatzResearch.WordTrace]
  refine ⟨65458706639054297105942405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43639137759369531403961603 65458706639054297105942405)
  ·
    refine ⟨12273507494822680707364201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65458706639054297105942405 12273507494822680707364201)
    ·
      refine ⟨9205130621117010530523151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12273507494822680707364201 9205130621117010530523151)
      ·
        refine ⟨13807695931675515795784727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205130621117010530523151 13807695931675515795784727)
        ·
          refine ⟨20711543897513273693677091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807695931675515795784727 20711543897513273693677091)
          ·
            refine ⟨31067315846269910540515637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20711543897513273693677091 31067315846269910540515637)
            ·
              refine ⟨2912560860587804113173341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31067315846269910540515637 2912560860587804113173341)
              ·
                refine ⟨1092210322720426542440003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2912560860587804113173341 1092210322720426542440003)
                ·
                  refine ⟨1638315484080639813660005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092210322720426542440003 1638315484080639813660005)
                  ·
                    refine ⟨307184153265119965061251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638315484080639813660005 307184153265119965061251)
                    ·
                      rfl

theorem cell23_1794717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1794717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794717 prefixEnd_1794717 := by exact prefixLift 1794717
  have htrace : WordTrace (prefixWord ++ tailWord_1794717) baseStart_1794717 baseEnd_1794717 := by
    simpa [prefixWord, tailWord_1794717, baseEnd_1794717] using wordTrace_append hprefix tailTrace_1794717
  have hstable : (prefixWord ++ tailWord_1794717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794717).length < 2 ^ (prefixWord ++ tailWord_1794717).sum := by decide
  have hdescent : baseEnd_1794717 < baseStart_1794717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794734 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1794734 : Nat := 118140960795 + 1794734 * 2 ^ 59
def prefixEnd_1794734 : Nat := 4983230072969 + 3 ^ 40 * 1794734 * 2
def baseEnd_1794734 : Nat := 307187062988828776223725

theorem tailTrace_1794734 : CollatzResearch.WordTrace tailWord_1794734 prefixEnd_1794734 307187062988828776223725 := by
  unfold tailWord_1794734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182415834999088626163907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43639551119995139339540837 8182415834999088626163907)
  ·
    refine ⟨12273623752498632939245861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8182415834999088626163907 12273623752498632939245861)
    ·
      refine ⟨2301304453593493676108599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12273623752498632939245861 2301304453593493676108599)
      ·
        refine ⟨3451956680390240514162899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301304453593493676108599 3451956680390240514162899)
        ·
          refine ⟨5177935020585360771244349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451956680390240514162899 5177935020585360771244349)
          ·
            refine ⟨1941725632719510289216631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5177935020585360771244349 1941725632719510289216631)
            ·
              refine ⟨2912588449079265433824947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941725632719510289216631 2912588449079265433824947)
              ·
                refine ⟨4368882673618898150737421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912588449079265433824947 4368882673618898150737421)
                ·
                  refine ⟨1638331002607086806526533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4368882673618898150737421 1638331002607086806526533)
                  ·
                    refine ⟨307187062988828776223725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638331002607086806526533 307187062988828776223725)
                    ·
                      rfl

theorem cell23_1794734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1794734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794734 prefixEnd_1794734 := by exact prefixLift 1794734
  have htrace : WordTrace (prefixWord ++ tailWord_1794734) baseStart_1794734 baseEnd_1794734 := by
    simpa [prefixWord, tailWord_1794734, baseEnd_1794734] using wordTrace_append hprefix tailTrace_1794734
  have hstable : (prefixWord ++ tailWord_1794734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794734).length < 2 ^ (prefixWord ++ tailWord_1794734).sum := by decide
  have hdescent : baseEnd_1794734 < baseStart_1794734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794736 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1794736 : Nat := 118140960795 + 1794736 * 2 ^ 59
def prefixEnd_1794736 : Nat := 4983230072969 + 3 ^ 40 * 1794736 * 2
def baseEnd_1794736 : Nat := 921562215927795320846165

theorem tailTrace_1794736 : CollatzResearch.WordTrace tailWord_1794736 prefixEnd_1794736 921562215927795320846165 := by
  unfold tailWord_1794736
  simp only [CollatzResearch.WordTrace]
  refine ⟨32729699812992731675442031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43639599750656975567256041 32729699812992731675442031)
  ·
    refine ⟨49094549719489097513163047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32729699812992731675442031 49094549719489097513163047)
    ·
      refine ⟨73641824579233646269744571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49094549719489097513163047 73641824579233646269744571)
      ·
        refine ⟨110462736868850469404616857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73641824579233646269744571 110462736868850469404616857)
        ·
          refine ⟨82847052651637852053462643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110462736868850469404616857 82847052651637852053462643)
          ·
            refine ⟨124270578977456778080193965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82847052651637852053462643 124270578977456778080193965)
            ·
              refine ⟨46601467116546291780072737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124270578977456778080193965 46601467116546291780072737)
              ·
                refine ⟨34951100337409718835054553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46601467116546291780072737 34951100337409718835054553)
                ·
                  refine ⟨26213325253057289126290915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34951100337409718835054553 26213325253057289126290915)
                  ·
                    refine ⟨39319987879585933689436373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26213325253057289126290915 39319987879585933689436373)
                    ·
                      refine ⟨921562215927795320846165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39319987879585933689436373 921562215927795320846165)
                      ·
                        rfl

theorem cell23_1794736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1794736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794736 prefixEnd_1794736 := by exact prefixLift 1794736
  have htrace : WordTrace (prefixWord ++ tailWord_1794736) baseStart_1794736 baseEnd_1794736 := by
    simpa [prefixWord, tailWord_1794736, baseEnd_1794736] using wordTrace_append hprefix tailTrace_1794736
  have hstable : (prefixWord ++ tailWord_1794736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794736).length < 2 ^ (prefixWord ++ tailWord_1794736).sum := by decide
  have hdescent : baseEnd_1794736 < baseStart_1794736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794760 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1794760 : Nat := 118140960795 + 1794760 * 2 ^ 59
def prefixEnd_1794760 : Nat := 4983230072969 + 3 ^ 40 * 1794760 * 2
def baseEnd_1794760 : Nat := 307191513154501075648685

theorem tailTrace_1794760 : CollatzResearch.WordTrace tailWord_1794760 prefixEnd_1794760 307191513154501075648685 := by
  unfold tailWord_1794760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32730137488949257724878867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43640183318599010299838489 32730137488949257724878867)
  ·
    refine ⟨49095206233423886587318301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32730137488949257724878867 49095206233423886587318301)
    ·
      refine ⟨18410702337533957470244363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49095206233423886587318301 18410702337533957470244363)
      ·
        refine ⟨27616053506300936205366545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18410702337533957470244363 27616053506300936205366545)
        ·
          refine ⟨20712040129725702154024909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27616053506300936205366545 20712040129725702154024909)
          ·
            refine ⟨7767015048647138307759341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20712040129725702154024909 7767015048647138307759341)
            ·
              refine ⟨2912630643242676865409753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7767015048647138307759341 2912630643242676865409753)
              ·
                refine ⟨2184472982432007649057315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912630643242676865409753 2184472982432007649057315)
                ·
                  refine ⟨3276709473648011473585973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184472982432007649057315 3276709473648011473585973)
                  ·
                    refine ⟨307191513154501075648685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3276709473648011473585973 307191513154501075648685)
                    ·
                      rfl

theorem cell23_1794760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1794760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794760 prefixEnd_1794760 := by exact prefixLift 1794760
  have htrace : WordTrace (prefixWord ++ tailWord_1794760) baseStart_1794760 baseEnd_1794760 := by
    simpa [prefixWord, tailWord_1794760, baseEnd_1794760] using wordTrace_append hprefix tailTrace_1794760
  have hstable : (prefixWord ++ tailWord_1794760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794760).length < 2 ^ (prefixWord ++ tailWord_1794760).sum := by decide
  have hdescent : baseEnd_1794760 < baseStart_1794760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794814 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1794814 : Nat := 118140960795 + 1794814 * 2 ^ 59
def prefixEnd_1794814 : Nat := 4983230072969 + 3 ^ 40 * 1794814 * 2
def baseEnd_1794814 : Nat := 921602267418846015670807

theorem tailTrace_1794814 : CollatzResearch.WordTrace tailWord_1794814 prefixEnd_1794814 921602267418846015670807 := by
  unfold tailWord_1794814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182780564962860334027937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43641496346468588448148997 8182780564962860334027937)
  ·
    refine ⟨6137085423722145250520953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8182780564962860334027937 6137085423722145250520953)
    ·
      refine ⟨4602814067791608937890715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6137085423722145250520953 4602814067791608937890715)
      ·
        refine ⟨6904221101687413406836073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602814067791608937890715 6904221101687413406836073)
        ·
          refine ⟨5178165826265560055127055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6904221101687413406836073 5178165826265560055127055)
          ·
            refine ⟨7767248739398340082690583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178165826265560055127055 7767248739398340082690583)
            ·
              refine ⟨11650873109097510124035875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767248739398340082690583 11650873109097510124035875)
              ·
                refine ⟨17476309663646265186053813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11650873109097510124035875 17476309663646265186053813)
                ·
                  refine ⟨1638404030966837361192545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17476309663646265186053813 1638404030966837361192545)
                  ·
                    refine ⟨1228803023225128020894409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638404030966837361192545 1228803023225128020894409)
                    ·
                      refine ⟨921602267418846015670807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1228803023225128020894409 921602267418846015670807)
                      ·
                        rfl

theorem cell23_1794814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1794814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794814 prefixEnd_1794814 := by exact prefixLift 1794814
  have htrace : WordTrace (prefixWord ++ tailWord_1794814) baseStart_1794814 baseEnd_1794814 := by
    simpa [prefixWord, tailWord_1794814, baseEnd_1794814] using wordTrace_append hprefix tailTrace_1794814
  have hstable : (prefixWord ++ tailWord_1794814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794814).length < 2 ^ (prefixWord ++ tailWord_1794814).sum := by decide
  have hdescent : baseEnd_1794814 < baseStart_1794814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794820 : List Nat := [2, 3, 2, 2, 1, 1, 5, 7]
def baseStart_1794820 : Nat := 118140960795 + 1794820 * 2 ^ 59
def prefixEnd_1794820 : Nat := 4983230072969 + 3 ^ 40 * 1794820 * 2
def baseEnd_1794820 : Nat := 34133531418621221933177

theorem tailTrace_1794820 : CollatzResearch.WordTrace tailWord_1794820 prefixEnd_1794820 34133531418621221933177 := by
  unfold tailWord_1794820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32731231678840572848470957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43641642238454097131294609 32731231678840572848470957)
  ·
    refine ⟨12274211879565214818176609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32731231678840572848470957 12274211879565214818176609)
    ·
      refine ⟨9205658909673911113632457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12274211879565214818176609 9205658909673911113632457)
      ·
        refine ⟨6904244182255433335224343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9205658909673911113632457 6904244182255433335224343)
        ·
          refine ⟨10356366273383150002836515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904244182255433335224343 10356366273383150002836515)
          ·
            refine ⟨15534549410074725004254773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356366273383150002836515 15534549410074725004254773)
            ·
              refine ⟨1456364007194505469148885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15534549410074725004254773 1456364007194505469148885)
              ·
                refine ⟨34133531418621221933177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1456364007194505469148885 34133531418621221933177)
                ·
                  rfl

theorem cell23_1794820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 7].length) (baseStart_1794820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794820 prefixEnd_1794820 := by exact prefixLift 1794820
  have htrace : WordTrace (prefixWord ++ tailWord_1794820) baseStart_1794820 baseEnd_1794820 := by
    simpa [prefixWord, tailWord_1794820, baseEnd_1794820] using wordTrace_append hprefix tailTrace_1794820
  have hstable : (prefixWord ++ tailWord_1794820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794820).length < 2 ^ (prefixWord ++ tailWord_1794820).sum := by decide
  have hdescent : baseEnd_1794820 < baseStart_1794820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794847 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 3]
def baseStart_1794847 : Nat := 118140960795 + 1794847 * 2 ^ 59
def prefixEnd_1794847 : Nat := 4983230072969 + 3 ^ 40 * 1794847 * 2
def baseEnd_1794847 : Nat := 921619212280444386558155

theorem tailTrace_1794847 : CollatzResearch.WordTrace tailWord_1794847 prefixEnd_1794847 921619212280444386558155 := by
  unfold tailWord_1794847
  simp only [CollatzResearch.WordTrace]
  refine ⟨65463448128583329308174795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43642298752388886205449863 65463448128583329308174795)
  ·
    refine ⟨98195172192874993962262193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65463448128583329308174795 98195172192874993962262193)
    ·
      refine ⟨73646379144656245471696645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98195172192874993962262193 73646379144656245471696645)
      ·
        refine ⟨13808696089623046025943121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73646379144656245471696645 13808696089623046025943121)
        ·
          refine ⟨10356522067217284519457341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13808696089623046025943121 10356522067217284519457341)
          ·
            refine ⟨3883695775206481694796503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10356522067217284519457341 3883695775206481694796503)
            ·
              refine ⟨5825543662809722542194755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883695775206481694796503 5825543662809722542194755)
              ·
                refine ⟨8738315494214583813292133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5825543662809722542194755 8738315494214583813292133)
                ·
                  refine ⟨1638434155165234464992275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8738315494214583813292133 1638434155165234464992275)
                  ·
                    refine ⟨2457651232747851697488413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1638434155165234464992275 2457651232747851697488413)
                    ·
                      refine ⟨921619212280444386558155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2457651232747851697488413 921619212280444386558155)
                      ·
                        rfl

theorem cell23_1794847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_1794847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794847 prefixEnd_1794847 := by exact prefixLift 1794847
  have htrace : WordTrace (prefixWord ++ tailWord_1794847) baseStart_1794847 baseEnd_1794847 := by
    simpa [prefixWord, tailWord_1794847, baseEnd_1794847] using wordTrace_append hprefix tailTrace_1794847
  have hstable : (prefixWord ++ tailWord_1794847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794847).length < 2 ^ (prefixWord ++ tailWord_1794847).sum := by decide
  have hdescent : baseEnd_1794847 < baseStart_1794847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794861 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1794861 : Nat := 118140960795 + 1794861 * 2 ^ 59
def prefixEnd_1794861 : Nat := 4983230072969 + 3 ^ 40 * 1794861 * 2
def baseEnd_1794861 : Nat := 921626401009607331783091

theorem tailTrace_1794861 : CollatzResearch.WordTrace tailWord_1794861 prefixEnd_1794861 921626401009607331783091 := by
  unfold tailWord_1794861
  simp only [CollatzResearch.WordTrace]
  refine ⟨65463958750532609699184437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43642639167021739799456291 65463958750532609699184437)
  ·
    refine ⟨6137246132862432159298541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65463958750532609699184437 6137246132862432159298541)
    ·
      refine ⟨2301467299823412059736953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6137246132862432159298541 2301467299823412059736953)
      ·
        refine ⟨1726100474867559044802715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2301467299823412059736953 1726100474867559044802715)
        ·
          refine ⟨2589150712301338567204073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726100474867559044802715 2589150712301338567204073)
          ·
            refine ⟨1941863034226003925403055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589150712301338567204073 1941863034226003925403055)
            ·
              refine ⟨2912794551339005888104583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941863034226003925403055 2912794551339005888104583)
              ·
                refine ⟨4369191827008508832156875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912794551339005888104583 4369191827008508832156875)
                ·
                  refine ⟨6553787740512763248235313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369191827008508832156875 6553787740512763248235313)
                  ·
                    refine ⟨4915340805384572436176485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6553787740512763248235313 4915340805384572436176485)
                    ·
                      refine ⟨921626401009607331783091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4915340805384572436176485 921626401009607331783091)
                      ·
                        rfl

theorem cell23_1794861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1794861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794861 prefixEnd_1794861 := by exact prefixLift 1794861
  have htrace : WordTrace (prefixWord ++ tailWord_1794861) baseStart_1794861 baseEnd_1794861 := by
    simpa [prefixWord, tailWord_1794861, baseEnd_1794861] using wordTrace_append hprefix tailTrace_1794861
  have hstable : (prefixWord ++ tailWord_1794861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794861).length < 2 ^ (prefixWord ++ tailWord_1794861).sum := by decide
  have hdescent : baseEnd_1794861 < baseStart_1794861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794913 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1794913 : Nat := 118140960795 + 1794913 * 2 ^ 59
def prefixEnd_1794913 : Nat := 4983230072969 + 3 ^ 40 * 1794913 * 2
def baseEnd_1794913 : Nat := 921653102003641128332851

theorem tailTrace_1794913 : CollatzResearch.WordTrace tailWord_1794913 prefixEnd_1794913 921653102003641128332851 := by
  unfold tailWord_1794913
  simp only [CollatzResearch.WordTrace]
  refine ⟨65465855346344222580077393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43643903564229481720051595 65465855346344222580077393)
  ·
    refine ⟨49099391509758166935058045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65465855346344222580077393 49099391509758166935058045)
    ·
      refine ⟨18412271816159312600646767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49099391509758166935058045 18412271816159312600646767)
      ·
        refine ⟨27618407724238968900970151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18412271816159312600646767 27618407724238968900970151)
        ·
          refine ⟨41427611586358453351455227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27618407724238968900970151 41427611586358453351455227)
          ·
            refine ⟨62141417379537680027182841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41427611586358453351455227 62141417379537680027182841)
            ·
              refine ⟨46606063034653260020387131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62141417379537680027182841 46606063034653260020387131)
              ·
                refine ⟨69909094551979890030580697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46606063034653260020387131 69909094551979890030580697)
                ·
                  refine ⟨52431820913984917522935523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69909094551979890030580697 52431820913984917522935523)
                  ·
                    refine ⟨78647731370977376284403285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52431820913984917522935523 78647731370977376284403285)
                    ·
                      refine ⟨921653102003641128332851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78647731370977376284403285 921653102003641128332851)
                      ·
                        rfl

theorem cell23_1794913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1794913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794913 prefixEnd_1794913 := by exact prefixLift 1794913
  have htrace : WordTrace (prefixWord ++ tailWord_1794913) baseStart_1794913 baseEnd_1794913 := by
    simpa [prefixWord, tailWord_1794913, baseEnd_1794913] using wordTrace_append hprefix tailTrace_1794913
  have hstable : (prefixWord ++ tailWord_1794913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794913).length < 2 ^ (prefixWord ++ tailWord_1794913).sum := by decide
  have hdescent : baseEnd_1794913 < baseStart_1794913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794923 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 7]
def baseStart_1794923 : Nat := 118140960795 + 1794923 * 2 ^ 59
def prefixEnd_1794923 : Nat := 4983230072969 + 3 ^ 40 * 1794923 * 2
def baseEnd_1794923 : Nat := 307219412270062029735935

theorem tailTrace_1794923 : CollatzResearch.WordTrace tailWord_1794923 prefixEnd_1794923 307219412270062029735935 := by
  unfold tailWord_1794923
  simp only [CollatzResearch.WordTrace]
  refine ⟨65466220076307994287941423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43644146717538662858627615 65466220076307994287941423)
  ·
    refine ⟨98199330114461991431912135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65466220076307994287941423 98199330114461991431912135)
    ·
      refine ⟨147298995171692987147868203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98199330114461991431912135 147298995171692987147868203)
      ·
        refine ⟨220948492757539480721802305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147298995171692987147868203 220948492757539480721802305)
        ·
          refine ⟨165711369568154610541351729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220948492757539480721802305 165711369568154610541351729)
          ·
            refine ⟨124283527176115957906013797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165711369568154610541351729 124283527176115957906013797)
            ·
              refine ⟨23303161345521742107377587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124283527176115957906013797 23303161345521742107377587)
              ·
                refine ⟨34954742018282613161066381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23303161345521742107377587 34954742018282613161066381)
                ·
                  refine ⟨13108028256855979935399893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34954742018282613161066381 13108028256855979935399893)
                  ·
                    refine ⟨307219412270062029735935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13108028256855979935399893 307219412270062029735935)
                    ·
                      rfl

theorem cell23_1794923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_1794923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794923 prefixEnd_1794923 := by exact prefixLift 1794923
  have htrace : WordTrace (prefixWord ++ tailWord_1794923) baseStart_1794923 baseEnd_1794923 := by
    simpa [prefixWord, tailWord_1794923, baseEnd_1794923] using wordTrace_append hprefix tailTrace_1794923
  have hstable : (prefixWord ++ tailWord_1794923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794923).length < 2 ^ (prefixWord ++ tailWord_1794923).sum := by decide
  have hdescent : baseEnd_1794923 < baseStart_1794923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1794997 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1794997 : Nat := 118140960795 + 1794997 * 2 ^ 59
def prefixEnd_1794997 : Nat := 4983230072969 + 3 ^ 40 * 1794997 * 2
def baseEnd_1794997 : Nat := 921696234378618799682465

theorem tailTrace_1794997 : CollatzResearch.WordTrace tailWord_1794997 prefixEnd_1794997 921696234378618799682465 := by
  unfold tailWord_1794997
  simp only [CollatzResearch.WordTrace]
  refine ⟨65468919078039904926135245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43645946052026603284090163 65468919078039904926135245)
  ·
    refine ⟨24550844654264964347300717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65468919078039904926135245 24550844654264964347300717)
    ·
      refine ⟨9206566745349361630237769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24550844654264964347300717 9206566745349361630237769)
      ·
        refine ⟨6904925059012021222678327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9206566745349361630237769 6904925059012021222678327)
        ·
          refine ⟨10357387588518031834017491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904925059012021222678327 10357387588518031834017491)
          ·
            refine ⟨15536081382777047751026237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10357387588518031834017491 15536081382777047751026237)
            ·
              refine ⟨5826030518541392906634839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15536081382777047751026237 5826030518541392906634839)
              ·
                refine ⟨8739045777812089359952259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826030518541392906634839 8739045777812089359952259)
                ·
                  refine ⟨13108568666718134039928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739045777812089359952259 13108568666718134039928389)
                  ·
                    refine ⟨2457856625009650132486573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13108568666718134039928389 2457856625009650132486573)
                    ·
                      refine ⟨921696234378618799682465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2457856625009650132486573 921696234378618799682465)
                      ·
                        rfl

theorem cell23_1794997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1794997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1794997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1794997 prefixEnd_1794997 := by exact prefixLift 1794997
  have htrace : WordTrace (prefixWord ++ tailWord_1794997) baseStart_1794997 baseEnd_1794997 := by
    simpa [prefixWord, tailWord_1794997, baseEnd_1794997] using wordTrace_append hprefix tailTrace_1794997
  have hstable : (prefixWord ++ tailWord_1794997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1794997).length < 2 ^ (prefixWord ++ tailWord_1794997).sum := by decide
  have hdescent : baseEnd_1794997 < baseStart_1794997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1794997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795020 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1795020 : Nat := 118140960795 + 1795020 * 2 ^ 59
def prefixEnd_1795020 : Nat := 4983230072969 + 3 ^ 40 * 1795020 * 2
def baseEnd_1795020 : Nat := 921708044433672209694859

theorem tailTrace_1795020 : CollatzResearch.WordTrace tailWord_1795020 prefixEnd_1795020 921708044433672209694859 := by
  unfold tailWord_1795020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32734878978478289927111257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43646505304637719902815009 32734878978478289927111257)
  ·
    refine ⟨24551159233858717445333443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32734878978478289927111257 24551159233858717445333443)
    ·
      refine ⟨36826738850788076168000165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24551159233858717445333443 36826738850788076168000165)
      ·
        refine ⟨6905013534522764281500031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36826738850788076168000165 6905013534522764281500031)
        ·
          refine ⟨10357520301784146422250047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905013534522764281500031 10357520301784146422250047)
          ·
            refine ⟨15536280452676219633375071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10357520301784146422250047 15536280452676219633375071)
            ·
              refine ⟨23304420679014329450062607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15536280452676219633375071 23304420679014329450062607)
              ·
                refine ⟨34956631018521494175093911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23304420679014329450062607 34956631018521494175093911)
                ·
                  refine ⟨52434946527782241262640867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34956631018521494175093911 52434946527782241262640867)
                  ·
                    refine ⟨78652419791673361893961301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52434946527782241262640867 78652419791673361893961301)
                    ·
                      refine ⟨921708044433672209694859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78652419791673361893961301 921708044433672209694859)
                      ·
                        rfl

theorem cell23_1795020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1795020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795020 prefixEnd_1795020 := by exact prefixLift 1795020
  have htrace : WordTrace (prefixWord ++ tailWord_1795020) baseStart_1795020 baseEnd_1795020 := by
    simpa [prefixWord, tailWord_1795020, baseEnd_1795020] using wordTrace_append hprefix tailTrace_1795020
  have hstable : (prefixWord ++ tailWord_1795020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795020).length < 2 ^ (prefixWord ++ tailWord_1795020).sum := by decide
  have hdescent : baseEnd_1795020 < baseStart_1795020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795034 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_1795034 : Nat := 118140960795 + 1795034 * 2 ^ 59
def prefixEnd_1795034 : Nat := 4983230072969 + 3 ^ 40 * 1795034 * 2
def baseEnd_1795034 : Nat := 102412803684759461657755

theorem tailTrace_1795034 : CollatzResearch.WordTrace tailWord_1795034 prefixEnd_1795034 102412803684759461657755 := by
  unfold tailWord_1795034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367567144726465061308039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43646845719270573496821437 16367567144726465061308039)
  ·
    refine ⟨24551350717089697591962059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16367567144726465061308039 24551350717089697591962059)
    ·
      refine ⟨36827026075634546387943089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24551350717089697591962059 36827026075634546387943089)
      ·
        refine ⟨27620269556725909790957317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36827026075634546387943089 27620269556725909790957317)
        ·
          refine ⟨5178800541886108085804497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27620269556725909790957317 5178800541886108085804497)
          ·
            refine ⟨3884100406414581064353373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178800541886108085804497 3884100406414581064353373)
            ·
              refine ⟨1456537652405467899132515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3884100406414581064353373 1456537652405467899132515)
              ·
                refine ⟨2184806478608201848698773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456537652405467899132515 2184806478608201848698773)
                ·
                  refine ⟨102412803684759461657755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2184806478608201848698773 102412803684759461657755)
                  ·
                    rfl

theorem cell23_1795034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_1795034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795034 prefixEnd_1795034 := by exact prefixLift 1795034
  have htrace : WordTrace (prefixWord ++ tailWord_1795034) baseStart_1795034 baseEnd_1795034 := by
    simpa [prefixWord, tailWord_1795034, baseEnd_1795034] using wordTrace_append hprefix tailTrace_1795034
  have hstable : (prefixWord ++ tailWord_1795034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795034).length < 2 ^ (prefixWord ++ tailWord_1795034).sum := by decide
  have hdescent : baseEnd_1795034 < baseStart_1795034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795077 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_1795077 : Nat := 118140960795 + 1795077 * 2 ^ 59
def prefixEnd_1795077 : Nat := 4983230072969 + 3 ^ 40 * 1795077 * 2
def baseEnd_1795077 : Nat := 307245770943659495560699

theorem tailTrace_1795077 : CollatzResearch.WordTrace tailWord_1795077 prefixEnd_1795077 307245770943659495560699 := by
  unfold tailWord_1795077
  simp only [CollatzResearch.WordTrace]
  refine ⟨65471836917750078589047485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43647891278500052392698323 65471836917750078589047485)
  ·
    refine ⟨24551938844156279470892807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65471836917750078589047485 24551938844156279470892807)
    ·
      refine ⟨36827908266234419206339211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24551938844156279470892807 36827908266234419206339211)
      ·
        refine ⟨55241862399351628809508817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36827908266234419206339211 55241862399351628809508817)
        ·
          refine ⟨41431396799513721607131613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55241862399351628809508817 41431396799513721607131613)
          ·
            refine ⟨15536773799817645602674355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41431396799513721607131613 15536773799817645602674355)
            ·
              refine ⟨23305160699726468404011533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15536773799817645602674355 23305160699726468404011533)
              ·
                refine ⟨8739435262397425651504325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23305160699726468404011533 8739435262397425651504325)
                ·
                  refine ⟨1638644111699517309657061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8739435262397425651504325 1638644111699517309657061)
                  ·
                    refine ⟨307245770943659495560699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638644111699517309657061 307245770943659495560699)
                    ·
                      rfl

theorem cell23_1795077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_1795077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795077 prefixEnd_1795077 := by exact prefixLift 1795077
  have htrace : WordTrace (prefixWord ++ tailWord_1795077) baseStart_1795077 baseEnd_1795077 := by
    simpa [prefixWord, tailWord_1795077, baseEnd_1795077] using wordTrace_append hprefix tailTrace_1795077
  have hstable : (prefixWord ++ tailWord_1795077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795077).length < 2 ^ (prefixWord ++ tailWord_1795077).sum := by decide
  have hdescent : baseEnd_1795077 < baseStart_1795077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795121 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_1795121 : Nat := 118140960795 + 1795121 * 2 ^ 59
def prefixEnd_1795121 : Nat := 4983230072969 + 3 ^ 40 * 1795121 * 2
def baseEnd_1795121 : Nat := 921759905979776314531895

theorem tailTrace_1795121 : CollatzResearch.WordTrace tailWord_1795121 prefixEnd_1795121 921759905979776314531895 := by
  unfold tailWord_1795121
  simp only [CollatzResearch.WordTrace]
  refine ⟨65473441729590674103649217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43648961153060449402432811 65473441729590674103649217)
  ·
    refine ⟨49105081297193005577736913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65473441729590674103649217 49105081297193005577736913)
    ·
      refine ⟨36828810972894754183302685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49105081297193005577736913 36828810972894754183302685)
      ·
        refine ⟨13810804114835532818738507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36828810972894754183302685 13810804114835532818738507)
        ·
          refine ⟨20716206172253299228107761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810804114835532818738507 20716206172253299228107761)
          ·
            refine ⟨15537154629189974421080821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20716206172253299228107761 15537154629189974421080821)
            ·
              refine ⟨1456608246486560101976327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15537154629189974421080821 1456608246486560101976327)
              ·
                refine ⟨2184912369729840152964491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456608246486560101976327 2184912369729840152964491)
                ·
                  refine ⟨3277368554594760229446737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184912369729840152964491 3277368554594760229446737)
                  ·
                    refine ⟨2458026415946070172085053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3277368554594760229446737 2458026415946070172085053)
                    ·
                      refine ⟨921759905979776314531895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2458026415946070172085053 921759905979776314531895)
                      ·
                        rfl

theorem cell23_1795121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_1795121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795121 prefixEnd_1795121 := by exact prefixLift 1795121
  have htrace : WordTrace (prefixWord ++ tailWord_1795121) baseStart_1795121 baseEnd_1795121 := by
    simpa [prefixWord, tailWord_1795121, baseEnd_1795121] using wordTrace_append hprefix tailTrace_1795121
  have hstable : (prefixWord ++ tailWord_1795121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795121).length < 2 ^ (prefixWord ++ tailWord_1795121).sum := by decide
  have hdescent : baseEnd_1795121 < baseStart_1795121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795144 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_1795144 : Nat := 118140960795 + 1795144 * 2 ^ 59
def prefixEnd_1795144 : Nat := 4983230072969 + 3 ^ 40 * 1795144 * 2
def baseEnd_1795144 : Nat := 921771716034829724544289

theorem tailTrace_1795144 : CollatzResearch.WordTrace tailWord_1795144 prefixEnd_1795144 921771716034829724544289 := by
  unfold tailWord_1795144
  simp only [CollatzResearch.WordTrace]
  refine ⟨32737140304253674515868243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43649520405671566021157657 32737140304253674515868243)
  ·
    refine ⟨49105710456380511773802365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32737140304253674515868243 49105710456380511773802365)
    ·
      refine ⟨18414641421142691915175887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49105710456380511773802365 18414641421142691915175887)
      ·
        refine ⟨27621962131714037872763831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414641421142691915175887 27621962131714037872763831)
        ·
          refine ⟨41432943197571056809145747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27621962131714037872763831 41432943197571056809145747)
          ·
            refine ⟨62149414796356585213718621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41432943197571056809145747 62149414796356585213718621)
            ·
              refine ⟨23306030548633719455144483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62149414796356585213718621 23306030548633719455144483)
              ·
                refine ⟨34959045822950579182716725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23306030548633719455144483 34959045822950579182716725)
                ·
                  refine ⟨3277410545901616798379693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34959045822950579182716725 3277410545901616798379693)
                  ·
                    refine ⟨1229028954713106299392385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277410545901616798379693 1229028954713106299392385)
                    ·
                      refine ⟨921771716034829724544289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229028954713106299392385 921771716034829724544289)
                      ·
                        rfl

theorem cell23_1795144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_1795144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795144 prefixEnd_1795144 := by exact prefixLift 1795144
  have htrace : WordTrace (prefixWord ++ tailWord_1795144) baseStart_1795144 baseEnd_1795144 := by
    simpa [prefixWord, tailWord_1795144, baseEnd_1795144] using wordTrace_append hprefix tailTrace_1795144
  have hstable : (prefixWord ++ tailWord_1795144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795144).length < 2 ^ (prefixWord ++ tailWord_1795144).sum := by decide
  have hdescent : baseEnd_1795144 < baseStart_1795144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795157 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1795157 : Nat := 118140960795 + 1795157 * 2 ^ 59
def prefixEnd_1795157 : Nat := 4983230072969 + 3 ^ 40 * 1795157 * 2
def baseEnd_1795157 : Nat := 921778391283338173681729

theorem tailTrace_1795157 : CollatzResearch.WordTrace tailWord_1795157 prefixEnd_1795157 921778391283338173681729 := by
  unfold tailWord_1795157
  simp only [CollatzResearch.WordTrace]
  refine ⟨65474754757460252251959725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43649836504973501501306483 65474754757460252251959725)
  ·
    refine ⟨24553033034047594594484897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65474754757460252251959725 24553033034047594594484897)
    ·
      refine ⟨18414774775535695945863673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24553033034047594594484897 18414774775535695945863673)
      ·
        refine ⟨13811081081651771959397755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18414774775535695945863673 13811081081651771959397755)
        ·
          refine ⟨20716621622477657939096633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13811081081651771959397755 20716621622477657939096633)
          ·
            refine ⟨15537466216858243454322475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20716621622477657939096633 15537466216858243454322475)
            ·
              refine ⟨23306199325287365181483713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15537466216858243454322475 23306199325287365181483713)
              ·
                refine ⟨17479649493965523886112785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23306199325287365181483713 17479649493965523886112785)
                ·
                  refine ⟨13109737120474142914584589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17479649493965523886112785 13109737120474142914584589)
                  ·
                    refine ⟨4916151420177803592969221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13109737120474142914584589 4916151420177803592969221)
                    ·
                      refine ⟨921778391283338173681729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4916151420177803592969221 921778391283338173681729)
                      ·
                        rfl

theorem cell23_1795157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1795157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795157 prefixEnd_1795157 := by exact prefixLift 1795157
  have htrace : WordTrace (prefixWord ++ tailWord_1795157) baseStart_1795157 baseEnd_1795157 := by
    simpa [prefixWord, tailWord_1795157, baseEnd_1795157] using wordTrace_append hprefix tailTrace_1795157
  have hstable : (prefixWord ++ tailWord_1795157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795157).length < 2 ^ (prefixWord ++ tailWord_1795157).sum := by decide
  have hdescent : baseEnd_1795157 < baseStart_1795157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795158 : List Nat := [5, 2, 2, 1, 2, 1, 3, 7]
def baseStart_1795158 : Nat := 118140960795 + 1795158 * 2 ^ 59
def prefixEnd_1795158 : Nat := 4983230072969 + 3 ^ 40 * 1795158 * 2
def baseEnd_1795158 : Nat := 34139959435703432213675

theorem tailTrace_1795158 : CollatzResearch.WordTrace tailWord_1795158 prefixEnd_1795158 34139959435703432213675 := by
  unfold tailWord_1795158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092174451903539338921633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43649860820304419615164085 4092174451903539338921633)
  ·
    refine ⟨3069130838927654504191225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4092174451903539338921633 3069130838927654504191225)
    ·
      refine ⟨2301848129195740878143419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069130838927654504191225 2301848129195740878143419)
      ·
        refine ⟨3452772193793611317215129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301848129195740878143419 3452772193793611317215129)
        ·
          refine ⟨2589579145345208487911347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452772193793611317215129 2589579145345208487911347)
          ·
            refine ⟨3884368718017812731867021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589579145345208487911347 3884368718017812731867021)
            ·
              refine ⟨1456638269256679774450133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3884368718017812731867021 1456638269256679774450133)
              ·
                refine ⟨34139959435703432213675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1456638269256679774450133 34139959435703432213675)
                ·
                  rfl

theorem cell23_1795158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_1795158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795158 prefixEnd_1795158 := by exact prefixLift 1795158
  have htrace : WordTrace (prefixWord ++ tailWord_1795158) baseStart_1795158 baseEnd_1795158 := by
    simpa [prefixWord, tailWord_1795158, baseEnd_1795158] using wordTrace_append hprefix tailTrace_1795158
  have hstable : (prefixWord ++ tailWord_1795158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795158).length < 2 ^ (prefixWord ++ tailWord_1795158).sum := by decide
  have hdescent : baseEnd_1795158 < baseStart_1795158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795178 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1795178 : Nat := 118140960795 + 1795178 * 2 ^ 59
def prefixEnd_1795178 : Nat := 4983230072969 + 3 ^ 40 * 1795178 * 2
def baseEnd_1795178 : Nat := 921789174377082591519133

theorem tailTrace_1795178 : CollatzResearch.WordTrace tailWord_1795178 prefixEnd_1795178 921789174377082591519133 := by
  unfold tailWord_1795178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368880172596043209618547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43650347126922781892316125 16368880172596043209618547)
  ·
    refine ⟨24553320258894064814427821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368880172596043209618547 24553320258894064814427821)
    ·
      refine ⟨9207495097085274305410433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24553320258894064814427821 9207495097085274305410433)
      ·
        refine ⟨6905621322813955729057825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9207495097085274305410433 6905621322813955729057825)
        ·
          refine ⟨5179215992110466796793369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905621322813955729057825 5179215992110466796793369)
          ·
            refine ⟨3884411994082850097595027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5179215992110466796793369 3884411994082850097595027)
            ·
              refine ⟨5826617991124275146392541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884411994082850097595027 5826617991124275146392541)
              ·
                refine ⟨2184981746671603179897203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5826617991124275146392541 2184981746671603179897203)
                ·
                  refine ⟨3277472620007404769845805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184981746671603179897203 3277472620007404769845805)
                  ·
                    refine ⟨1229052232502776788692177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277472620007404769845805 1229052232502776788692177)
                    ·
                      refine ⟨921789174377082591519133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229052232502776788692177 921789174377082591519133)
                      ·
                        rfl

theorem cell23_1795178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1795178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795178 prefixEnd_1795178 := by exact prefixLift 1795178
  have htrace : WordTrace (prefixWord ++ tailWord_1795178) baseStart_1795178 baseEnd_1795178 := by
    simpa [prefixWord, tailWord_1795178, baseEnd_1795178] using wordTrace_append hprefix tailTrace_1795178
  have hstable : (prefixWord ++ tailWord_1795178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795178).length < 2 ^ (prefixWord ++ tailWord_1795178).sum := by decide
  have hdescent : baseEnd_1795178 < baseStart_1795178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795191 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_1795191 : Nat := 118140960795 + 1795191 * 2 ^ 59
def prefixEnd_1795191 : Nat := 4983230072969 + 3 ^ 40 * 1795191 * 2
def baseEnd_1795191 : Nat := 921795849625591040656573

theorem tailTrace_1795191 : CollatzResearch.WordTrace tailWord_1795191 prefixEnd_1795191 921795849625591040656573 := by
  unfold tailWord_1795191
  simp only [CollatzResearch.WordTrace]
  refine ⟨65475994839337076058697427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43650663226224717372464951 65475994839337076058697427)
  ·
    refine ⟨98213992259005614088046141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65475994839337076058697427 98213992259005614088046141)
    ·
      refine ⟨36830247097127105283017303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98213992259005614088046141 36830247097127105283017303)
      ·
        refine ⟨55245370645690657924525955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36830247097127105283017303 55245370645690657924525955)
        ·
          refine ⟨82868055968535986886788933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55245370645690657924525955 82868055968535986886788933)
          ·
            refine ⟨15537760494100497541272925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82868055968535986886788933 15537760494100497541272925)
            ·
              refine ⟨5826660185287686577977347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15537760494100497541272925 5826660185287686577977347)
              ·
                refine ⟨8739990277931529866966021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826660185287686577977347 8739990277931529866966021)
                ·
                  refine ⟨1638748177112161850056129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8739990277931529866966021 1638748177112161850056129)
                  ·
                    refine ⟨1229061132834121387542097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638748177112161850056129 1229061132834121387542097)
                    ·
                      refine ⟨921795849625591040656573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229061132834121387542097 921795849625591040656573)
                      ·
                        rfl

theorem cell23_1795191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_1795191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795191 prefixEnd_1795191 := by exact prefixLift 1795191
  have htrace : WordTrace (prefixWord ++ tailWord_1795191) baseStart_1795191 baseEnd_1795191 := by
    simpa [prefixWord, tailWord_1795191, baseEnd_1795191] using wordTrace_append hprefix tailTrace_1795191
  have hstable : (prefixWord ++ tailWord_1795191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795191).length < 2 ^ (prefixWord ++ tailWord_1795191).sum := by decide
  have hdescent : baseEnd_1795191 < baseStart_1795191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795204 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1795204 : Nat := 118140960795 + 1795204 * 2 ^ 59
def prefixEnd_1795204 : Nat := 4983230072969 + 3 ^ 40 * 1795204 * 2
def baseEnd_1795204 : Nat := 921802524874099489794013

theorem tailTrace_1795204 : CollatzResearch.WordTrace tailWord_1795204 prefixEnd_1795204 921802524874099489794013 := by
  unfold tailWord_1795204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32738234494144989639460333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43650979325526652852613777 32738234494144989639460333)
  ·
    refine ⟨12276837935304371114797625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32738234494144989639460333 12276837935304371114797625)
    ·
      refine ⟨9207628451478278336098219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12276837935304371114797625 9207628451478278336098219)
      ·
        refine ⟨13811442677217417504147329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207628451478278336098219 13811442677217417504147329)
        ·
          refine ⟨10358582007913063128110497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811442677217417504147329 10358582007913063128110497)
          ·
            refine ⟨7768936505934797346082873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10358582007913063128110497 7768936505934797346082873)
            ·
              refine ⟨5826702379451098009562155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768936505934797346082873 5826702379451098009562155)
              ·
                refine ⟨8740053569176647014343233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826702379451098009562155 8740053569176647014343233)
                ·
                  refine ⟨6555040176882485260757425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8740053569176647014343233 6555040176882485260757425)
                  ·
                    refine ⟨4916280132661863945568069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555040176882485260757425 4916280132661863945568069)
                    ·
                      refine ⟨921802524874099489794013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4916280132661863945568069 921802524874099489794013)
                      ·
                        rfl

theorem cell23_1795204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1795204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795204 prefixEnd_1795204 := by exact prefixLift 1795204
  have htrace : WordTrace (prefixWord ++ tailWord_1795204) baseStart_1795204 baseEnd_1795204 := by
    simpa [prefixWord, tailWord_1795204, baseEnd_1795204] using wordTrace_append hprefix tailTrace_1795204
  have hstable : (prefixWord ++ tailWord_1795204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795204).length < 2 ^ (prefixWord ++ tailWord_1795204).sum := by decide
  have hdescent : baseEnd_1795204 < baseStart_1795204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795214 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_1795214 : Nat := 118140960795 + 1795214 * 2 ^ 59
def prefixEnd_1795214 : Nat := 4983230072969 + 3 ^ 40 * 1795214 * 2
def baseEnd_1795214 : Nat := 102423073297849383407663

theorem tailTrace_1795214 : CollatzResearch.WordTrace tailWord_1795214 prefixEnd_1795214 102423073297849383407663 := by
  unfold tailWord_1795214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184604214781718873348087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43651222478835833991189797 8184604214781718873348087)
  ·
    refine ⟨12276906322172578310022131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184604214781718873348087 12276906322172578310022131)
    ·
      refine ⟨18415359483258867465033197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276906322172578310022131 18415359483258867465033197)
      ·
        refine ⟨6905759806222075299387449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18415359483258867465033197 6905759806222075299387449)
        ·
          refine ⟨5179319854666556474540587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905759806222075299387449 5179319854666556474540587)
          ·
            refine ⟨7768979781999834711810881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179319854666556474540587 7768979781999834711810881)
            ·
              refine ⟨5826734836499876033858161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7768979781999834711810881 5826734836499876033858161)
              ·
                refine ⟨4370051127374907025393621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826734836499876033858161 4370051127374907025393621)
                ·
                  refine ⟨102423073297849383407663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4370051127374907025393621 102423073297849383407663)
                  ·
                    rfl

theorem cell23_1795214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_1795214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795214 prefixEnd_1795214 := by exact prefixLift 1795214
  have htrace : WordTrace (prefixWord ++ tailWord_1795214) baseStart_1795214 baseEnd_1795214 := by
    simpa [prefixWord, tailWord_1795214, baseEnd_1795214] using wordTrace_append hprefix tailTrace_1795214
  have hstable : (prefixWord ++ tailWord_1795214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795214).length < 2 ^ (prefixWord ++ tailWord_1795214).sum := by decide
  have hdescent : baseEnd_1795214 < baseStart_1795214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795287 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 10]
def baseStart_1795287 : Nat := 118140960795 + 1795287 * 2 ^ 59
def prefixEnd_1795287 : Nat := 4983230072969 + 3 ^ 40 * 1795287 * 2
def baseEnd_1795287 : Nat := 102427238196491407228459

theorem tailTrace_1795287 : CollatzResearch.WordTrace tailWord_1795287 prefixEnd_1795287 102427238196491407228459 := by
  unfold tailWord_1795287
  simp only [CollatzResearch.WordTrace]
  refine ⟨65479496246989284454192115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43652997497992856302794743 65479496246989284454192115)
  ·
    refine ⟨98219244370483926681288173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65479496246989284454192115 98219244370483926681288173)
    ·
      refine ⟨36832216638931472505483065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98219244370483926681288173 36832216638931472505483065)
      ·
        refine ⟨27624162479198604379112299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36832216638931472505483065 27624162479198604379112299)
        ·
          refine ⟨41436243718797906568668449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27624162479198604379112299 41436243718797906568668449)
          ·
            refine ⟨31077182789098429926501337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41436243718797906568668449 31077182789098429926501337)
            ·
              refine ⟨23307887091823822444876003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31077182789098429926501337 23307887091823822444876003)
              ·
                refine ⟨34961830637735733667314005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23307887091823822444876003 34961830637735733667314005)
                ·
                  refine ⟨102427238196491407228459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34961830637735733667314005 102427238196491407228459)
                  ·
                    rfl

theorem cell23_1795287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 10].length) (baseStart_1795287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795287 prefixEnd_1795287 := by exact prefixLift 1795287
  have htrace : WordTrace (prefixWord ++ tailWord_1795287) baseStart_1795287 baseEnd_1795287 := by
    simpa [prefixWord, tailWord_1795287, baseEnd_1795287] using wordTrace_append hprefix tailTrace_1795287
  have hstable : (prefixWord ++ tailWord_1795287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795287).length < 2 ^ (prefixWord ++ tailWord_1795287).sum := by decide
  have hdescent : baseEnd_1795287 < baseStart_1795287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795308 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_1795308 : Nat := 118140960795 + 1795308 * 2 ^ 59
def prefixEnd_1795308 : Nat := 4983230072969 + 3 ^ 40 * 1795308 * 2
def baseEnd_1795308 : Nat := 307285308954055694297845

theorem tailTrace_1795308 : CollatzResearch.WordTrace tailWord_1795308 prefixEnd_1795308 307285308954055694297845 := by
  unfold tailWord_1795308
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740131089956602520353289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43653508119942136693804385 32740131089956602520353289)
  ·
    refine ⟨24555098317467451890264967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32740131089956602520353289 24555098317467451890264967)
    ·
      refine ⟨36832647476201177835397451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555098317467451890264967 36832647476201177835397451)
      ·
        refine ⟨55248971214301766753096177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36832647476201177835397451 55248971214301766753096177)
        ·
          refine ⟨41436728410726325064822133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55248971214301766753096177 41436728410726325064822133)
          ·
            refine ⟨3884693288505592974827075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41436728410726325064822133 3884693288505592974827075)
            ·
              refine ⟨5827039932758389462240613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884693288505592974827075 5827039932758389462240613)
              ·
                refine ⟨1092569987392198024170115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5827039932758389462240613 1092569987392198024170115)
                ·
                  refine ⟨1638854981088297036255173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092569987392198024170115 1638854981088297036255173)
                  ·
                    refine ⟨307285308954055694297845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638854981088297036255173 307285308954055694297845)
                    ·
                      rfl

theorem cell23_1795308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_1795308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795308 prefixEnd_1795308 := by exact prefixLift 1795308
  have htrace : WordTrace (prefixWord ++ tailWord_1795308) baseStart_1795308 baseEnd_1795308 := by
    simpa [prefixWord, tailWord_1795308, baseEnd_1795308] using wordTrace_append hprefix tailTrace_1795308
  have hstable : (prefixWord ++ tailWord_1795308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795308).length < 2 ^ (prefixWord ++ tailWord_1795308).sum := by decide
  have hdescent : baseEnd_1795308 < baseStart_1795308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795331 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 3]
def baseStart_1795331 : Nat := 118140960795 + 1795331 * 2 ^ 59
def prefixEnd_1795331 : Nat := 4983230072969 + 3 ^ 40 * 1795331 * 2
def baseEnd_1795331 : Nat := 921867736917220492905929

theorem tailTrace_1795331 : CollatzResearch.WordTrace tailWord_1795331 prefixEnd_1795331 921867736917220492905929 := by
  unfold tailWord_1795331
  simp only [CollatzResearch.WordTrace]
  refine ⟨65481101058829879968793847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43654067372553253312529231 65481101058829879968793847)
  ·
    refine ⟨98221651588244819953190771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65481101058829879968793847 98221651588244819953190771)
    ·
      refine ⟨147332477382367229929786157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98221651588244819953190771 147332477382367229929786157)
      ·
        refine ⟨55249679018387711223669809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147332477382367229929786157 55249679018387711223669809)
        ·
          refine ⟨41437259263790783417752357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55249679018387711223669809 41437259263790783417752357)
          ·
            refine ⟨7769486111960771890828567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41437259263790783417752357 7769486111960771890828567)
            ·
              refine ⟨11654229167941157836242851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769486111960771890828567 11654229167941157836242851)
              ·
                refine ⟨17481343751911736754364277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11654229167941157836242851 17481343751911736754364277)
                ·
                  refine ⟨1638875976741725320721651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17481343751911736754364277 1638875976741725320721651)
                  ·
                    refine ⟨2458313965112587981082477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1638875976741725320721651 2458313965112587981082477)
                    ·
                      refine ⟨921867736917220492905929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2458313965112587981082477 921867736917220492905929)
                      ·
                        rfl

theorem cell23_1795331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_1795331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795331 prefixEnd_1795331 := by exact prefixLift 1795331
  have htrace : WordTrace (prefixWord ++ tailWord_1795331) baseStart_1795331 baseEnd_1795331 := by
    simpa [prefixWord, tailWord_1795331, baseEnd_1795331] using wordTrace_append hprefix tailTrace_1795331
  have hstable : (prefixWord ++ tailWord_1795331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795331).length < 2 ^ (prefixWord ++ tailWord_1795331).sum := by decide
  have hdescent : baseEnd_1795331 < baseStart_1795331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795351 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 1, 5]
def baseStart_1795351 : Nat := 118140960795 + 1795351 * 2 ^ 59
def prefixEnd_1795351 : Nat := 4983230072969 + 3 ^ 40 * 1795351 * 2
def baseEnd_1795351 : Nat := 307292668843436804885279

theorem tailTrace_1795351 : CollatzResearch.WordTrace tailWord_1795351 prefixEnd_1795351 307292668843436804885279 := by
  unfold tailWord_1795351
  simp only [CollatzResearch.WordTrace]
  refine ⟨65481830518757423384521907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43654553679171615589681271 65481830518757423384521907)
  ·
    refine ⟨98222745778136135076782861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65481830518757423384521907 98222745778136135076782861)
    ·
      refine ⟨36833529666801050653793573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98222745778136135076782861 36833529666801050653793573)
      ·
        refine ⟨6906286812525196997586295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36833529666801050653793573 6906286812525196997586295)
        ·
          refine ⟨10359430218787795496379443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906286812525196997586295 10359430218787795496379443)
          ·
            refine ⟨15539145328181693244569165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359430218787795496379443 15539145328181693244569165)
            ·
              refine ⟨5827179498068134966713437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15539145328181693244569165 5827179498068134966713437)
              ·
                refine ⟨2185192311775550612517539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5827179498068134966713437 2185192311775550612517539)
                ·
                  refine ⟨3277788467663325918776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185192311775550612517539 3277788467663325918776309)
                  ·
                    refine ⟨307292668843436804885279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3277788467663325918776309 307292668843436804885279)
                    ·
                      rfl

theorem cell23_1795351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_1795351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795351 prefixEnd_1795351 := by exact prefixLift 1795351
  have htrace : WordTrace (prefixWord ++ tailWord_1795351) baseStart_1795351 baseEnd_1795351 := by
    simpa [prefixWord, tailWord_1795351, baseEnd_1795351] using wordTrace_append hprefix tailTrace_1795351
  have hstable : (prefixWord ++ tailWord_1795351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795351).length < 2 ^ (prefixWord ++ tailWord_1795351).sum := by decide
  have hdescent : baseEnd_1795351 < baseStart_1795351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795365 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 1, 1, 3]
def baseStart_1795365 : Nat := 118140960795 + 1795365 * 2 ^ 59
def prefixEnd_1795365 : Nat := 4983230072969 + 3 ^ 40 * 1795365 * 2
def baseEnd_1795365 : Nat := 921885195259473359880773

theorem tailTrace_1795365 : CollatzResearch.WordTrace tailWord_1795365 prefixEnd_1795365 921885195259473359880773 := by
  unfold tailWord_1795365
  simp only [CollatzResearch.WordTrace]
  refine ⟨65482341140706703775531549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43654894093804469183687699 65482341140706703775531549)
  ·
    refine ⟨24555877927765013915824331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65482341140706703775531549 24555877927765013915824331)
    ·
      refine ⟨36833816891647520873736497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555877927765013915824331 36833816891647520873736497)
      ·
        refine ⟨27625362668735640655302373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36833816891647520873736497 27625362668735640655302373)
        ·
          refine ⟨5179755500387932622869195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27625362668735640655302373 5179755500387932622869195)
          ·
            refine ⟨7769633250581898934303793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179755500387932622869195 7769633250581898934303793)
            ·
              refine ⟨5827224937936424200727845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769633250581898934303793 5827224937936424200727845)
              ·
                refine ⟨1092604675863079537636471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5827224937936424200727845 1092604675863079537636471)
                ·
                  refine ⟨1638907013794619306454707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092604675863079537636471 1638907013794619306454707)
                  ·
                    refine ⟨2458360520691928959682061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1638907013794619306454707 2458360520691928959682061)
                    ·
                      refine ⟨921885195259473359880773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2458360520691928959682061 921885195259473359880773)
                      ·
                        rfl

theorem cell23_1795365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_1795365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795365 prefixEnd_1795365 := by exact prefixLift 1795365
  have htrace : WordTrace (prefixWord ++ tailWord_1795365) baseStart_1795365 baseEnd_1795365 := by
    simpa [prefixWord, tailWord_1795365, baseEnd_1795365] using wordTrace_append hprefix tailTrace_1795365
  have hstable : (prefixWord ++ tailWord_1795365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795365).length < 2 ^ (prefixWord ++ tailWord_1795365).sum := by decide
  have hdescent : baseEnd_1795365 < baseStart_1795365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795381 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1795381 : Nat := 118140960795 + 1795381 * 2 ^ 59
def prefixEnd_1795381 : Nat := 4983230072969 + 3 ^ 40 * 1795381 * 2
def baseEnd_1795381 : Nat := 307297803649981765760233

theorem tailTrace_1795381 : CollatzResearch.WordTrace tailWord_1795381 prefixEnd_1795381 307297803649981765760233 := by
  unfold tailWord_1795381
  simp only [CollatzResearch.WordTrace]
  refine ⟨65482924708648738508113997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43655283139099159005409331 65482924708648738508113997)
  ·
    refine ⟨24556096765743276940542749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65482924708648738508113997 24556096765743276940542749)
    ·
      refine ⟨9208536287153728852703531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24556096765743276940542749 9208536287153728852703531)
      ·
        refine ⟨13812804430730593279055297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208536287153728852703531 13812804430730593279055297)
        ·
          refine ⟨10359603323047944959291473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13812804430730593279055297 10359603323047944959291473)
          ·
            refine ⟨7769702492285958719468605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10359603323047944959291473 7769702492285958719468605)
            ·
              refine ⟨2913638434607234519800727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7769702492285958719468605 2913638434607234519800727)
              ·
                refine ⟨4370457651910851779701091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913638434607234519800727 4370457651910851779701091)
                ·
                  refine ⟨6555686477866277669551637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370457651910851779701091 6555686477866277669551637)
                  ·
                    refine ⟨307297803649981765760233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6555686477866277669551637 307297803649981765760233)
                    ·
                      rfl

theorem cell23_1795381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1795381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795381 prefixEnd_1795381 := by exact prefixLift 1795381
  have htrace : WordTrace (prefixWord ++ tailWord_1795381) baseStart_1795381 baseEnd_1795381 := by
    simpa [prefixWord, tailWord_1795381, baseEnd_1795381] using wordTrace_append hprefix tailTrace_1795381
  have hstable : (prefixWord ++ tailWord_1795381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795381).length < 2 ^ (prefixWord ++ tailWord_1795381).sum := by decide
  have hdescent : baseEnd_1795381 < baseStart_1795381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795388 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1795388 : Nat := 118140960795 + 1795388 * 2 ^ 59
def prefixEnd_1795388 : Nat := 4983230072969 + 3 ^ 40 * 1795388 * 2
def baseEnd_1795388 : Nat := 921897005314526769893167

theorem tailTrace_1795388 : CollatzResearch.WordTrace tailWord_1795388 prefixEnd_1795388 921897005314526769893167 := by
  unfold tailWord_1795388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32741590009811689351809409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43655453346415585802412545 32741590009811689351809409)
  ·
    refine ⟨24556192507358767013857057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32741590009811689351809409 24556192507358767013857057)
    ·
      refine ⟨18417144380519075260392793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24556192507358767013857057 18417144380519075260392793)
      ·
        refine ⟨13812858285389306445294595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18417144380519075260392793 13812858285389306445294595)
        ·
          refine ⟨20719287428083959667941893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812858285389306445294595 20719287428083959667941893)
          ·
            refine ⟨3884866392765742437739105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20719287428083959667941893 3884866392765742437739105)
            ·
              refine ⟨2913649794574306828304329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884866392765742437739105 2913649794574306828304329)
              ·
                refine ⟨2185237345930730121228247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2913649794574306828304329 2185237345930730121228247)
                ·
                  refine ⟨3277856018896095181842371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185237345930730121228247 3277856018896095181842371)
                  ·
                    refine ⟨4916784028344142772763557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3277856018896095181842371 4916784028344142772763557)
                    ·
                      refine ⟨921897005314526769893167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4916784028344142772763557 921897005314526769893167)
                      ·
                        rfl

theorem cell23_1795388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1795388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795388 prefixEnd_1795388 := by exact prefixLift 1795388
  have htrace : WordTrace (prefixWord ++ tailWord_1795388) baseStart_1795388 baseEnd_1795388 := by
    simpa [prefixWord, tailWord_1795388, baseEnd_1795388] using wordTrace_append hprefix tailTrace_1795388
  have hstable : (prefixWord ++ tailWord_1795388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795388).length < 2 ^ (prefixWord ++ tailWord_1795388).sum := by decide
  have hdescent : baseEnd_1795388 < baseStart_1795388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795432 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1795432 : Nat := 118140960795 + 1795432 * 2 ^ 59
def prefixEnd_1795432 : Nat := 4983230072969 + 3 ^ 40 * 1795432 * 2
def baseEnd_1795432 : Nat := 307306532821108199247655

theorem tailTrace_1795432 : CollatzResearch.WordTrace tailWord_1795432 prefixEnd_1795432 307306532821108199247655 := by
  unfold tailWord_1795432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32742392415731987109110275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43656523220975982812147033 32742392415731987109110275)
  ·
    refine ⟨49113588623597980663665413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32742392415731987109110275 49113588623597980663665413)
    ·
      refine ⟨9208797866924621374437265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49113588623597980663665413 9208797866924621374437265)
      ·
        refine ⟨6906598400193466030827949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9208797866924621374437265 6906598400193466030827949)
        ·
          refine ⟨2589974400072549761560481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6906598400193466030827949 2589974400072549761560481)
          ·
            refine ⟨1942480800054412321170361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589974400072549761560481 1942480800054412321170361)
            ·
              refine ⟨1456860600040809240877771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942480800054412321170361 1456860600040809240877771)
              ·
                refine ⟨2185290900061213861316657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456860600040809240877771 2185290900061213861316657)
                ·
                  refine ⟨1638968175045910395987493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2185290900061213861316657 1638968175045910395987493)
                  ·
                    refine ⟨307306532821108199247655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1638968175045910395987493 307306532821108199247655)
                    ·
                      rfl

theorem cell23_1795432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1795432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795432 prefixEnd_1795432 := by exact prefixLift 1795432
  have htrace : WordTrace (prefixWord ++ tailWord_1795432) baseStart_1795432 baseEnd_1795432 := by
    simpa [prefixWord, tailWord_1795432, baseEnd_1795432] using wordTrace_append hprefix tailTrace_1795432
  have hstable : (prefixWord ++ tailWord_1795432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795432).length < 2 ^ (prefixWord ++ tailWord_1795432).sum := by decide
  have hdescent : baseEnd_1795432 < baseStart_1795432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795481 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_1795481 : Nat := 118140960795 + 1795481 * 2 ^ 59
def prefixEnd_1795481 : Nat := 4983230072969 + 3 ^ 40 * 1795481 * 2
def baseEnd_1795481 : Nat := 921944759015394906030239

theorem tailTrace_1795481 : CollatzResearch.WordTrace tailWord_1795481 prefixEnd_1795481 921944759015394906030239 := by
  unfold tailWord_1795481
  simp only [CollatzResearch.WordTrace]
  refine ⟨65486572008286455586754297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43657714672190970391169531 65486572008286455586754297)
  ·
    refine ⟨49114929006214841690065723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65486572008286455586754297 49114929006214841690065723)
    ·
      refine ⟨73672393509322262535098585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49114929006214841690065723 73672393509322262535098585)
      ·
        refine ⟨55254295131991696901323939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73672393509322262535098585 55254295131991696901323939)
        ·
          refine ⟨82881442697987545351985909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55254295131991696901323939 82881442697987545351985909)
          ·
            refine ⟨7770135252936332376748679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82881442697987545351985909 7770135252936332376748679)
            ·
              refine ⟨11655202879404498565123019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770135252936332376748679 11655202879404498565123019)
              ·
                refine ⟨17482804319106747847684529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655202879404498565123019 17482804319106747847684529)
                ·
                  refine ⟨13112103239330060885763397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17482804319106747847684529 13112103239330060885763397)
                  ·
                    refine ⟨2458519357374386416080637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13112103239330060885763397 2458519357374386416080637)
                    ·
                      refine ⟨921944759015394906030239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2458519357374386416080637 921944759015394906030239)
                      ·
                        rfl

theorem cell23_1795481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_1795481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795481 prefixEnd_1795481 := by exact prefixLift 1795481
  have htrace : WordTrace (prefixWord ++ tailWord_1795481) baseStart_1795481 baseEnd_1795481 := by
    simpa [prefixWord, tailWord_1795481, baseEnd_1795481] using wordTrace_append hprefix tailTrace_1795481
  have hstable : (prefixWord ++ tailWord_1795481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795481).length < 2 ^ (prefixWord ++ tailWord_1795481).sum := by decide
  have hdescent : baseEnd_1795481 < baseStart_1795481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795491 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1795491 : Nat := 118140960795 + 1795491 * 2 ^ 59
def prefixEnd_1795491 : Nat := 4983230072969 + 3 ^ 40 * 1795491 * 2
def baseEnd_1795491 : Nat := 921949893821939866905193

theorem tailTrace_1795491 : CollatzResearch.WordTrace tailWord_1795491 prefixEnd_1795491 921949893821939866905193 := by
  unfold tailWord_1795491
  simp only [CollatzResearch.WordTrace]
  refine ⟨65486936738250227294618327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43657957825500151529745551 65486936738250227294618327)
  ·
    refine ⟨98230405107375340941927491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65486936738250227294618327 98230405107375340941927491)
    ·
      refine ⟨147345607661063011412891237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98230405107375340941927491 147345607661063011412891237)
      ·
        refine ⟨27627301436449314639917107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147345607661063011412891237 27627301436449314639917107)
        ·
          refine ⟨41440952154673971959875661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27627301436449314639917107 41440952154673971959875661)
          ·
            refine ⟨15540357058002739484953373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41440952154673971959875661 15540357058002739484953373)
            ·
              refine ⟨5827633896751027306857515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15540357058002739484953373 5827633896751027306857515)
              ·
                refine ⟨8741450845126540960286273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827633896751027306857515 8741450845126540960286273)
                ·
                  refine ⟨6556088133844905720214705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741450845126540960286273 6556088133844905720214705)
                  ·
                    refine ⟨4917066100383679290161029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6556088133844905720214705 4917066100383679290161029)
                    ·
                      refine ⟨921949893821939866905193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4917066100383679290161029 921949893821939866905193)
                      ·
                        rfl

theorem cell23_1795491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1795491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795491 prefixEnd_1795491 := by exact prefixLift 1795491
  have htrace : WordTrace (prefixWord ++ tailWord_1795491) baseStart_1795491 baseEnd_1795491 := by
    simpa [prefixWord, tailWord_1795491, baseEnd_1795491] using wordTrace_append hprefix tailTrace_1795491
  have hstable : (prefixWord ++ tailWord_1795491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795491).length < 2 ^ (prefixWord ++ tailWord_1795491).sum := by decide
  have hdescent : baseEnd_1795491 < baseStart_1795491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795495 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1795495 : Nat := 118140960795 + 1795495 * 2 ^ 59
def prefixEnd_1795495 : Nat := 4983230072969 + 3 ^ 40 * 1795495 * 2
def baseEnd_1795495 : Nat := 921951947744557851255175

theorem tailTrace_1795495 : CollatzResearch.WordTrace tailWord_1795495 prefixEnd_1795495 921951947744557851255175 := by
  unfold tailWord_1795495
  simp only [CollatzResearch.WordTrace]
  refine ⟨65487082630235735977763939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43658055086823823985175959 65487082630235735977763939)
  ·
    refine ⟨98230623945353603966645909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65487082630235735977763939 98230623945353603966645909)
    ·
      refine ⟨4604560497438450185936527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98230623945353603966645909 4604560497438450185936527)
      ·
        refine ⟨6906840746157675278904791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604560497438450185936527 6906840746157675278904791)
        ·
          refine ⟨10360261119236512918357187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906840746157675278904791 10360261119236512918357187)
          ·
            refine ⟨15540391678854769377535781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360261119236512918357187 15540391678854769377535781)
            ·
              refine ⟨2913823439785269258287959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15540391678854769377535781 2913823439785269258287959)
              ·
                refine ⟨4370735159677903887431939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913823439785269258287959 4370735159677903887431939)
                ·
                  refine ⟨6556102739516855831147909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370735159677903887431939 6556102739516855831147909)
                  ·
                    refine ⟨1229269263659410468340233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556102739516855831147909 1229269263659410468340233)
                    ·
                      refine ⟨921951947744557851255175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229269263659410468340233 921951947744557851255175)
                      ·
                        rfl

theorem cell23_1795495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1795495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795495 prefixEnd_1795495 := by exact prefixLift 1795495
  have htrace : WordTrace (prefixWord ++ tailWord_1795495) baseStart_1795495 baseEnd_1795495 := by
    simpa [prefixWord, tailWord_1795495, baseEnd_1795495] using wordTrace_append hprefix tailTrace_1795495
  have hstable : (prefixWord ++ tailWord_1795495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795495).length < 2 ^ (prefixWord ++ tailWord_1795495).sum := by decide
  have hdescent : baseEnd_1795495 < baseStart_1795495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795511 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1795511 : Nat := 118140960795 + 1795511 * 2 ^ 59
def prefixEnd_1795511 : Nat := 4983230072969 + 3 ^ 40 * 1795511 * 2
def baseEnd_1795511 : Nat := 921960163435029788655101

theorem tailTrace_1795511 : CollatzResearch.WordTrace tailWord_1795511 prefixEnd_1795511 921960163435029788655101 := by
  unfold tailWord_1795511
  simp only [CollatzResearch.WordTrace]
  refine ⟨65487666198177770710346387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43658444132118513806897591 65487666198177770710346387)
  ·
    refine ⟨98231499297266656065519581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65487666198177770710346387 98231499297266656065519581)
    ·
      refine ⟨36836812236474996024569843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98231499297266656065519581 36836812236474996024569843)
      ·
        refine ⟨55255218354712494036854765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36836812236474996024569843 55255218354712494036854765)
        ·
          refine ⟨20720706883017185263820537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55255218354712494036854765 20720706883017185263820537)
          ·
            refine ⟨15540530162262888947865403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20720706883017185263820537 15540530162262888947865403)
            ·
              refine ⟨23310795243394333421798105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540530162262888947865403 23310795243394333421798105)
              ·
                refine ⟨17483096432545750066348579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23310795243394333421798105 17483096432545750066348579)
                ·
                  refine ⟨26224644648818625099522869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17483096432545750066348579 26224644648818625099522869)
                  ·
                    refine ⟨2458560435826746103080269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26224644648818625099522869 2458560435826746103080269)
                    ·
                      refine ⟨921960163435029788655101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2458560435826746103080269 921960163435029788655101)
                      ·
                        rfl

theorem cell23_1795511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1795511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795511 prefixEnd_1795511 := by exact prefixLift 1795511
  have htrace : WordTrace (prefixWord ++ tailWord_1795511) baseStart_1795511 baseEnd_1795511 := by
    simpa [prefixWord, tailWord_1795511, baseEnd_1795511] using wordTrace_append hprefix tailTrace_1795511
  have hstable : (prefixWord ++ tailWord_1795511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795511).length < 2 ^ (prefixWord ++ tailWord_1795511).sum := by decide
  have hdescent : baseEnd_1795511 < baseStart_1795511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795516 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1795516 : Nat := 118140960795 + 1795516 * 2 ^ 59
def prefixEnd_1795516 : Nat := 4983230072969 + 3 ^ 40 * 1795516 * 2
def baseEnd_1795516 : Nat := 921962730838302269092579

theorem tailTrace_1795516 : CollatzResearch.WordTrace tailWord_1795516 prefixEnd_1795516 921962730838302269092579 := by
  unfold tailWord_1795516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32743924281579828282139201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43658565708773104376185601 32743924281579828282139201)
  ·
    refine ⟨24557943211184871211604401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32743924281579828282139201 24557943211184871211604401)
    ·
      refine ⟨18418457408388653408703301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24557943211184871211604401 18418457408388653408703301)
      ·
        refine ⟨3453460764072872514131869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18418457408388653408703301 3453460764072872514131869)
        ·
          refine ⟨1295047786527327192799451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3453460764072872514131869 1295047786527327192799451)
          ·
            refine ⟨1942571679790990789199177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295047786527327192799451 1942571679790990789199177)
            ·
              refine ⟨1456928759843243091899383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942571679790990789199177 1456928759843243091899383)
              ·
                refine ⟨2185393139764864637849075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456928759843243091899383 2185393139764864637849075)
                ·
                  refine ⟨3278089709647296956773613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185393139764864637849075 3278089709647296956773613)
                  ·
                    refine ⟨1229283641117736358790105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278089709647296956773613 1229283641117736358790105)
                    ·
                      refine ⟨921962730838302269092579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229283641117736358790105 921962730838302269092579)
                      ·
                        rfl

theorem cell23_1795516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1795516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795516 prefixEnd_1795516 := by exact prefixLift 1795516
  have htrace : WordTrace (prefixWord ++ tailWord_1795516) baseStart_1795516 baseEnd_1795516 := by
    simpa [prefixWord, tailWord_1795516, baseEnd_1795516] using wordTrace_append hprefix tailTrace_1795516
  have hstable : (prefixWord ++ tailWord_1795516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795516).length < 2 ^ (prefixWord ++ tailWord_1795516).sum := by decide
  have hdescent : baseEnd_1795516 < baseStart_1795516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795531 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 2, 5]
def baseStart_1795531 : Nat := 118140960795 + 1795531 * 2 ^ 59
def prefixEnd_1795531 : Nat := 4983230072969 + 3 ^ 40 * 1795531 * 2
def baseEnd_1795531 : Nat := 307323477682706570135003

theorem tailTrace_1795531 : CollatzResearch.WordTrace tailWord_1795531 prefixEnd_1795531 307323477682706570135003 := by
  unfold tailWord_1795531
  simp only [CollatzResearch.WordTrace]
  refine ⟨65488395658105314126074447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43658930438736876084049631 65488395658105314126074447)
  ·
    refine ⟨98232593487157971189111671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65488395658105314126074447 98232593487157971189111671)
    ·
      refine ⟨147348890230736956783667507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98232593487157971189111671 147348890230736956783667507)
      ·
        refine ⟨221023335346105435175501261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147348890230736956783667507 221023335346105435175501261)
        ·
          refine ⟨82883750754789538190812973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221023335346105435175501261 82883750754789538190812973)
          ·
            refine ⟨31081406533046076821554865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82883750754789538190812973 31081406533046076821554865)
            ·
              refine ⟨23311054899784557616166149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31081406533046076821554865 23311054899784557616166149)
              ·
                refine ⟨4370822793709604553031153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23311054899784557616166149 4370822793709604553031153)
                ·
                  refine ⟨3278117095282203414773365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370822793709604553031153 3278117095282203414773365)
                  ·
                    refine ⟨307323477682706570135003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3278117095282203414773365 307323477682706570135003)
                    ·
                      rfl

theorem cell23_1795531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 5].length) (baseStart_1795531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795531 prefixEnd_1795531 := by exact prefixLift 1795531
  have htrace : WordTrace (prefixWord ++ tailWord_1795531) baseStart_1795531 baseEnd_1795531 := by
    simpa [prefixWord, tailWord_1795531, baseEnd_1795531] using wordTrace_append hprefix tailTrace_1795531
  have hstable : (prefixWord ++ tailWord_1795531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795531).length < 2 ^ (prefixWord ++ tailWord_1795531).sum := by decide
  have hdescent : baseEnd_1795531 < baseStart_1795531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795541 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1795541 : Nat := 118140960795 + 1795541 * 2 ^ 59
def prefixEnd_1795541 : Nat := 4983230072969 + 3 ^ 40 * 1795541 * 2
def baseEnd_1795541 : Nat := 921975567854664671279963

theorem tailTrace_1795541 : CollatzResearch.WordTrace tailWord_1795541 prefixEnd_1795541 921975567854664671279963 := by
  unfold tailWord_1795541
  simp only [CollatzResearch.WordTrace]
  refine ⟨65488760388069085833938477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43659173592046057222625651 65488760388069085833938477)
  ·
    refine ⟨24558285145525907187726929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65488760388069085833938477 24558285145525907187726929)
    ·
      refine ⟨18418713859144430390795197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24558285145525907187726929 18418713859144430390795197)
      ·
        refine ⟨6907017697179161396548199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18418713859144430390795197 6907017697179161396548199)
        ·
          refine ⟨10360526545768742094822299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907017697179161396548199 10360526545768742094822299)
          ·
            refine ⟨15540789818653113142233449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360526545768742094822299 15540789818653113142233449)
            ·
              refine ⟨11655592363989834856675087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15540789818653113142233449 11655592363989834856675087)
              ·
                refine ⟨17483388545984752285012631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655592363989834856675087 17483388545984752285012631)
                ·
                  refine ⟨26225082818977128427518947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17483388545984752285012631 26225082818977128427518947)
                  ·
                    refine ⟨39337624228465692641278421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26225082818977128427518947 39337624228465692641278421)
                    ·
                      refine ⟨921975567854664671279963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39337624228465692641278421 921975567854664671279963)
                      ·
                        rfl

theorem cell23_1795541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1795541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795541 prefixEnd_1795541 := by exact prefixLift 1795541
  have htrace : WordTrace (prefixWord ++ tailWord_1795541) baseStart_1795541 baseEnd_1795541 := by
    simpa [prefixWord, tailWord_1795541, baseEnd_1795541] using wordTrace_append hprefix tailTrace_1795541
  have hstable : (prefixWord ++ tailWord_1795541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795541).length < 2 ^ (prefixWord ++ tailWord_1795541).sum := by decide
  have hdescent : baseEnd_1795541 < baseStart_1795541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795551 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1795551 : Nat := 118140960795 + 1795551 * 2 ^ 59
def prefixEnd_1795551 : Nat := 4983230072969 + 3 ^ 40 * 1795551 * 2
def baseEnd_1795551 : Nat := 921980702661209632154917

theorem tailTrace_1795551 : CollatzResearch.WordTrace tailWord_1795551 prefixEnd_1795551 921980702661209632154917 := by
  unfold tailWord_1795551
  simp only [CollatzResearch.WordTrace]
  refine ⟨65489125118032857541802507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43659416745355238361201671 65489125118032857541802507)
  ·
    refine ⟨98233687677049286312703761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65489125118032857541802507 98233687677049286312703761)
    ·
      refine ⟨73675265757786964734527821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98233687677049286312703761 73675265757786964734527821)
      ·
        refine ⟨27628224659170111775447933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73675265757786964734527821 27628224659170111775447933)
        ·
          refine ⟨10360584247188791915792975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27628224659170111775447933 10360584247188791915792975)
          ·
            refine ⟨15540876370783187873689463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360584247188791915792975 15540876370783187873689463)
            ·
              refine ⟨23311314556174781810534195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540876370783187873689463 23311314556174781810534195)
              ·
                refine ⟨34966971834262172715801293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23311314556174781810534195 34966971834262172715801293)
                ·
                  refine ⟨13112614437848314768425485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34966971834262172715801293 13112614437848314768425485)
                  ·
                    refine ⟨4917230414193118038159557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13112614437848314768425485 4917230414193118038159557)
                    ·
                      refine ⟨921980702661209632154917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4917230414193118038159557 921980702661209632154917)
                      ·
                        rfl

theorem cell23_1795551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1795551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795551 prefixEnd_1795551 := by exact prefixLift 1795551
  have htrace : WordTrace (prefixWord ++ tailWord_1795551) baseStart_1795551 baseEnd_1795551 := by
    simpa [prefixWord, tailWord_1795551, baseEnd_1795551] using wordTrace_append hprefix tailTrace_1795551
  have hstable : (prefixWord ++ tailWord_1795551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795551).length < 2 ^ (prefixWord ++ tailWord_1795551).sum := by decide
  have hdescent : baseEnd_1795551 < baseStart_1795551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795582 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1795582 : Nat := 118140960795 + 1795582 * 2 ^ 59
def prefixEnd_1795582 : Nat := 4983230072969 + 3 ^ 40 * 1795582 * 2
def baseEnd_1795582 : Nat := 307332206853833003622425

theorem tailTrace_1795582 : CollatzResearch.WordTrace tailWord_1795582 prefixEnd_1795582 307332206853833003622425 := by
  unfold tailWord_1795582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186281972615068729522625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43660170520613699890787333 8186281972615068729522625)
  ·
    refine ⟨6139711479461301547141969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8186281972615068729522625 6139711479461301547141969)
    ·
      refine ⟨4604783609595976160356477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6139711479461301547141969 4604783609595976160356477)
      ·
        refine ⟨1726793853598491060133679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4604783609595976160356477 1726793853598491060133679)
        ·
          refine ⟨2590190780397736590200519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726793853598491060133679 2590190780397736590200519)
          ·
            refine ⟨3885286170596604885300779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590190780397736590200519 3885286170596604885300779)
            ·
              refine ⟨5827929255894907327951169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885286170596604885300779 5827929255894907327951169)
              ·
                refine ⟨4370946941921180495963377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5827929255894907327951169 4370946941921180495963377)
                ·
                  refine ⟨3278210206440885371972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370946941921180495963377 3278210206440885371972533)
                  ·
                    refine ⟨307332206853833003622425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3278210206440885371972533 307332206853833003622425)
                    ·
                      rfl

theorem cell23_1795582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1795582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795582 prefixEnd_1795582 := by exact prefixLift 1795582
  have htrace : WordTrace (prefixWord ++ tailWord_1795582) baseStart_1795582 baseEnd_1795582 := by
    simpa [prefixWord, tailWord_1795582, baseEnd_1795582] using wordTrace_append hprefix tailTrace_1795582
  have hstable : (prefixWord ++ tailWord_1795582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795582).length < 2 ^ (prefixWord ++ tailWord_1795582).sum := by decide
  have hdescent : baseEnd_1795582 < baseStart_1795582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795585 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1795585 : Nat := 118140960795 + 1795585 * 2 ^ 59
def prefixEnd_1795585 : Nat := 4983230072969 + 3 ^ 40 * 1795585 * 2
def baseEnd_1795585 : Nat := 921998161003462499129761

theorem tailTrace_1795585 : CollatzResearch.WordTrace tailWord_1795585 prefixEnd_1795585 921998161003462499129761 := by
  unfold tailWord_1795585
  simp only [CollatzResearch.WordTrace]
  refine ⟨65490365199909681348540209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43660243466606454232360139 65490365199909681348540209)
  ·
    refine ⟨49117773899932261011405157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65490365199909681348540209 49117773899932261011405157)
    ·
      refine ⟨9209582606237298939638467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49117773899932261011405157 9209582606237298939638467)
      ·
        refine ⟨13814373909355948409457701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209582606237298939638467 13814373909355948409457701)
        ·
          refine ⟨2590195108004240326773319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13814373909355948409457701 2590195108004240326773319)
          ·
            refine ⟨3885292662006360490159979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590195108004240326773319 3885292662006360490159979)
            ·
              refine ⟨5827938993009540735239969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885292662006360490159979 5827938993009540735239969)
              ·
                refine ⟨4370954244757155551429977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5827938993009540735239969 4370954244757155551429977)
                ·
                  refine ⟨3278215683567866663572483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4370954244757155551429977 3278215683567866663572483)
                  ·
                    refine ⟨4917323525351799995358725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278215683567866663572483 4917323525351799995358725)
                    ·
                      refine ⟨921998161003462499129761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4917323525351799995358725 921998161003462499129761)
                      ·
                        rfl

theorem cell23_1795585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1795585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795585 prefixEnd_1795585 := by exact prefixLift 1795585
  have htrace : WordTrace (prefixWord ++ tailWord_1795585) baseStart_1795585 baseEnd_1795585 := by
    simpa [prefixWord, tailWord_1795585, baseEnd_1795585] using wordTrace_append hprefix tailTrace_1795585
  have hstable : (prefixWord ++ tailWord_1795585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795585).length < 2 ^ (prefixWord ++ tailWord_1795585).sum := by decide
  have hdescent : baseEnd_1795585 < baseStart_1795585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795618 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1795618 : Nat := 118140960795 + 1795618 * 2 ^ 59
def prefixEnd_1795618 : Nat := 4983230072969 + 3 ^ 40 * 1795618 * 2
def baseEnd_1795618 : Nat := 922015105865060870017109

theorem tailTrace_1795618 : CollatzResearch.WordTrace tailWord_1795618 prefixEnd_1795618 922015105865060870017109 := by
  unfold tailWord_1795618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372892202197531996122877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43661045872526751989661005 16372892202197531996122877)
  ·
    refine ⟨6139834575824074498546079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16372892202197531996122877 6139834575824074498546079)
    ·
      refine ⟨9209751863736111747819119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6139834575824074498546079 9209751863736111747819119)
      ·
        refine ⟨13814627795604167621728679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209751863736111747819119 13814627795604167621728679)
        ·
          refine ⟨20721941693406251432593019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13814627795604167621728679 20721941693406251432593019)
          ·
            refine ⟨31082912540109377148889529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20721941693406251432593019 31082912540109377148889529)
            ·
              refine ⟨23312184405082032861667147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31082912540109377148889529 23312184405082032861667147)
              ·
                refine ⟨34968276607623049292500721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23312184405082032861667147 34968276607623049292500721)
                ·
                  refine ⟨26226207455717286969375541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34968276607623049292500721 26226207455717286969375541)
                  ·
                    refine ⟨2458706948973495653378957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26226207455717286969375541 2458706948973495653378957)
                    ·
                      refine ⟨922015105865060870017109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2458706948973495653378957 922015105865060870017109)
                      ·
                        rfl

theorem cell23_1795618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1795618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795618 prefixEnd_1795618 := by exact prefixLift 1795618
  have htrace : WordTrace (prefixWord ++ tailWord_1795618) baseStart_1795618 baseEnd_1795618 := by
    simpa [prefixWord, tailWord_1795618, baseEnd_1795618] using wordTrace_append hprefix tailTrace_1795618
  have hstable : (prefixWord ++ tailWord_1795618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795618).length < 2 ^ (prefixWord ++ tailWord_1795618).sum := by decide
  have hdescent : baseEnd_1795618 < baseStart_1795618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795658 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1795658 : Nat := 118140960795 + 1795658 * 2 ^ 59
def prefixEnd_1795658 : Nat := 4983230072969 + 3 ^ 40 * 1795658 * 2
def baseEnd_1795658 : Nat := 922035645091240713516925

theorem tailTrace_1795658 : CollatzResearch.WordTrace tailWord_1795658 prefixEnd_1795658 922035645091240713516925 := by
  unfold tailWord_1795658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373256932161303703986907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43662018485763476543965085 16373256932161303703986907)
  ·
    refine ⟨24559885398241955555980361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16373256932161303703986907 24559885398241955555980361)
    ·
      refine ⟨18419914048681466666985271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24559885398241955555980361 18419914048681466666985271)
      ·
        refine ⟨27629871073022200000477907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18419914048681466666985271 27629871073022200000477907)
        ·
          refine ⟨41444806609533300000716861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27629871073022200000477907 41444806609533300000716861)
          ·
            refine ⟨15541802478574987500268823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41444806609533300000716861 15541802478574987500268823)
            ·
              refine ⟨23312703717862481250403235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15541802478574987500268823 23312703717862481250403235)
              ·
                refine ⟨34969055576793721875604853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23312703717862481250403235 34969055576793721875604853)
                ·
                  refine ⟨3278348960324411425837955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34969055576793721875604853 3278348960324411425837955)
                  ·
                    refine ⟨4917523440486617138756933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278348960324411425837955 4917523440486617138756933)
                    ·
                      refine ⟨922035645091240713516925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4917523440486617138756933 922035645091240713516925)
                      ·
                        rfl

theorem cell23_1795658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1795658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795658 prefixEnd_1795658 := by exact prefixLift 1795658
  have htrace : WordTrace (prefixWord ++ tailWord_1795658) baseStart_1795658 baseEnd_1795658 := by
    simpa [prefixWord, tailWord_1795658, baseEnd_1795658] using wordTrace_append hprefix tailTrace_1795658
  have hstable : (prefixWord ++ tailWord_1795658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795658).length < 2 ^ (prefixWord ++ tailWord_1795658).sum := by decide
  have hdescent : baseEnd_1795658 < baseStart_1795658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795691 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_1795691 : Nat := 118140960795 + 1795691 * 2 ^ 59
def prefixEnd_1795691 : Nat := 4983230072969 + 3 ^ 40 * 1795691 * 2
def baseEnd_1795691 : Nat := 922052589952839084404273

theorem tailTrace_1795691 : CollatzResearch.WordTrace tailWord_1795691 prefixEnd_1795691 922052589952839084404273 := by
  unfold tailWord_1795691
  simp only [CollatzResearch.WordTrace]
  refine ⟨65494231337525661451898927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43662820891683774301265951 65494231337525661451898927)
  ·
    refine ⟨98241347006288492177848391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65494231337525661451898927 98241347006288492177848391)
    ·
      refine ⟨147362020509432738266772587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98241347006288492177848391 147362020509432738266772587)
      ·
        refine ⟨221043030764149107400158881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147362020509432738266772587 221043030764149107400158881)
        ·
          refine ⟨165782273073111830550119161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221043030764149107400158881 165782273073111830550119161)
          ·
            refine ⟨124336704804833872912589371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165782273073111830550119161 124336704804833872912589371)
            ·
              refine ⟨186505057207250809368884057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124336704804833872912589371 186505057207250809368884057)
              ·
                refine ⟨139878792905438107026663043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186505057207250809368884057 139878792905438107026663043)
                ·
                  refine ⟨209818189358157160539994565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139878792905438107026663043 209818189358157160539994565)
                  ·
                    refine ⟨39340910504654467601248981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209818189358157160539994565 39340910504654467601248981)
                    ·
                      refine ⟨922052589952839084404273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39340910504654467601248981 922052589952839084404273)
                      ·
                        rfl

theorem cell23_1795691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_1795691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795691 prefixEnd_1795691 := by exact prefixLift 1795691
  have htrace : WordTrace (prefixWord ++ tailWord_1795691) baseStart_1795691 baseEnd_1795691 := by
    simpa [prefixWord, tailWord_1795691, baseEnd_1795691] using wordTrace_append hprefix tailTrace_1795691
  have hstable : (prefixWord ++ tailWord_1795691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795691).length < 2 ^ (prefixWord ++ tailWord_1795691).sum := by decide
  have hdescent : baseEnd_1795691 < baseStart_1795691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795698 : List Nat := [3, 2, 1, 2, 3, 2, 10]
def baseStart_1795698 : Nat := 118140960795 + 1795698 * 2 ^ 59
def prefixEnd_1795698 : Nat := 4983230072969 + 3 ^ 40 * 1795698 * 2
def baseEnd_1795698 : Nat := 11383409682931117987861

theorem tailTrace_1795698 : CollatzResearch.WordTrace tailWord_1795698 prefixEnd_1795698 11383409682931117987861 := by
  unfold tailWord_1795698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373621662125075411850937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43662991099000201098269165 16373621662125075411850937)
  ·
    refine ⟨12280216246593806558888203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16373621662125075411850937 12280216246593806558888203)
    ·
      refine ⟨18420324369890709838332305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12280216246593806558888203 18420324369890709838332305)
      ·
        refine ⟨13815243277418032378749229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18420324369890709838332305 13815243277418032378749229)
        ·
          refine ⟨5180716229031762142030961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13815243277418032378749229 5180716229031762142030961)
          ·
            refine ⟨3885537171773821606523221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180716229031762142030961 3885537171773821606523221)
            ·
              refine ⟨11383409682931117987861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3885537171773821606523221 11383409682931117987861)
              ·
                rfl

theorem cell23_1795698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 10].length) (baseStart_1795698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795698 prefixEnd_1795698 := by exact prefixLift 1795698
  have htrace : WordTrace (prefixWord ++ tailWord_1795698) baseStart_1795698 baseEnd_1795698 := by
    simpa [prefixWord, tailWord_1795698, baseEnd_1795698] using wordTrace_append hprefix tailTrace_1795698
  have hstable : (prefixWord ++ tailWord_1795698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795698).length < 2 ^ (prefixWord ++ tailWord_1795698).sum := by decide
  have hdescent : baseEnd_1795698 < baseStart_1795698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795702 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1795702 : Nat := 118140960795 + 1795702 * 2 ^ 59
def prefixEnd_1795702 : Nat := 4983230072969 + 3 ^ 40 * 1795702 * 2
def baseEnd_1795702 : Nat := 307352746080012847122241

theorem tailTrace_1795702 : CollatzResearch.WordTrace tailWord_1795702 prefixEnd_1795702 307352746080012847122241 := by
  unfold tailWord_1795702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093414533780363145659335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43663088360323873553699573 4093414533780363145659335)
  ·
    refine ⟨6140121800670544718489003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4093414533780363145659335 6140121800670544718489003)
    ·
      refine ⟨9210182701005817077733505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6140121800670544718489003 9210182701005817077733505)
      ·
        refine ⟨6907637025754362808300129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9210182701005817077733505 6907637025754362808300129)
        ·
          refine ⟨5180727769315772106225097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6907637025754362808300129 5180727769315772106225097)
          ·
            refine ⟨3885545826986829079668823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180727769315772106225097 3885545826986829079668823)
            ·
              refine ⟨5828318740480243619503235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885545826986829079668823 5828318740480243619503235)
              ·
                refine ⟨8742478110720365429254853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828318740480243619503235 8742478110720365429254853)
                ·
                  refine ⟨1639214645760068517985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8742478110720365429254853 1639214645760068517985285)
                  ·
                    refine ⟨307352746080012847122241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639214645760068517985285 307352746080012847122241)
                    ·
                      rfl

theorem cell23_1795702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1795702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795702 prefixEnd_1795702 := by exact prefixLift 1795702
  have htrace : WordTrace (prefixWord ++ tailWord_1795702) baseStart_1795702 baseEnd_1795702 := by
    simpa [prefixWord, tailWord_1795702, baseEnd_1795702] using wordTrace_append hprefix tailTrace_1795702
  have hstable : (prefixWord ++ tailWord_1795702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795702).length < 2 ^ (prefixWord ++ tailWord_1795702).sum := by decide
  have hdescent : baseEnd_1795702 < baseStart_1795702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795709 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_1795709 : Nat := 118140960795 + 1795709 * 2 ^ 59
def prefixEnd_1795709 : Nat := 4983230072969 + 3 ^ 40 * 1795709 * 2
def baseEnd_1795709 : Nat := 922061832604620013979191

theorem tailTrace_1795709 : CollatzResearch.WordTrace tailWord_1795709 prefixEnd_1795709 922061832604620013979191 := by
  unfold tailWord_1795709
  simp only [CollatzResearch.WordTrace]
  refine ⟨65494887851460450526054181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43663258567640300350702787 65494887851460450526054181)
  ·
    refine ⟨12280291472148834473635159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65494887851460450526054181 12280291472148834473635159)
    ·
      refine ⟨18420437208223251710452739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12280291472148834473635159 18420437208223251710452739)
      ·
        refine ⟨27630655812334877565679109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18420437208223251710452739 27630655812334877565679109)
        ·
          refine ⟨5180747964812789543564833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27630655812334877565679109 5180747964812789543564833)
          ·
            refine ⟨3885560973609592157673625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180747964812789543564833 3885560973609592157673625)
            ·
              refine ⟨2914170730207194118255219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885560973609592157673625 2914170730207194118255219)
              ·
                refine ⟨4371256095310791177382829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914170730207194118255219 4371256095310791177382829)
                ·
                  refine ⟨1639221035741546691518561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4371256095310791177382829 1639221035741546691518561)
                  ·
                    refine ⟨1229415776806160018638921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1639221035741546691518561 1229415776806160018638921)
                    ·
                      refine ⟨922061832604620013979191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229415776806160018638921 922061832604620013979191)
                      ·
                        rfl

theorem cell23_1795709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_1795709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795709 prefixEnd_1795709 := by exact prefixLift 1795709
  have htrace : WordTrace (prefixWord ++ tailWord_1795709) baseStart_1795709 baseEnd_1795709 := by
    simpa [prefixWord, tailWord_1795709, baseEnd_1795709] using wordTrace_append hprefix tailTrace_1795709
  have hstable : (prefixWord ++ tailWord_1795709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795709).length < 2 ^ (prefixWord ++ tailWord_1795709).sum := by decide
  have hdescent : baseEnd_1795709 < baseStart_1795709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795722 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1795722 : Nat := 118140960795 + 1795722 * 2 ^ 59
def prefixEnd_1795722 : Nat := 4983230072969 + 3 ^ 40 * 1795722 * 2
def baseEnd_1795722 : Nat := 922068507853128463116631

theorem tailTrace_1795722 : CollatzResearch.WordTrace tailWord_1795722 prefixEnd_1795722 922068507853128463116631 := by
  unfold tailWord_1795722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373840500103338436569355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43663574666942235830851613 16373840500103338436569355)
  ·
    refine ⟨24560760750155007654854033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16373840500103338436569355 24560760750155007654854033)
    ·
      refine ⟨18420570562616255741140525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24560760750155007654854033 18420570562616255741140525)
      ·
        refine ⟨6907713960981095902927697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18420570562616255741140525 6907713960981095902927697)
        ·
          refine ⟨5180785470735821927195773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6907713960981095902927697 5180785470735821927195773)
          ·
            refine ⟨1942794551525933222698415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5180785470735821927195773 1942794551525933222698415)
            ·
              refine ⟨2914191827288899834047623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942794551525933222698415 2914191827288899834047623)
              ·
                refine ⟨4371287740933349751071435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914191827288899834047623 4371287740933349751071435)
                ·
                  refine ⟨6556931611400024626607153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371287740933349751071435 6556931611400024626607153)
                  ·
                    refine ⟨4917698708550018469955365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6556931611400024626607153 4917698708550018469955365)
                    ·
                      refine ⟨922068507853128463116631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4917698708550018469955365 922068507853128463116631)
                      ·
                        rfl

theorem cell23_1795722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1795722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795722 prefixEnd_1795722 := by exact prefixLift 1795722
  have htrace : WordTrace (prefixWord ++ tailWord_1795722) baseStart_1795722 baseEnd_1795722 := by
    simpa [prefixWord, tailWord_1795722, baseEnd_1795722] using wordTrace_append hprefix tailTrace_1795722
  have hstable : (prefixWord ++ tailWord_1795722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795722).length < 2 ^ (prefixWord ++ tailWord_1795722).sum := by decide
  have hdescent : baseEnd_1795722 < baseStart_1795722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795786 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_1795786 : Nat := 118140960795 + 1795786 * 2 ^ 59
def prefixEnd_1795786 : Nat := 4983230072969 + 3 ^ 40 * 1795786 * 2
def baseEnd_1795786 : Nat := 922101370615016212716337

theorem tailTrace_1795786 : CollatzResearch.WordTrace tailWord_1795786 prefixEnd_1795786 922101370615016212716337 := by
  unfold tailWord_1795786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16374424068045373169151803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43665130848120995117738141 16374424068045373169151803)
  ·
    refine ⟨24561636102068059753727705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16374424068045373169151803 24561636102068059753727705)
    ·
      refine ⟨18421227076551044815295779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24561636102068059753727705 18421227076551044815295779)
      ·
        refine ⟨27631840614826567222943669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18421227076551044815295779 27631840614826567222943669)
        ·
          refine ⟨2590485057639990677150969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27631840614826567222943669 2590485057639990677150969)
          ·
            refine ⟨1942863793229993007863227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2590485057639990677150969 1942863793229993007863227)
            ·
              refine ⟨2914295689844989511794841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942863793229993007863227 2914295689844989511794841)
              ·
                refine ⟨2185721767383742133846131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914295689844989511794841 2185721767383742133846131)
                ·
                  refine ⟨3278582651075613200769197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185721767383742133846131 3278582651075613200769197)
                  ·
                    refine ⟨1229468494153354950288449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278582651075613200769197 1229468494153354950288449)
                    ·
                      refine ⟨922101370615016212716337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229468494153354950288449 922101370615016212716337)
                      ·
                        rfl

theorem cell23_1795786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_1795786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795786 prefixEnd_1795786 := by exact prefixLift 1795786
  have htrace : WordTrace (prefixWord ++ tailWord_1795786) baseStart_1795786 baseEnd_1795786 := by
    simpa [prefixWord, tailWord_1795786, baseEnd_1795786] using wordTrace_append hprefix tailTrace_1795786
  have hstable : (prefixWord ++ tailWord_1795786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795786).length < 2 ^ (prefixWord ++ tailWord_1795786).sum := by decide
  have hdescent : baseEnd_1795786 < baseStart_1795786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795816 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1795816 : Nat := 118140960795 + 1795816 * 2 ^ 59
def prefixEnd_1795816 : Nat := 4983230072969 + 3 ^ 40 * 1795816 * 2
def baseEnd_1795816 : Nat := 922116775034651095341199

theorem tailTrace_1795816 : CollatzResearch.WordTrace tailWord_1795816 prefixEnd_1795816 922116775034651095341199 := by
  unfold tailWord_1795816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32749395231036403900099651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43665860308048538533466201 32749395231036403900099651)
  ·
    refine ⟨49124092846554605850149477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32749395231036403900099651 49124092846554605850149477)
    ·
      refine ⟨9210767408728988596903027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49124092846554605850149477 9210767408728988596903027)
      ·
        refine ⟨13816151113093482895354541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9210767408728988596903027 13816151113093482895354541)
        ·
          refine ⟨5181056667410056085757953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13816151113093482895354541 5181056667410056085757953)
          ·
            refine ⟨3885792500557542064318465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181056667410056085757953 3885792500557542064318465)
            ·
              refine ⟨2914344375418156548238849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885792500557542064318465 2914344375418156548238849)
              ·
                refine ⟨2185758281563617411179137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914344375418156548238849 2185758281563617411179137)
                ·
                  refine ⟨1639318711172713058384353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2185758281563617411179137 1639318711172713058384353)
                  ·
                    refine ⟨1229489033379534793788265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1639318711172713058384353 1229489033379534793788265)
                    ·
                      refine ⟨922116775034651095341199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229489033379534793788265 922116775034651095341199)
                      ·
                        rfl

theorem cell23_1795816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1795816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795816 prefixEnd_1795816 := by exact prefixLift 1795816
  have htrace : WordTrace (prefixWord ++ tailWord_1795816) baseStart_1795816 baseEnd_1795816 := by
    simpa [prefixWord, tailWord_1795816, baseEnd_1795816] using wordTrace_append hprefix tailTrace_1795816
  have hstable : (prefixWord ++ tailWord_1795816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795816).length < 2 ^ (prefixWord ++ tailWord_1795816).sum := by decide
  have hdescent : baseEnd_1795816 < baseStart_1795816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795822 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_1795822 : Nat := 118140960795 + 1795822 * 2 ^ 59
def prefixEnd_1795822 : Nat := 4983230072969 + 3 ^ 40 * 1795822 * 2
def baseEnd_1795822 : Nat := 102457761768730896874019

theorem tailTrace_1795822 : CollatzResearch.WordTrace tailWord_1795822 prefixEnd_1795822 102457761768730896874019 := by
  unfold tailWord_1795822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187376162506383853114715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43666006200034047216611813 8187376162506383853114715)
  ·
    refine ⟨12281064243759575779672073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8187376162506383853114715 12281064243759575779672073)
    ·
      refine ⟨9210798182819681834754055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12281064243759575779672073 9210798182819681834754055)
      ·
        refine ⟨13816197274229522752131083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9210798182819681834754055 13816197274229522752131083)
        ·
          refine ⟨20724295911344284128196625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816197274229522752131083 20724295911344284128196625)
          ·
            refine ⟨15543221933508213096147469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20724295911344284128196625 15543221933508213096147469)
            ·
              refine ⟨5828708225065579911055301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15543221933508213096147469 5828708225065579911055301)
              ·
                refine ⟨1092882792199796233322869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5828708225065579911055301 1092882792199796233322869)
                ·
                  refine ⟨102457761768730896874019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092882792199796233322869 102457761768730896874019)
                  ·
                    rfl

theorem cell23_1795822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_1795822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795822 prefixEnd_1795822 := by exact prefixLift 1795822
  have htrace : WordTrace (prefixWord ++ tailWord_1795822) baseStart_1795822 baseEnd_1795822 := by
    simpa [prefixWord, tailWord_1795822, baseEnd_1795822] using wordTrace_append hprefix tailTrace_1795822
  have hstable : (prefixWord ++ tailWord_1795822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795822).length < 2 ^ (prefixWord ++ tailWord_1795822).sum := by decide
  have hdescent : baseEnd_1795822 < baseStart_1795822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795855 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_1795855 : Nat := 118140960795 + 1795855 * 2 ^ 59
def prefixEnd_1795855 : Nat := 4983230072969 + 3 ^ 40 * 1795855 * 2
def baseEnd_1795855 : Nat := 922136800780176442753519

theorem tailTrace_1795855 : CollatzResearch.WordTrace tailWord_1795855 prefixEnd_1795855 922136800780176442753519 := by
  unfold tailWord_1795855
  simp only [CollatzResearch.WordTrace]
  refine ⟨65500212908931517460869019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43666808605954344973912679 65500212908931517460869019)
  ·
    refine ⟨98250319363397276191303529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65500212908931517460869019 98250319363397276191303529)
    ·
      refine ⟨73687739522547957143477647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98250319363397276191303529 73687739522547957143477647)
      ·
        refine ⟨110531609283821935715216471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73687739522547957143477647 110531609283821935715216471)
        ·
          refine ⟨165797413925732903572824707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110531609283821935715216471 165797413925732903572824707)
          ·
            refine ⟨248696120888599355359237061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165797413925732903572824707 248696120888599355359237061)
            ·
              refine ⟨46630522666612379129856949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248696120888599355359237061 46630522666612379129856949)
              ·
                refine ⟨4371611499994910543424089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46630522666612379129856949 4371611499994910543424089)
                ·
                  refine ⟨3278708624996182907568067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371611499994910543424089 3278708624996182907568067)
                  ·
                    refine ⟨4918062937494274361352101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278708624996182907568067 4918062937494274361352101)
                    ·
                      refine ⟨922136800780176442753519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4918062937494274361352101 922136800780176442753519)
                      ·
                        rfl

theorem cell23_1795855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_1795855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795855 prefixEnd_1795855 := by exact prefixLift 1795855
  have htrace : WordTrace (prefixWord ++ tailWord_1795855) baseStart_1795855 baseEnd_1795855 := by
    simpa [prefixWord, tailWord_1795855, baseEnd_1795855] using wordTrace_append hprefix tailTrace_1795855
  have hstable : (prefixWord ++ tailWord_1795855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795855).length < 2 ^ (prefixWord ++ tailWord_1795855).sum := by decide
  have hdescent : baseEnd_1795855 < baseStart_1795855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795872 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1795872 : Nat := 118140960795 + 1795872 * 2 ^ 59
def prefixEnd_1795872 : Nat := 4983230072969 + 3 ^ 40 * 1795872 * 2
def baseEnd_1795872 : Nat := 922145529951302876240941

theorem tailTrace_1795872 : CollatzResearch.WordTrace tailWord_1795872 prefixEnd_1795872 922145529951302876240941 := by
  unfold tailWord_1795872
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750416474934964682118935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43667221966579952909491913 32750416474934964682118935)
  ·
    refine ⟨49125624712402447023178403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32750416474934964682118935 49125624712402447023178403)
    ·
      refine ⟨73688437068603670534767605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49125624712402447023178403 73688437068603670534767605)
      ·
        refine ⟨6908290975181594112634463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73688437068603670534767605 6908290975181594112634463)
        ·
          refine ⟨10362436462772391168951695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908290975181594112634463 10362436462772391168951695)
          ·
            refine ⟨15543654694158586753427543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362436462772391168951695 15543654694158586753427543)
            ·
              refine ⟨23315482041237880130141315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15543654694158586753427543 23315482041237880130141315)
              ·
                refine ⟨34973223061856820195211973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23315482041237880130141315 34973223061856820195211973)
                ·
                  refine ⟨6557479324098153786602245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34973223061856820195211973 6557479324098153786602245)
                  ·
                    refine ⟨1229527373268403834987921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557479324098153786602245 1229527373268403834987921)
                    ·
                      refine ⟨922145529951302876240941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229527373268403834987921 922145529951302876240941)
                      ·
                        rfl

theorem cell23_1795872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1795872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795872 prefixEnd_1795872 := by exact prefixLift 1795872
  have htrace : WordTrace (prefixWord ++ tailWord_1795872) baseStart_1795872 baseEnd_1795872 := by
    simpa [prefixWord, tailWord_1795872, baseEnd_1795872] using wordTrace_append hprefix tailTrace_1795872
  have hstable : (prefixWord ++ tailWord_1795872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795872).length < 2 ^ (prefixWord ++ tailWord_1795872).sum := by decide
  have hdescent : baseEnd_1795872 < baseStart_1795872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795955 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 1, 6]
def baseStart_1795955 : Nat := 118140960795 + 1795955 * 2 ^ 59
def prefixEnd_1795955 : Nat := 4983230072969 + 3 ^ 40 * 1795955 * 2
def baseEnd_1795955 : Nat := 307396049615208683834353

theorem tailTrace_1795955 : CollatzResearch.WordTrace tailWord_1795955 prefixEnd_1795955 307396049615208683834353 := by
  unfold tailWord_1795955
  simp only [CollatzResearch.WordTrace]
  refine ⟨65503860208569234539509319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43669240139046156359672879 65503860208569234539509319)
  ·
    refine ⟨98255790312853851809263979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65503860208569234539509319 98255790312853851809263979)
    ·
      refine ⟨147383685469280777713895969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98255790312853851809263979 147383685469280777713895969)
      ·
        refine ⟨110537764101960583285421977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147383685469280777713895969 110537764101960583285421977)
        ·
          refine ⟨82903323076470437464066483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110537764101960583285421977 82903323076470437464066483)
          ·
            refine ⟨124354984614705656196099725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82903323076470437464066483 124354984614705656196099725)
            ·
              refine ⟨46633119230514621073537397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124354984614705656196099725 46633119230514621073537397)
              ·
                refine ⟨4371854927860745725644131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46633119230514621073537397 4371854927860745725644131)
                ·
                  refine ⟨6557782391791118588466197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371854927860745725644131 6557782391791118588466197)
                  ·
                    refine ⟨307396049615208683834353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6557782391791118588466197 307396049615208683834353)
                    ·
                      rfl

theorem cell23_1795955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 6].length) (baseStart_1795955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795955 prefixEnd_1795955 := by exact prefixLift 1795955
  have htrace : WordTrace (prefixWord ++ tailWord_1795955) baseStart_1795955 baseEnd_1795955 := by
    simpa [prefixWord, tailWord_1795955, baseEnd_1795955] using wordTrace_append hprefix tailTrace_1795955
  have hstable : (prefixWord ++ tailWord_1795955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795955).length < 2 ^ (prefixWord ++ tailWord_1795955).sum := by decide
  have hdescent : baseEnd_1795955 < baseStart_1795955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795962 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_1795962 : Nat := 118140960795 + 1795962 * 2 ^ 59
def prefixEnd_1795962 : Nat := 4983230072969 + 3 ^ 40 * 1795962 * 2
def baseEnd_1795962 : Nat := 922191743210207524115527

theorem tailTrace_1795962 : CollatzResearch.WordTrace tailWord_1795962 prefixEnd_1795962 922191743210207524115527 := by
  unfold tailWord_1795962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376028879885968683753535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43669410346362583156676093 16376028879885968683753535)
  ·
    refine ⟨24564043319828953025630303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16376028879885968683753535 24564043319828953025630303)
    ·
      refine ⟨36846064979743429538445455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24564043319828953025630303 36846064979743429538445455)
      ·
        refine ⟨55269097469615144307668183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36846064979743429538445455 55269097469615144307668183)
        ·
          refine ⟨82903646204422716461502275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55269097469615144307668183 82903646204422716461502275)
          ·
            refine ⟨124355469306634074692253413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82903646204422716461502275 124355469306634074692253413)
            ·
              refine ⟨23316650494993889004797515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124355469306634074692253413 23316650494993889004797515)
              ·
                refine ⟨34974975742490833507196273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23316650494993889004797515 34974975742490833507196273)
                ·
                  refine ⟨26231231806868125130397205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34974975742490833507196273 26231231806868125130397205)
                  ·
                    refine ⟨1229588990946943365487369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26231231806868125130397205 1229588990946943365487369)
                    ·
                      refine ⟨922191743210207524115527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229588990946943365487369 922191743210207524115527)
                      ·
                        rfl

theorem cell23_1795962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_1795962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795962 prefixEnd_1795962 := by exact prefixLift 1795962
  have htrace : WordTrace (prefixWord ++ tailWord_1795962) baseStart_1795962 baseEnd_1795962 := by
    simpa [prefixWord, tailWord_1795962, baseEnd_1795962] using wordTrace_append hprefix tailTrace_1795962
  have hstable : (prefixWord ++ tailWord_1795962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795962).length < 2 ^ (prefixWord ++ tailWord_1795962).sum := by decide
  have hdescent : baseEnd_1795962 < baseStart_1795962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795972 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1795972 : Nat := 118140960795 + 1795972 * 2 ^ 59
def prefixEnd_1795972 : Nat := 4983230072969 + 3 ^ 40 * 1795972 * 2
def baseEnd_1795972 : Nat := 307398959338917494996827

theorem tailTrace_1795972 : CollatzResearch.WordTrace tailWord_1795972 prefixEnd_1795972 307398959338917494996827 := by
  unfold tailWord_1795972
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752240124753823221439085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43669653499671764295252113 32752240124753823221439085)
  ·
    refine ⟨12282090046782683708039657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32752240124753823221439085 12282090046782683708039657)
    ·
      refine ⟨9211567535087012781029743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282090046782683708039657 9211567535087012781029743)
      ·
        refine ⟨13817351302630519171544615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211567535087012781029743 13817351302630519171544615)
        ·
          refine ⟨20726026953945778757316923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817351302630519171544615 20726026953945778757316923)
          ·
            refine ⟨31089040430918668135975385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20726026953945778757316923 31089040430918668135975385)
            ·
              refine ⟨23316780323189001101981539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31089040430918668135975385 23316780323189001101981539)
              ·
                refine ⟨34975170484783501652972309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23316780323189001101981539 34975170484783501652972309)
                ·
                  refine ⟨1639461116474226639983077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34975170484783501652972309 1639461116474226639983077)
                  ·
                    refine ⟨307398959338917494996827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639461116474226639983077 307398959338917494996827)
                    ·
                      rfl

theorem cell23_1795972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1795972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795972 prefixEnd_1795972 := by exact prefixLift 1795972
  have htrace : WordTrace (prefixWord ++ tailWord_1795972) baseStart_1795972 baseEnd_1795972 := by
    simpa [prefixWord, tailWord_1795972, baseEnd_1795972] using wordTrace_append hprefix tailTrace_1795972
  have hstable : (prefixWord ++ tailWord_1795972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795972).length < 2 ^ (prefixWord ++ tailWord_1795972).sum := by decide
  have hdescent : baseEnd_1795972 < baseStart_1795972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795976 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 1, 5]
def baseStart_1795976 : Nat := 118140960795 + 1795976 * 2 ^ 59
def prefixEnd_1795976 : Nat := 4983230072969 + 3 ^ 40 * 1795976 * 2
def baseEnd_1795976 : Nat := 307399643979790156446821

theorem tailTrace_1795976 : CollatzResearch.WordTrace tailWord_1795976 prefixEnd_1795976 307399643979790156446821 := by
  unfold tailWord_1795976
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752313070746577563011891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43669750760995436750682521 32752313070746577563011891)
  ·
    refine ⟨49128469606119866344517837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32752313070746577563011891 49128469606119866344517837)
    ·
      refine ⟨18423176102294949879194189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49128469606119866344517837 18423176102294949879194189)
      ·
        refine ⟨6908691038360606204697821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18423176102294949879194189 6908691038360606204697821)
        ·
          refine ⟨2590759139385227326761683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6908691038360606204697821 2590759139385227326761683)
          ·
            refine ⟨3886138709077840990142525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590759139385227326761683 3886138709077840990142525)
            ·
              refine ⟨1457302015904190371303447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886138709077840990142525 1457302015904190371303447)
              ·
                refine ⟨2185953023856285556955171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457302015904190371303447 2185953023856285556955171)
                ·
                  refine ⟨3278929535784428335432757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185953023856285556955171 3278929535784428335432757)
                  ·
                    refine ⟨307399643979790156446821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3278929535784428335432757 307399643979790156446821)
                    ·
                      rfl

theorem cell23_1795976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_1795976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795976 prefixEnd_1795976 := by exact prefixLift 1795976
  have htrace : WordTrace (prefixWord ++ tailWord_1795976) baseStart_1795976 baseEnd_1795976 := by
    simpa [prefixWord, tailWord_1795976, baseEnd_1795976] using wordTrace_append hprefix tailTrace_1795976
  have hstable : (prefixWord ++ tailWord_1795976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795976).length < 2 ^ (prefixWord ++ tailWord_1795976).sum := by decide
  have hdescent : baseEnd_1795976 < baseStart_1795976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1795989 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_1795989 : Nat := 118140960795 + 1795989 * 2 ^ 59
def prefixEnd_1795989 : Nat := 4983230072969 + 3 ^ 40 * 1795989 * 2
def baseEnd_1795989 : Nat := 307401869062626306159301

theorem tailTrace_1795989 : CollatzResearch.WordTrace tailWord_1795989 prefixEnd_1795989 307401869062626306159301 := by
  unfold tailWord_1795989
  simp only [CollatzResearch.WordTrace]
  refine ⟨65505100290446058346247021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43670066860297372230831347 65505100290446058346247021)
  ·
    refine ⟨24564412608917271879842633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65505100290446058346247021 24564412608917271879842633)
    ·
      refine ⟨18423309456687953909881975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24564412608917271879842633 18423309456687953909881975)
      ·
        refine ⟨27634964185031930864822963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18423309456687953909881975 27634964185031930864822963)
        ·
          refine ⟨41452446277547896297234445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27634964185031930864822963 41452446277547896297234445)
          ·
            refine ⟨15544667354080461111462917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41452446277547896297234445 15544667354080461111462917)
            ·
              refine ⟨2914625128890086458399297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15544667354080461111462917 2914625128890086458399297)
              ·
                refine ⟨2185968846667564843799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914625128890086458399297 2185968846667564843799473)
                ·
                  refine ⟨1639476635000673632849605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2185968846667564843799473 1639476635000673632849605)
                  ·
                    refine ⟨307401869062626306159301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639476635000673632849605 307401869062626306159301)
                    ·
                      rfl

theorem cell23_1795989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_1795989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1795989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1795989 prefixEnd_1795989 := by exact prefixLift 1795989
  have htrace : WordTrace (prefixWord ++ tailWord_1795989) baseStart_1795989 baseEnd_1795989 := by
    simpa [prefixWord, tailWord_1795989, baseEnd_1795989] using wordTrace_append hprefix tailTrace_1795989
  have hstable : (prefixWord ++ tailWord_1795989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1795989).length < 2 ^ (prefixWord ++ tailWord_1795989).sum := by decide
  have hdescent : baseEnd_1795989 < baseStart_1795989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1795989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796005 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1796005 : Nat := 118140960795 + 1796005 * 2 ^ 59
def prefixEnd_1796005 : Nat := 4983230072969 + 3 ^ 40 * 1796005 * 2
def baseEnd_1796005 : Nat := 922213822878350855877829

theorem tailTrace_1796005 : CollatzResearch.WordTrace tailWord_1796005 prefixEnd_1796005 922213822878350855877829 := by
  unfold tailWord_1796005
  simp only [CollatzResearch.WordTrace]
  refine ⟨65505683858388093078829469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43670455905592062052552979 65505683858388093078829469)
  ·
    refine ⟨24564631446895534904561051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65505683858388093078829469 24564631446895534904561051)
    ·
      refine ⟨36846947170343302356841577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24564631446895534904561051 36846947170343302356841577)
      ·
        refine ⟨27635210377757476767631183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36846947170343302356841577 27635210377757476767631183)
        ·
          refine ⟨41452815566636215151446775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27635210377757476767631183 41452815566636215151446775)
          ·
            refine ⟨62179223349954322727170163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41452815566636215151446775 62179223349954322727170163)
            ·
              refine ⟨93268835024931484090755245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62179223349954322727170163 93268835024931484090755245)
              ·
                refine ⟨34975813134349306534033217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93268835024931484090755245 34975813134349306534033217)
                ·
                  refine ⟨26231859850761979900524913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34975813134349306534033217 26231859850761979900524913)
                  ·
                    refine ⟨19673894888071484925393685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26231859850761979900524913 19673894888071484925393685)
                    ·
                      refine ⟨922213822878350855877829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19673894888071484925393685 922213822878350855877829)
                      ·
                        rfl

theorem cell23_1796005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1796005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796005 prefixEnd_1796005 := by exact prefixLift 1796005
  have htrace : WordTrace (prefixWord ++ tailWord_1796005) baseStart_1796005 baseEnd_1796005 := by
    simpa [prefixWord, tailWord_1796005, baseEnd_1796005] using wordTrace_append hprefix tailTrace_1796005
  have hstable : (prefixWord ++ tailWord_1796005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796005).length < 2 ^ (prefixWord ++ tailWord_1796005).sum := by decide
  have hdescent : baseEnd_1796005 < baseStart_1796005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796015 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 7]
def baseStart_1796015 : Nat := 118140960795 + 1796015 * 2 ^ 59
def prefixEnd_1796015 : Nat := 4983230072969 + 3 ^ 40 * 1796015 * 2
def baseEnd_1796015 : Nat := 307406319228298605584261

theorem tailTrace_1796015 : CollatzResearch.WordTrace tailWord_1796015 prefixEnd_1796015 307406319228298605584261 := by
  unfold tailWord_1796015
  simp only [CollatzResearch.WordTrace]
  refine ⟨65506048588351864786693499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43670699058901243191128999 65506048588351864786693499)
  ·
    refine ⟨98259072882527797180040249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65506048588351864786693499 98259072882527797180040249)
    ·
      refine ⟨73694304661895847885030187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98259072882527797180040249 73694304661895847885030187)
      ·
        refine ⟨110541456992843771827545281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73694304661895847885030187 110541456992843771827545281)
        ·
          refine ⟨82906092744632828870658961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110541456992843771827545281 82906092744632828870658961)
          ·
            refine ⟨62179569558474621652994221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82906092744632828870658961 62179569558474621652994221)
            ·
              refine ⟨23317338584427983119872833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62179569558474621652994221 23317338584427983119872833)
              ·
                refine ⟨17488003938320987339904625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23317338584427983119872833 17488003938320987339904625)
                ·
                  refine ⟨13116002953740740504928469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488003938320987339904625 13116002953740740504928469)
                  ·
                    refine ⟨307406319228298605584261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13116002953740740504928469 307406319228298605584261)
                    ·
                      rfl

theorem cell23_1796015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_1796015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796015 prefixEnd_1796015 := by exact prefixLift 1796015
  have htrace : WordTrace (prefixWord ++ tailWord_1796015) baseStart_1796015 baseEnd_1796015 := by
    simpa [prefixWord, tailWord_1796015, baseEnd_1796015] using wordTrace_append hprefix tailTrace_1796015
  have hstable : (prefixWord ++ tailWord_1796015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796015).length < 2 ^ (prefixWord ++ tailWord_1796015).sum := by decide
  have hdescent : baseEnd_1796015 < baseStart_1796015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796029 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1796029 : Nat := 118140960795 + 1796029 * 2 ^ 59
def prefixEnd_1796029 : Nat := 4983230072969 + 3 ^ 40 * 1796029 * 2
def baseEnd_1796029 : Nat := 922226146414058761977719

theorem tailTrace_1796029 : CollatzResearch.WordTrace tailWord_1796029 prefixEnd_1796029 922226146414058761977719 := by
  unfold tailWord_1796029
  simp only [CollatzResearch.WordTrace]
  refine ⟨65506559210301145177703141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43671039473534096785135427 65506559210301145177703141)
  ·
    refine ⟨12282479851931464720819339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65506559210301145177703141 12282479851931464720819339)
    ·
      refine ⟨18423719777897197081229009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12282479851931464720819339 18423719777897197081229009)
      ·
        refine ⟨13817789833422897810921757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18423719777897197081229009 13817789833422897810921757)
        ·
          refine ⟨5181671187533586679095659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13817789833422897810921757 5181671187533586679095659)
          ·
            refine ⟨7772506781300380018643489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181671187533586679095659 7772506781300380018643489)
            ·
              refine ⟨5829380085975285013982617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7772506781300380018643489 5829380085975285013982617)
              ·
                refine ⟨4372035064481463760486963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829380085975285013982617 4372035064481463760486963)
                ·
                  refine ⟨6558052596722195640730445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372035064481463760486963 6558052596722195640730445)
                  ·
                    refine ⟨2459269723770823365273917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6558052596722195640730445 2459269723770823365273917)
                    ·
                      refine ⟨922226146414058761977719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459269723770823365273917 922226146414058761977719)
                      ·
                        rfl

theorem cell23_1796029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1796029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796029 prefixEnd_1796029 := by exact prefixLift 1796029
  have htrace : WordTrace (prefixWord ++ tailWord_1796029) baseStart_1796029 baseEnd_1796029 := by
    simpa [prefixWord, tailWord_1796029, baseEnd_1796029] using wordTrace_append hprefix tailTrace_1796029
  have hstable : (prefixWord ++ tailWord_1796029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796029).length < 2 ^ (prefixWord ++ tailWord_1796029).sum := by decide
  have hdescent : baseEnd_1796029 < baseStart_1796029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796030 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_1796030 : Nat := 118140960795 + 1796030 * 2 ^ 59
def prefixEnd_1796030 : Nat := 4983230072969 + 3 ^ 40 * 1796030 * 2
def baseEnd_1796030 : Nat := 922226659894713258065215

theorem tailTrace_1796030 : CollatzResearch.WordTrace tailWord_1796030 prefixEnd_1796030 922226659894713258065215 := by
  unfold tailWord_1796030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188324460412190293561193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43671063788865014898993029 8188324460412190293561193)
  ·
    refine ⟨6141243345309142720170895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8188324460412190293561193 6141243345309142720170895)
    ·
      refine ⟨9211865017963714080256343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6141243345309142720170895 9211865017963714080256343)
      ·
        refine ⟨13817797526945571120384515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211865017963714080256343 13817797526945571120384515)
        ·
          refine ⟨20726696290418356680576773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817797526945571120384515 20726696290418356680576773)
          ·
            refine ⟨3886255554453441877608145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20726696290418356680576773 3886255554453441877608145)
            ·
              refine ⟨2914691665840081408206109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886255554453441877608145 2914691665840081408206109)
              ·
                refine ⟨1093009374690030528077291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2914691665840081408206109 1093009374690030528077291)
                ·
                  refine ⟨1639514062035045792115937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093009374690030528077291 1639514062035045792115937)
                  ·
                    refine ⟨1229635546526284344086953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1639514062035045792115937 1229635546526284344086953)
                    ·
                      refine ⟨922226659894713258065215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229635546526284344086953 922226659894713258065215)
                      ·
                        rfl

theorem cell23_1796030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_1796030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796030 prefixEnd_1796030 := by exact prefixLift 1796030
  have htrace : WordTrace (prefixWord ++ tailWord_1796030) baseStart_1796030 baseEnd_1796030 := by
    simpa [prefixWord, tailWord_1796030, baseEnd_1796030] using wordTrace_append hprefix tailTrace_1796030
  have hstable : (prefixWord ++ tailWord_1796030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796030).length < 2 ^ (prefixWord ++ tailWord_1796030).sum := by decide
  have hdescent : baseEnd_1796030 < baseStart_1796030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796060 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1796060 : Nat := 118140960795 + 1796060 * 2 ^ 59
def prefixEnd_1796060 : Nat := 4983230072969 + 3 ^ 40 * 1796060 * 2
def baseEnd_1796060 : Nat := 922242064314348140690077

theorem tailTrace_1796060 : CollatzResearch.WordTrace tailWord_1796060 prefixEnd_1796060 922242064314348140690077 := by
  unfold tailWord_1796060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32753844936594418736040817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43671793248792558314721089 32753844936594418736040817)
  ·
    refine ⟨24565383702445814052030613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32753844936594418736040817 24565383702445814052030613)
    ·
      refine ⟨1151502361052147533688935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24565383702445814052030613 1151502361052147533688935)
      ·
        refine ⟨1727253541578221300533403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151502361052147533688935 1727253541578221300533403)
        ·
          refine ⟨2590880312367331950800105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727253541578221300533403 2590880312367331950800105)
          ·
            refine ⟨1943160234275498963100079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2590880312367331950800105 1943160234275498963100079)
            ·
              refine ⟨2914740351413248444650119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943160234275498963100079 2914740351413248444650119)
              ·
                refine ⟨4372110527119872666975179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914740351413248444650119 4372110527119872666975179)
                ·
                  refine ⟨6558165790679809000462769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372110527119872666975179 6558165790679809000462769)
                  ·
                    refine ⟨4918624343009856750347077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558165790679809000462769 4918624343009856750347077)
                    ·
                      refine ⟨922242064314348140690077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4918624343009856750347077 922242064314348140690077)
                      ·
                        rfl

theorem cell23_1796060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1796060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796060 prefixEnd_1796060 := by exact prefixLift 1796060
  have htrace : WordTrace (prefixWord ++ tailWord_1796060) baseStart_1796060 baseEnd_1796060 := by
    simpa [prefixWord, tailWord_1796060, baseEnd_1796060] using wordTrace_append hprefix tailTrace_1796060
  have hstable : (prefixWord ++ tailWord_1796060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796060).length < 2 ^ (prefixWord ++ tailWord_1796060).sum := by decide
  have hdescent : baseEnd_1796060 < baseStart_1796060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796063 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 2, 1, 3]
def baseStart_1796063 : Nat := 118140960795 + 1796063 * 2 ^ 59
def prefixEnd_1796063 : Nat := 4983230072969 + 3 ^ 40 * 1796063 * 2
def baseEnd_1796063 : Nat := 922243604756311628952563

theorem tailTrace_1796063 : CollatzResearch.WordTrace tailWord_1796063 prefixEnd_1796063 922243604756311628952563 := by
  unfold tailWord_1796063
  simp only [CollatzResearch.WordTrace]
  refine ⟨65507799292177968984440843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43671866194785312656293895 65507799292177968984440843)
  ·
    refine ⟨98261698938266953476661265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65507799292177968984440843 98261698938266953476661265)
    ·
      refine ⟨73696274203700215107495949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98261698938266953476661265 73696274203700215107495949)
      ·
        refine ⟨27636102826387580665310981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73696274203700215107495949 27636102826387580665310981)
        ·
          refine ⟨5181769279947671374745809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27636102826387580665310981 5181769279947671374745809)
          ·
            refine ⟨3886326959960753531059357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181769279947671374745809 3886326959960753531059357)
            ·
              refine ⟨1457372609985282574147259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3886326959960753531059357 1457372609985282574147259)
              ·
                refine ⟨2186058914977923861220889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457372609985282574147259 2186058914977923861220889)
                ·
                  refine ⟨1639544186233442895915667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186058914977923861220889 1639544186233442895915667)
                  ·
                    refine ⟨2459316279350164343873501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1639544186233442895915667 2459316279350164343873501)
                    ·
                      refine ⟨922243604756311628952563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459316279350164343873501 922243604756311628952563)
                      ·
                        rfl

theorem cell23_1796063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_1796063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796063 prefixEnd_1796063 := by exact prefixLift 1796063
  have htrace : WordTrace (prefixWord ++ tailWord_1796063) baseStart_1796063 baseEnd_1796063 := by
    simpa [prefixWord, tailWord_1796063, baseEnd_1796063] using wordTrace_append hprefix tailTrace_1796063
  have hstable : (prefixWord ++ tailWord_1796063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796063).length < 2 ^ (prefixWord ++ tailWord_1796063).sum := by decide
  have hdescent : baseEnd_1796063 < baseStart_1796063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796072 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1796072 : Nat := 118140960795 + 1796072 * 2 ^ 59
def prefixEnd_1796072 : Nat := 4983230072969 + 3 ^ 40 * 1796072 * 2
def baseEnd_1796072 : Nat := 922248226082202093740021

theorem tailTrace_1796072 : CollatzResearch.WordTrace tailWord_1796072 prefixEnd_1796072 922248226082202093740021 := by
  unfold tailWord_1796072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32754063774572681760759235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43672085032763575681012313 32754063774572681760759235)
  ·
    refine ⟨49131095661859022641138853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32754063774572681760759235 49131095661859022641138853)
    ·
      refine ⟨9212080436598566745213535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49131095661859022641138853 9212080436598566745213535)
      ·
        refine ⟨13818120654897850117820303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9212080436598566745213535 13818120654897850117820303)
        ·
          refine ⟨20727180982346775176730455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13818120654897850117820303 20727180982346775176730455)
          ·
            refine ⟨31090771473520162765095683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20727180982346775176730455 31090771473520162765095683)
            ·
              refine ⟨46636157210280244147643525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31090771473520162765095683 46636157210280244147643525)
              ·
                refine ⟨8744279476927545777683161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46636157210280244147643525 8744279476927545777683161)
                ·
                  refine ⟨6558209607695659333262371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8744279476927545777683161 6558209607695659333262371)
                  ·
                    refine ⟨9837314411543488999893557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558209607695659333262371 9837314411543488999893557)
                    ·
                      refine ⟨922248226082202093740021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9837314411543488999893557 922248226082202093740021)
                      ·
                        rfl

theorem cell23_1796072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1796072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796072 prefixEnd_1796072 := by exact prefixLift 1796072
  have htrace : WordTrace (prefixWord ++ tailWord_1796072) baseStart_1796072 baseEnd_1796072 := by
    simpa [prefixWord, tailWord_1796072, baseEnd_1796072] using wordTrace_append hprefix tailTrace_1796072
  have hstable : (prefixWord ++ tailWord_1796072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796072).length < 2 ^ (prefixWord ++ tailWord_1796072).sum := by decide
  have hdescent : baseEnd_1796072 < baseStart_1796072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796159 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1796159 : Nat := 118140960795 + 1796159 * 2 ^ 59
def prefixEnd_1796159 : Nat := 4983230072969 + 3 ^ 40 * 1796159 * 2
def baseEnd_1796159 : Nat := 922292898899143253352121

theorem tailTrace_1796159 : CollatzResearch.WordTrace tailWord_1796159 prefixEnd_1796159 922292898899143253352121 := by
  unfold tailWord_1796159
  simp only [CollatzResearch.WordTrace]
  refine ⟨65511300699830177379935531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43674200466553451586623687 65511300699830177379935531)
  ·
    refine ⟨98266951049745266069903297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65511300699830177379935531 98266951049745266069903297)
    ·
      refine ⟨73700213287308949552427473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98266951049745266069903297 73700213287308949552427473)
      ·
        refine ⟨55275159965481712164320605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73700213287308949552427473 55275159965481712164320605)
        ·
          refine ⟨20728184987055642061620227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55275159965481712164320605 20728184987055642061620227)
          ·
            refine ⟨31092277480583463092430341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728184987055642061620227 31092277480583463092430341)
            ·
              refine ⟨5829802027609399329830689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31092277480583463092430341 5829802027609399329830689)
              ·
                refine ⟨4372351520707049497373017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829802027609399329830689 4372351520707049497373017)
                ·
                  refine ⟨3279263640530287123029763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4372351520707049497373017 3279263640530287123029763)
                  ·
                    refine ⟨4918895460795430684544645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3279263640530287123029763 4918895460795430684544645)
                    ·
                      refine ⟨922292898899143253352121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4918895460795430684544645 922292898899143253352121)
                      ·
                        rfl

theorem cell23_1796159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1796159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796159 prefixEnd_1796159 := by exact prefixLift 1796159
  have htrace : WordTrace (prefixWord ++ tailWord_1796159) baseStart_1796159 baseEnd_1796159 := by
    simpa [prefixWord, tailWord_1796159, baseEnd_1796159] using wordTrace_append hprefix tailTrace_1796159
  have hstable : (prefixWord ++ tailWord_1796159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796159).length < 2 ^ (prefixWord ++ tailWord_1796159).sum := by decide
  have hdescent : baseEnd_1796159 < baseStart_1796159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796166 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1796166 : Nat := 118140960795 + 1796166 * 2 ^ 59
def prefixEnd_1796166 : Nat := 4983230072969 + 3 ^ 40 * 1796166 * 2
def baseEnd_1796166 : Nat := 922296493263724725964589

theorem tailTrace_1796166 : CollatzResearch.WordTrace tailWord_1796166 prefixEnd_1796166 922296493263724725964589 := by
  unfold tailWord_1796166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047236125337650549232511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43674370673869878383626901 2047236125337650549232511)
  ·
    refine ⟨3070854188006475823848767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047236125337650549232511 3070854188006475823848767)
    ·
      refine ⟨4606281282009713735773151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070854188006475823848767 4606281282009713735773151)
      ·
        refine ⟨6909421923014570603659727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606281282009713735773151 6909421923014570603659727)
        ·
          refine ⟨10364132884521855905489591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909421923014570603659727 10364132884521855905489591)
          ·
            refine ⟨15546199326782783858234387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364132884521855905489591 15546199326782783858234387)
            ·
              refine ⟨23319298990174175787351581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546199326782783858234387 23319298990174175787351581)
              ·
                refine ⟨8744737121315315920256843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23319298990174175787351581 8744737121315315920256843)
                ·
                  refine ⟨13117105681972973880385265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744737121315315920256843 13117105681972973880385265)
                  ·
                    refine ⟨9837829261479730410288949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13117105681972973880385265 9837829261479730410288949)
                    ·
                      refine ⟨922296493263724725964589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9837829261479730410288949 922296493263724725964589)
                      ·
                        rfl

theorem cell23_1796166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1796166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796166 prefixEnd_1796166 := by exact prefixLift 1796166
  have htrace : WordTrace (prefixWord ++ tailWord_1796166) baseStart_1796166 baseEnd_1796166 := by
    simpa [prefixWord, tailWord_1796166, baseEnd_1796166] using wordTrace_append hprefix tailTrace_1796166
  have hstable : (prefixWord ++ tailWord_1796166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796166).length < 2 ^ (prefixWord ++ tailWord_1796166).sum := by decide
  have hdescent : baseEnd_1796166 < baseStart_1796166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796169 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_1796169 : Nat := 118140960795 + 1796169 * 2 ^ 59
def prefixEnd_1796169 : Nat := 4983230072969 + 3 ^ 40 * 1796169 * 2
def baseEnd_1796169 : Nat := 307432677901896071409025

theorem tailTrace_1796169 : CollatzResearch.WordTrace tailWord_1796169 prefixEnd_1796169 307432677901896071409025 := by
  unfold tailWord_1796169
  simp only [CollatzResearch.WordTrace]
  refine ⟨65511665429793949087799561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43674443619862632725199707 65511665429793949087799561)
  ·
    refine ⟨49133749072345461815849671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65511665429793949087799561 49133749072345461815849671)
    ·
      refine ⟨73700623608518192723774507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49133749072345461815849671 73700623608518192723774507)
      ·
        refine ⟨110550935412777289085661761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73700623608518192723774507 110550935412777289085661761)
        ·
          refine ⟨82913201559582966814246321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110550935412777289085661761 82913201559582966814246321)
          ·
            refine ⟨62184901169687225110684741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82913201559582966814246321 62184901169687225110684741)
            ·
              refine ⟨11659668969316354708253389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62184901169687225110684741 11659668969316354708253389)
              ·
                refine ⟨4372375863493633015595021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11659668969316354708253389 4372375863493633015595021)
                ·
                  refine ⟨1639640948810112380848133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4372375863493633015595021 1639640948810112380848133)
                  ·
                    refine ⟨307432677901896071409025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639640948810112380848133 307432677901896071409025)
                    ·
                      rfl

theorem cell23_1796169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_1796169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796169 prefixEnd_1796169 := by exact prefixLift 1796169
  have htrace : WordTrace (prefixWord ++ tailWord_1796169) baseStart_1796169 baseEnd_1796169 := by
    simpa [prefixWord, tailWord_1796169, baseEnd_1796169] using wordTrace_append hprefix tailTrace_1796169
  have hstable : (prefixWord ++ tailWord_1796169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796169).length < 2 ^ (prefixWord ++ tailWord_1796169).sum := by decide
  have hdescent : baseEnd_1796169 < baseStart_1796169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796196 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_1796196 : Nat := 118140960795 + 1796196 * 2 ^ 59
def prefixEnd_1796196 : Nat := 4983230072969 + 3 ^ 40 * 1796196 * 2
def baseEnd_1796196 : Nat := 922311897683359608589451

theorem tailTrace_1796196 : CollatzResearch.WordTrace tailWord_1796196 prefixEnd_1796196 922311897683359608589451 := by
  unfold tailWord_1796196
  simp only [CollatzResearch.WordTrace]
  refine ⟨32756325100348066349516221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43675100133797421799354961 32756325100348066349516221)
  ·
    refine ⟨12283621912630524881068583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32756325100348066349516221 12283621912630524881068583)
    ·
      refine ⟨18425432868945787321602875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283621912630524881068583 18425432868945787321602875)
      ·
        refine ⟨27638149303418680982404313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425432868945787321602875 27638149303418680982404313)
        ·
          refine ⟨20728611977564010736803235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27638149303418680982404313 20728611977564010736803235)
          ·
            refine ⟨31092917966346016105204853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728611977564010736803235 31092917966346016105204853)
            ·
              refine ⟨2914961059344939009862955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31092917966346016105204853 2914961059344939009862955)
              ·
                refine ⟨4372441589017408514794433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914961059344939009862955 4372441589017408514794433)
                ·
                  refine ⟨3279331191763056386095825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4372441589017408514794433 3279331191763056386095825)
                  ·
                    refine ⟨2459498393822292289571869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3279331191763056386095825 2459498393822292289571869)
                    ·
                      refine ⟨922311897683359608589451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459498393822292289571869 922311897683359608589451)
                      ·
                        rfl

theorem cell23_1796196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_1796196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796196 prefixEnd_1796196 := by exact prefixLift 1796196
  have htrace : WordTrace (prefixWord ++ tailWord_1796196) baseStart_1796196 baseEnd_1796196 := by
    simpa [prefixWord, tailWord_1796196, baseEnd_1796196] using wordTrace_append hprefix tailTrace_1796196
  have hstable : (prefixWord ++ tailWord_1796196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796196).length < 2 ^ (prefixWord ++ tailWord_1796196).sum := by decide
  have hdescent : baseEnd_1796196 < baseStart_1796196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796249 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1796249 : Nat := 118140960795 + 1796249 * 2 ^ 59
def prefixEnd_1796249 : Nat := 4983230072969 + 3 ^ 40 * 1796249 * 2
def baseEnd_1796249 : Nat := 922339112158047901226707

theorem tailTrace_1796249 : CollatzResearch.WordTrace tailWord_1796249 prefixEnd_1796249 922339112158047901226707 := by
  unfold tailWord_1796249
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514583269504122750711801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43676388846336081833807867 65514583269504122750711801)
  ·
    refine ⟨49135937452128092063033851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65514583269504122750711801 49135937452128092063033851)
    ·
      refine ⟨73703906178192138094550777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49135937452128092063033851 73703906178192138094550777)
      ·
        refine ⟨55277929633644103570913083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73703906178192138094550777 55277929633644103570913083)
        ·
          refine ⟨82916894450466155356369625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55277929633644103570913083 82916894450466155356369625)
          ·
            refine ⟨62187670837849616517277219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82916894450466155356369625 62187670837849616517277219)
            ·
              refine ⟨93281506256774424775915829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62187670837849616517277219 93281506256774424775915829)
              ·
                refine ⟨8745141211572602322742109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93281506256774424775915829 8745141211572602322742109)
                ·
                  refine ⟨3279427954339725871028291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8745141211572602322742109 3279427954339725871028291)
                  ·
                    refine ⟨4919141931509588806542437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3279427954339725871028291 4919141931509588806542437)
                    ·
                      refine ⟨922339112158047901226707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4919141931509588806542437 922339112158047901226707)
                      ·
                        rfl

theorem cell23_1796249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1796249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796249 prefixEnd_1796249 := by exact prefixLift 1796249
  have htrace : WordTrace (prefixWord ++ tailWord_1796249) baseStart_1796249 baseEnd_1796249 := by
    simpa [prefixWord, tailWord_1796249, baseEnd_1796249] using wordTrace_append hprefix tailTrace_1796249
  have hstable : (prefixWord ++ tailWord_1796249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796249).length < 2 ^ (prefixWord ++ tailWord_1796249).sum := by decide
  have hdescent : baseEnd_1796249 < baseStart_1796249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796254 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1796254 : Nat := 118140960795 + 1796254 * 2 ^ 59
def prefixEnd_1796254 : Nat := 4983230072969 + 3 ^ 40 * 1796254 * 2
def baseEnd_1796254 : Nat := 307447226520440127221395

theorem tailTrace_1796254 : CollatzResearch.WordTrace tailWord_1796254 prefixEnd_1796254 307447226520440127221395 := by
  unfold tailWord_1796254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189345704310751075580477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43676510422990672403095877 8189345704310751075580477)
  ·
    refine ⟨3071004639116531653342679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8189345704310751075580477 3071004639116531653342679)
    ·
      refine ⟨4606506958674797480014019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071004639116531653342679 4606506958674797480014019)
      ·
        refine ⟨6909760438012196220021029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606506958674797480014019 6909760438012196220021029)
        ·
          refine ⟨1295580082127286791253943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6909760438012196220021029 1295580082127286791253943)
          ·
            refine ⟨1943370123190930186880915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295580082127286791253943 1943370123190930186880915)
            ·
              refine ⟨2915055184786395280321373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943370123190930186880915 2915055184786395280321373)
              ·
                refine ⟨1093145694294898230120515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2915055184786395280321373 1093145694294898230120515)
                ·
                  refine ⟨1639718541442347345180773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093145694294898230120515 1639718541442347345180773)
                  ·
                    refine ⟨307447226520440127221395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639718541442347345180773 307447226520440127221395)
                    ·
                      rfl

theorem cell23_1796254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1796254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796254 prefixEnd_1796254 := by exact prefixLift 1796254
  have htrace : WordTrace (prefixWord ++ tailWord_1796254) baseStart_1796254 baseEnd_1796254 := by
    simpa [prefixWord, tailWord_1796254, baseEnd_1796254] using wordTrace_append hprefix tailTrace_1796254
  have hstable : (prefixWord ++ tailWord_1796254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796254).length < 2 ^ (prefixWord ++ tailWord_1796254).sum := by decide
  have hdescent : baseEnd_1796254 < baseStart_1796254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796277 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1796277 : Nat := 118140960795 + 1796277 * 2 ^ 59
def prefixEnd_1796277 : Nat := 4983230072969 + 3 ^ 40 * 1796277 * 2
def baseEnd_1796277 : Nat := 922353489616373791676579

theorem tailTrace_1796277 : CollatzResearch.WordTrace tailWord_1796277 prefixEnd_1796277 922353489616373791676579 := by
  unfold tailWord_1796277
  simp only [CollatzResearch.WordTrace]
  refine ⟨65515604513402683532731085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43677069675601789021820723 65515604513402683532731085)
  ·
    refine ⟨24568351692526006324774157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65515604513402683532731085 24568351692526006324774157)
    ·
      refine ⟨9213131884697252371790309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24568351692526006324774157 9213131884697252371790309)
      ·
        refine ⟨1727462228380734819710683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9213131884697252371790309 1727462228380734819710683)
        ·
          refine ⟨2591193342571102229566025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727462228380734819710683 2591193342571102229566025)
          ·
            refine ⟨1943395006928326672174519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591193342571102229566025 1943395006928326672174519)
            ·
              refine ⟨2915092510392490008261779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943395006928326672174519 2915092510392490008261779)
              ·
                refine ⟨4372638765588735012392669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915092510392490008261779 4372638765588735012392669)
                ·
                  refine ⟨1639739537095775629647251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4372638765588735012392669 1639739537095775629647251)
                  ·
                    refine ⟨2459609305643663444470877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1639739537095775629647251 2459609305643663444470877)
                    ·
                      refine ⟨922353489616373791676579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459609305643663444470877 922353489616373791676579)
                      ·
                        rfl

theorem cell23_1796277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1796277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796277 prefixEnd_1796277 := by exact prefixLift 1796277
  have htrace : WordTrace (prefixWord ++ tailWord_1796277) baseStart_1796277 baseEnd_1796277 := by
    simpa [prefixWord, tailWord_1796277, baseEnd_1796277] using wordTrace_append hprefix tailTrace_1796277
  have hstable : (prefixWord ++ tailWord_1796277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796277).length < 2 ^ (prefixWord ++ tailWord_1796277).sum := by decide
  have hdescent : baseEnd_1796277 < baseStart_1796277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796279 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1796279 : Nat := 118140960795 + 1796279 * 2 ^ 59
def prefixEnd_1796279 : Nat := 4983230072969 + 3 ^ 40 * 1796279 * 2
def baseEnd_1796279 : Nat := 922354516577682783851569

theorem tailTrace_1796279 : CollatzResearch.WordTrace tailWord_1796279 prefixEnd_1796279 922354516577682783851569 := by
  unfold tailWord_1796279
  simp only [CollatzResearch.WordTrace]
  refine ⟨65515677459395437874303891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43677118306263625249535927 65515677459395437874303891)
  ·
    refine ⟨98273516189093156811455837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65515677459395437874303891 98273516189093156811455837)
    ·
      refine ⟨36852568570909933804295939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98273516189093156811455837 36852568570909933804295939)
      ·
        refine ⟨55278852856364900706443909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852568570909933804295939 55278852856364900706443909)
        ·
          refine ⟨10364784910568418882458233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55278852856364900706443909 10364784910568418882458233)
          ·
            refine ⟨7773588682926314161843675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10364784910568418882458233 7773588682926314161843675)
            ·
              refine ⟨11660383024389471242765513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773588682926314161843675 11660383024389471242765513)
              ·
                refine ⟨8745287268292103432074135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11660383024389471242765513 8745287268292103432074135)
                ·
                  refine ⟨13117930902438155148111203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745287268292103432074135 13117930902438155148111203)
                  ·
                    refine ⟨19676896353657232722166805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13117930902438155148111203 19676896353657232722166805)
                    ·
                      refine ⟨922354516577682783851569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19676896353657232722166805 922354516577682783851569)
                      ·
                        rfl

theorem cell23_1796279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1796279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796279 prefixEnd_1796279 := by exact prefixLift 1796279
  have htrace : WordTrace (prefixWord ++ tailWord_1796279) baseStart_1796279 baseEnd_1796279 := by
    simpa [prefixWord, tailWord_1796279, baseEnd_1796279] using wordTrace_append hprefix tailTrace_1796279
  have hstable : (prefixWord ++ tailWord_1796279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796279).length < 2 ^ (prefixWord ++ tailWord_1796279).sum := by decide
  have hdescent : baseEnd_1796279 < baseStart_1796279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796293 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_1796293 : Nat := 118140960795 + 1796293 * 2 ^ 59
def prefixEnd_1796293 : Nat := 4983230072969 + 3 ^ 40 * 1796293 * 2
def baseEnd_1796293 : Nat := 307453901768948576358835

theorem tailTrace_1796293 : CollatzResearch.WordTrace tailWord_1796293 prefixEnd_1796293 307453901768948576358835 := by
  unfold tailWord_1796293
  simp only [CollatzResearch.WordTrace]
  refine ⟨65516188081344718265313533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43677458720896478843542355 65516188081344718265313533)
  ·
    refine ⟨24568570530504269349492575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65516188081344718265313533 24568570530504269349492575)
    ·
      refine ⟨36852855795756404024238863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24568570530504269349492575 36852855795756404024238863)
      ·
        refine ⟨55279283693634606036358295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852855795756404024238863 55279283693634606036358295)
        ·
          refine ⟨82918925540451909054537443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55279283693634606036358295 82918925540451909054537443)
          ·
            refine ⟨124378388310677863581806165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82918925540451909054537443 124378388310677863581806165)
            ·
              refine ⟨1457559238015756213849291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 124378388310677863581806165 1457559238015756213849291)
              ·
                refine ⟨2186338857023634320773937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457559238015756213849291 2186338857023634320773937)
                ·
                  refine ⟨1639754142767725740580453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186338857023634320773937 1639754142767725740580453)
                  ·
                    refine ⟨307453901768948576358835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1639754142767725740580453 307453901768948576358835)
                    ·
                      rfl

theorem cell23_1796293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_1796293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796293 prefixEnd_1796293 := by exact prefixLift 1796293
  have htrace : WordTrace (prefixWord ++ tailWord_1796293) baseStart_1796293 baseEnd_1796293 := by
    simpa [prefixWord, tailWord_1796293, baseEnd_1796293] using wordTrace_append hprefix tailTrace_1796293
  have hstable : (prefixWord ++ tailWord_1796293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796293).length < 2 ^ (prefixWord ++ tailWord_1796293).sum := by decide
  have hdescent : baseEnd_1796293 < baseStart_1796293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796339 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_1796339 : Nat := 118140960795 + 1796339 * 2 ^ 59
def prefixEnd_1796339 : Nat := 4983230072969 + 3 ^ 40 * 1796339 * 2
def baseEnd_1796339 : Nat := 922385325416952549101293

theorem tailTrace_1796339 : CollatzResearch.WordTrace tailWord_1796339 prefixEnd_1796339 922385325416952549101293 := by
  unfold tailWord_1796339
  simp only [CollatzResearch.WordTrace]
  refine ⟨65517865839178068121488071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43678577226118712080992047 65517865839178068121488071)
  ·
    refine ⟨98276798758767102182232107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65517865839178068121488071 98276798758767102182232107)
    ·
      refine ⟨147415198138150653273348161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98276798758767102182232107 147415198138150653273348161)
      ·
        refine ⟨110561398603612989955011121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147415198138150653273348161 110561398603612989955011121)
        ·
          refine ⟨82921048952709742466258341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110561398603612989955011121 82921048952709742466258341)
          ·
            refine ⟨15547696678633076712423439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82921048952709742466258341 15547696678633076712423439)
            ·
              refine ⟨23321545017949615068635159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15547696678633076712423439 23321545017949615068635159)
              ·
                refine ⟨34982317526924422602952739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23321545017949615068635159 34982317526924422602952739)
                ·
                  refine ⟨52473476290386633904429109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34982317526924422602952739 52473476290386633904429109)
                  ·
                    refine ⟨4919388402223746928540229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52473476290386633904429109 4919388402223746928540229)
                    ·
                      refine ⟨922385325416952549101293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4919388402223746928540229 922385325416952549101293)
                      ·
                        rfl

theorem cell23_1796339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_1796339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796339 prefixEnd_1796339 := by exact prefixLift 1796339
  have htrace : WordTrace (prefixWord ++ tailWord_1796339) baseStart_1796339 baseEnd_1796339 := by
    simpa [prefixWord, tailWord_1796339, baseEnd_1796339] using wordTrace_append hprefix tailTrace_1796339
  have hstable : (prefixWord ++ tailWord_1796339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796339).length < 2 ^ (prefixWord ++ tailWord_1796339).sum := by decide
  have hdescent : baseEnd_1796339 < baseStart_1796339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796350 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1796350 : Nat := 118140960795 + 1796350 * 2 ^ 59
def prefixEnd_1796350 : Nat := 4983230072969 + 3 ^ 40 * 1796350 * 2
def baseEnd_1796350 : Nat := 922390973704152006063743

theorem tailTrace_1796350 : CollatzResearch.WordTrace tailWord_1796350 prefixEnd_1796350 922390973704152006063743 := by
  unfold tailWord_1796350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8189783380267277125017313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43678844694758811333425669 8189783380267277125017313)
  ·
    refine ⟨6142337535200457843762985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8189783380267277125017313 6142337535200457843762985)
    ·
      refine ⟨4606753151400343382822239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6142337535200457843762985 4606753151400343382822239)
      ·
        refine ⟨6910129727100515074233359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606753151400343382822239 6910129727100515074233359)
        ·
          refine ⟨10365194590650772611350039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910129727100515074233359 10365194590650772611350039)
          ·
            refine ⟨15547791885976158917025059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365194590650772611350039 15547791885976158917025059)
            ·
              refine ⟨23321687828964238375537589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15547791885976158917025059 23321687828964238375537589)
              ·
                refine ⟨2186408233965397347706649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23321687828964238375537589 2186408233965397347706649)
                ·
                  refine ⟨1639806175474048010779987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186408233965397347706649 1639806175474048010779987)
                  ·
                    refine ⟨2459709263211072016169981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1639806175474048010779987 2459709263211072016169981)
                    ·
                      refine ⟨922390973704152006063743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459709263211072016169981 922390973704152006063743)
                      ·
                        rfl

theorem cell23_1796350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1796350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796350 prefixEnd_1796350 := by exact prefixLift 1796350
  have htrace : WordTrace (prefixWord ++ tailWord_1796350) baseStart_1796350 baseEnd_1796350 := by
    simpa [prefixWord, tailWord_1796350, baseEnd_1796350] using wordTrace_append hprefix tailTrace_1796350
  have hstable : (prefixWord ++ tailWord_1796350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796350).length < 2 ^ (prefixWord ++ tailWord_1796350).sum := by decide
  have hdescent : baseEnd_1796350 < baseStart_1796350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796373 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_1796373 : Nat := 118140960795 + 1796373 * 2 ^ 59
def prefixEnd_1796373 : Nat := 4983230072969 + 3 ^ 40 * 1796373 * 2
def baseEnd_1796373 : Nat := 922402783759205416076137

theorem tailTrace_1796373 : CollatzResearch.WordTrace tailWord_1796373 prefixEnd_1796373 922402783759205416076137 := by
  unfold tailWord_1796373
  simp only [CollatzResearch.WordTrace]
  refine ⟨65519105921054891928225773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43679403947369927952150515 65519105921054891928225773)
  ·
    refine ⟨24569664720395584473084665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65519105921054891928225773 24569664720395584473084665)
    ·
      refine ⟨18427248540296688354813499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24569664720395584473084665 18427248540296688354813499)
      ·
        refine ⟨27640872810445032532220249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18427248540296688354813499 27640872810445032532220249)
        ·
          refine ⟨20730654607833774399165187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27640872810445032532220249 20730654607833774399165187)
          ·
            refine ⟨31095981911750661598747781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20730654607833774399165187 31095981911750661598747781)
            ·
              refine ⟨5830496608453249049765209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31095981911750661598747781 5830496608453249049765209)
              ·
                refine ⟨4372872456339936787323907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5830496608453249049765209 4372872456339936787323907)
                ·
                  refine ⟨6559308684509905180985861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372872456339936787323907 6559308684509905180985861)
                  ·
                    refine ⟨1229870378345607221434849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6559308684509905180985861 1229870378345607221434849)
                    ·
                      refine ⟨922402783759205416076137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1229870378345607221434849 922402783759205416076137)
                      ·
                        rfl

theorem cell23_1796373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_1796373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796373 prefixEnd_1796373 := by exact prefixLift 1796373
  have htrace : WordTrace (prefixWord ++ tailWord_1796373) baseStart_1796373 baseEnd_1796373 := by
    simpa [prefixWord, tailWord_1796373, baseEnd_1796373] using wordTrace_append hprefix tailTrace_1796373
  have hstable : (prefixWord ++ tailWord_1796373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796373).length < 2 ^ (prefixWord ++ tailWord_1796373).sum := by decide
  have hdescent : baseEnd_1796373 < baseStart_1796373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796496 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_1796496 : Nat := 118140960795 + 1796496 * 2 ^ 59
def prefixEnd_1796496 : Nat := 4983230072969 + 3 ^ 40 * 1796496 * 2
def baseEnd_1796496 : Nat := 922465941879708434838071

theorem tailTrace_1796496 : CollatzResearch.WordTrace tailWord_1796496 prefixEnd_1796496 922465941879708434838071 := by
  unfold tailWord_1796496
  simp only [CollatzResearch.WordTrace]
  refine ⟨32761796049804641967476671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43682394733072855956635561 32761796049804641967476671)
  ·
    refine ⟨49142694074706962951215007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32761796049804641967476671 49142694074706962951215007)
    ·
      refine ⟨73714041112060444426822511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49142694074706962951215007 73714041112060444426822511)
      ·
        refine ⟨110571061668090666640233767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73714041112060444426822511 110571061668090666640233767)
        ·
          refine ⟨165856592502135999960350651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110571061668090666640233767 165856592502135999960350651)
          ·
            refine ⟨248784888753203999940525977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165856592502135999960350651 248784888753203999940525977)
            ·
              refine ⟨186588666564902999955394483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248784888753203999940525977 186588666564902999955394483)
              ·
                refine ⟨279882999847354499933091725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186588666564902999955394483 279882999847354499933091725)
                ·
                  refine ⟨104956124942757937474909397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279882999847354499933091725 104956124942757937474909397)
                  ·
                    refine ⟨2459909178345889159568189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 104956124942757937474909397 2459909178345889159568189)
                    ·
                      refine ⟨922465941879708434838071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459909178345889159568189 922465941879708434838071)
                      ·
                        rfl

theorem cell23_1796496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_1796496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796496 prefixEnd_1796496 := by exact prefixLift 1796496
  have htrace : WordTrace (prefixWord ++ tailWord_1796496) baseStart_1796496 baseEnd_1796496 := by
    simpa [prefixWord, tailWord_1796496, baseEnd_1796496] using wordTrace_append hprefix tailTrace_1796496
  have hstable : (prefixWord ++ tailWord_1796496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796496).length < 2 ^ (prefixWord ++ tailWord_1796496).sum := by decide
  have hdescent : baseEnd_1796496 < baseStart_1796496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796520 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 6]
def baseStart_1796520 : Nat := 118140960795 + 1796520 * 2 ^ 59
def prefixEnd_1796520 : Nat := 4983230072969 + 3 ^ 40 * 1796520 * 2
def baseEnd_1796520 : Nat := 102497585046157371215329

theorem tailTrace_1796520 : CollatzResearch.WordTrace tailWord_1796520 prefixEnd_1796520 102497585046157371215329 := by
  unfold tailWord_1796520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32762233725761168016913507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43682978301014890689218009 32762233725761168016913507)
  ·
    refine ⟨49143350588641752025370261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32762233725761168016913507 49143350588641752025370261)
    ·
      refine ⟨2303594558842582126189231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49143350588641752025370261 2303594558842582126189231)
      ·
        refine ⟨3455391838263873189283847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303594558842582126189231 3455391838263873189283847)
        ·
          refine ⟨5183087757395809783925771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455391838263873189283847 5183087757395809783925771)
          ·
            refine ⟨7774631636093714675888657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183087757395809783925771 7774631636093714675888657)
            ·
              refine ⟨5830973727070286006916493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774631636093714675888657 5830973727070286006916493)
              ·
                refine ⟨2186615147651357252593685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5830973727070286006916493 2186615147651357252593685)
                ·
                  refine ⟨102497585046157371215329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2186615147651357252593685 102497585046157371215329)
                  ·
                    rfl

theorem cell23_1796520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_1796520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796520 prefixEnd_1796520 := by exact prefixLift 1796520
  have htrace : WordTrace (prefixWord ++ tailWord_1796520) baseStart_1796520 baseEnd_1796520 := by
    simpa [prefixWord, tailWord_1796520, baseEnd_1796520] using wordTrace_append hprefix tailTrace_1796520
  have hstable : (prefixWord ++ tailWord_1796520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796520).length < 2 ^ (prefixWord ++ tailWord_1796520).sum := by decide
  have hdescent : baseEnd_1796520 < baseStart_1796520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796530 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_1796530 : Nat := 118140960795 + 1796530 * 2 ^ 59
def prefixEnd_1796530 : Nat := 4983230072969 + 3 ^ 40 * 1796530 * 2
def baseEnd_1796530 : Nat := 922483400221961301812915

theorem tailTrace_1796530 : CollatzResearch.WordTrace tailWord_1796530 prefixEnd_1796530 922483400221961301812915 := by
  unfold tailWord_1796530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381208045371526935422761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43683221454324071827794029 16381208045371526935422761)
  ·
    refine ⟨12285906034028645201567071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16381208045371526935422761 12285906034028645201567071)
    ·
      refine ⟨18428859051042967802350607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12285906034028645201567071 18428859051042967802350607)
      ·
        refine ⟨27643288576564451703525911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18428859051042967802350607 27643288576564451703525911)
        ·
          refine ⟨41464932864846677555288867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27643288576564451703525911 41464932864846677555288867)
          ·
            refine ⟨62197399297270016332933301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41464932864846677555288867 62197399297270016332933301)
            ·
              refine ⟨5831006184119064031212497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62197399297270016332933301 5831006184119064031212497)
              ·
                refine ⟨4373254638089298023409373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5831006184119064031212497 4373254638089298023409373)
                ·
                  refine ⟨1639970489283486758778515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4373254638089298023409373 1639970489283486758778515)
                  ·
                    refine ⟨2459955733925230138167773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1639970489283486758778515 2459955733925230138167773)
                    ·
                      refine ⟨922483400221961301812915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2459955733925230138167773 922483400221961301812915)
                      ·
                        rfl

theorem cell23_1796530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_1796530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796530 prefixEnd_1796530 := by exact prefixLift 1796530
  have htrace : WordTrace (prefixWord ++ tailWord_1796530) baseStart_1796530 baseEnd_1796530 := by
    simpa [prefixWord, tailWord_1796530, baseEnd_1796530] using wordTrace_append hprefix tailTrace_1796530
  have hstable : (prefixWord ++ tailWord_1796530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796530).length < 2 ^ (prefixWord ++ tailWord_1796530).sum := by decide
  have hdescent : baseEnd_1796530 < baseStart_1796530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796564 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1796564 : Nat := 118140960795 + 1796564 * 2 ^ 59
def prefixEnd_1796564 : Nat := 4983230072969 + 3 ^ 40 * 1796564 * 2
def baseEnd_1796564 : Nat := 922500858564214168787759

theorem tailTrace_1796564 : CollatzResearch.WordTrace tailWord_1796564 prefixEnd_1796564 922500858564214168787759 := by
  unfold tailWord_1796564
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763036131681465774214373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43684048175575287698952497 32763036131681465774214373)
  ·
    refine ⟨6143069274690274832665195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32763036131681465774214373 6143069274690274832665195)
    ·
      refine ⟨9214603912035412248997793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6143069274690274832665195 9214603912035412248997793)
      ·
        refine ⟨6910952934026559186748345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9214603912035412248997793 6910952934026559186748345)
        ·
          refine ⟨5183214700519919390061259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6910952934026559186748345 5183214700519919390061259)
          ·
            refine ⟨7774822050779879085091889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183214700519919390061259 7774822050779879085091889)
            ·
              refine ⟨5831116538084909313818917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774822050779879085091889 5831116538084909313818917)
              ·
                refine ⟨1093334350890920496341047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5831116538084909313818917 1093334350890920496341047)
                ·
                  refine ⟨1640001526336380744511571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093334350890920496341047 1640001526336380744511571)
                  ·
                    refine ⟨2460002289504571116767357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640001526336380744511571 2460002289504571116767357)
                    ·
                      refine ⟨922500858564214168787759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2460002289504571116767357 922500858564214168787759)
                      ·
                        rfl

theorem cell23_1796564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1796564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796564 prefixEnd_1796564 := by exact prefixLift 1796564
  have htrace : WordTrace (prefixWord ++ tailWord_1796564) baseStart_1796564 baseEnd_1796564 := by
    simpa [prefixWord, tailWord_1796564, baseEnd_1796564] using wordTrace_append hprefix tailTrace_1796564
  have hstable : (prefixWord ++ tailWord_1796564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796564).length < 2 ^ (prefixWord ++ tailWord_1796564).sum := by decide
  have hdescent : baseEnd_1796564 < baseStart_1796564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796576 : List Nat := [2, 1, 1, 3, 1, 1, 4, 10]
def baseStart_1796576 : Nat := 118140960795 + 1796576 * 2 ^ 59
def prefixEnd_1796576 : Nat := 4983230072969 + 3 ^ 40 * 1796576 * 2
def baseEnd_1796576 : Nat := 34166926678965485993989

theorem tailTrace_1796576 : CollatzResearch.WordTrace tailWord_1796576 prefixEnd_1796576 34166926678965485993989 := by
  unfold tailWord_1796576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763254969659728798932791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43684339959546305065243721 32763254969659728798932791)
  ·
    refine ⟨49144882454489593198399187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32763254969659728798932791 49144882454489593198399187)
    ·
      refine ⟨73717323681734389797598781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49144882454489593198399187 73717323681734389797598781)
      ·
        refine ⟨27643996380650396174099543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73717323681734389797598781 27643996380650396174099543)
        ·
          refine ⟨41465994570975594261149315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27643996380650396174099543 41465994570975594261149315)
          ·
            refine ⟨62198991856463391391723973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41465994570975594261149315 62198991856463391391723973)
            ·
              refine ⟨11662310973086885885948245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62198991856463391391723973 11662310973086885885948245)
              ·
                refine ⟨34166926678965485993989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11662310973086885885948245 34166926678965485993989)
                ·
                  rfl

theorem cell23_1796576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 10].length) (baseStart_1796576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796576 prefixEnd_1796576 := by exact prefixLift 1796576
  have htrace : WordTrace (prefixWord ++ tailWord_1796576) baseStart_1796576 baseEnd_1796576 := by
    simpa [prefixWord, tailWord_1796576, baseEnd_1796576] using wordTrace_append hprefix tailTrace_1796576
  have hstable : (prefixWord ++ tailWord_1796576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796576).length < 2 ^ (prefixWord ++ tailWord_1796576).sum := by decide
  have hdescent : baseEnd_1796576 < baseStart_1796576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796583 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1796583 : Nat := 118140960795 + 1796583 * 2 ^ 59
def prefixEnd_1796583 : Nat := 4983230072969 + 3 ^ 40 * 1796583 * 2
def baseEnd_1796583 : Nat := 922510614696649594450171

theorem tailTrace_1796583 : CollatzResearch.WordTrace tailWord_1796583 prefixEnd_1796583 922510614696649594450171 := by
  unfold tailWord_1796583
  simp only [CollatzResearch.WordTrace]
  refine ⟨65526765250294097793370403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43684510166862731862246935 65526765250294097793370403)
  ·
    refine ⟨98290147875441146690055605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65526765250294097793370403 98290147875441146690055605)
    ·
      refine ⟨9214701363322607502192713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98290147875441146690055605 9214701363322607502192713)
      ·
        refine ⟨6911026022491955626644535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9214701363322607502192713 6911026022491955626644535)
        ·
          refine ⟨10366539033737933439966803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911026022491955626644535 10366539033737933439966803)
          ·
            refine ⟨15549808550606900159950205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366539033737933439966803 15549808550606900159950205)
            ·
              refine ⟨5831178206477587559981327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15549808550606900159950205 5831178206477587559981327)
              ·
                refine ⟨8746767309716381339971991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831178206477587559981327 8746767309716381339971991)
                ·
                  refine ⟨13120150964574572009957987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746767309716381339971991 13120150964574572009957987)
                  ·
                    refine ⟨19680226446861858014936981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13120150964574572009957987 19680226446861858014936981)
                    ·
                      refine ⟨922510614696649594450171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19680226446861858014936981 922510614696649594450171)
                      ·
                        rfl

theorem cell23_1796583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1796583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796583 prefixEnd_1796583 := by exact prefixLift 1796583
  have htrace : WordTrace (prefixWord ++ tailWord_1796583) baseStart_1796583 baseEnd_1796583 := by
    simpa [prefixWord, tailWord_1796583, baseEnd_1796583] using wordTrace_append hprefix tailTrace_1796583
  have hstable : (prefixWord ++ tailWord_1796583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796583).length < 2 ^ (prefixWord ++ tailWord_1796583).sum := by decide
  have hdescent : baseEnd_1796583 < baseStart_1796583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796631 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 2, 4]
def baseStart_1796631 : Nat := 118140960795 + 1796631 * 2 ^ 59
def prefixEnd_1796631 : Nat := 4983230072969 + 3 ^ 40 * 1796631 * 2
def baseEnd_1796631 : Nat := 307511753922688468883317

theorem tailTrace_1796631 : CollatzResearch.WordTrace tailWord_1796631 prefixEnd_1796631 307511753922688468883317 := by
  unfold tailWord_1796631
  simp only [CollatzResearch.WordTrace]
  refine ⟨65528515954120201991117747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43685677302746801327411831 65528515954120201991117747)
  ·
    refine ⟨98292773931180302986676621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65528515954120201991117747 98292773931180302986676621)
    ·
      refine ⟨36859790224192613620003733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98292773931180302986676621 36859790224192613620003733)
      ·
        refine ⟨1727802666759028763437675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36859790224192613620003733 1727802666759028763437675)
        ·
          refine ⟨2591704000138543145156513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727802666759028763437675 2591704000138543145156513)
          ·
            refine ⟨1943778000103907358867385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591704000138543145156513 1943778000103907358867385)
            ·
              refine ⟨1457833500077930519150539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943778000103907358867385 1457833500077930519150539)
              ·
                refine ⟨2186750250116895778725809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457833500077930519150539 2186750250116895778725809)
                ·
                  refine ⟨1640062687587671834044357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186750250116895778725809 1640062687587671834044357)
                  ·
                    refine ⟨307511753922688468883317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1640062687587671834044357 307511753922688468883317)
                    ·
                      rfl

theorem cell23_1796631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_1796631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796631 prefixEnd_1796631 := by exact prefixLift 1796631
  have htrace : WordTrace (prefixWord ++ tailWord_1796631) baseStart_1796631 baseEnd_1796631 := by
    simpa [prefixWord, tailWord_1796631, baseEnd_1796631] using wordTrace_append hprefix tailTrace_1796631
  have hstable : (prefixWord ++ tailWord_1796631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796631).length < 2 ^ (prefixWord ++ tailWord_1796631).sum := by decide
  have hdescent : baseEnd_1796631 < baseStart_1796631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796663 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1796663 : Nat := 118140960795 + 1796663 * 2 ^ 59
def prefixEnd_1796663 : Nat := 4983230072969 + 3 ^ 40 * 1796663 * 2
def baseEnd_1796663 : Nat := 922551693149009281449803

theorem tailTrace_1796663 : CollatzResearch.WordTrace tailWord_1796663 prefixEnd_1796663 922551693149009281449803 := by
  unfold tailWord_1796663
  simp only [CollatzResearch.WordTrace]
  refine ⟨65529683090004271456282643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43686455393336180970855095 65529683090004271456282643)
  ·
    refine ⟨98294524635006407184423965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65529683090004271456282643 98294524635006407184423965)
    ·
      refine ⟨36860446738127402694158987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98294524635006407184423965 36860446738127402694158987)
      ·
        refine ⟨55290670107191104041238481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36860446738127402694158987 55290670107191104041238481)
        ·
          refine ⟨41468002580393328030928861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55290670107191104041238481 41468002580393328030928861)
          ·
            refine ⟨15550500967647498011598323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41468002580393328030928861 15550500967647498011598323)
            ·
              refine ⟨23325751451471247017397485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15550500967647498011598323 23325751451471247017397485)
              ·
                refine ⟨8747156794301717631524057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23325751451471247017397485 8747156794301717631524057)
                ·
                  refine ⟨6560367595726288223643043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747156794301717631524057 6560367595726288223643043)
                  ·
                    refine ⟨9840551393589432335464565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560367595726288223643043 9840551393589432335464565)
                    ·
                      refine ⟨922551693149009281449803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9840551393589432335464565 922551693149009281449803)
                      ·
                        rfl

theorem cell23_1796663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1796663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796663 prefixEnd_1796663 := by exact prefixLift 1796663
  have htrace : WordTrace (prefixWord ++ tailWord_1796663) baseStart_1796663 baseEnd_1796663 := by
    simpa [prefixWord, tailWord_1796663, baseEnd_1796663] using wordTrace_append hprefix tailTrace_1796663
  have hstable : (prefixWord ++ tailWord_1796663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796663).length < 2 ^ (prefixWord ++ tailWord_1796663).sum := by decide
  have hdescent : baseEnd_1796663 < baseStart_1796663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796664 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_1796664 : Nat := 118140960795 + 1796664 * 2 ^ 59
def prefixEnd_1796664 : Nat := 4983230072969 + 3 ^ 40 * 1796664 * 2
def baseEnd_1796664 : Nat := 922552206629663777537299

theorem tailTrace_1796664 : CollatzResearch.WordTrace tailWord_1796664 prefixEnd_1796664 922552206629663777537299 := by
  unfold tailWord_1796664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32764859781500324313534523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43686479708667099084712697 32764859781500324313534523)
  ·
    refine ⟨49147289672250486470301785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32764859781500324313534523 49147289672250486470301785)
    ·
      refine ⟨36860467254187864852726339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49147289672250486470301785 36860467254187864852726339)
      ·
        refine ⟨55290700881281797279089509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36860467254187864852726339 55290700881281797279089509)
        ·
          refine ⟨10367006415240336989829283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55290700881281797279089509 10367006415240336989829283)
          ·
            refine ⟨15550509622860505484743925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367006415240336989829283 15550509622860505484743925)
            ·
              refine ⟨1457860277143172389194743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15550509622860505484743925 1457860277143172389194743)
              ·
                refine ⟨2186790415714758583792115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457860277143172389194743 2186790415714758583792115)
                ·
                  refine ⟨3280185623572137875688173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186790415714758583792115 3280185623572137875688173)
                  ·
                    refine ⟨1230069608839551703383065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280185623572137875688173 1230069608839551703383065)
                    ·
                      refine ⟨922552206629663777537299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230069608839551703383065 922552206629663777537299)
                      ·
                        rfl

theorem cell23_1796664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_1796664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796664 prefixEnd_1796664 := by exact prefixLift 1796664
  have htrace : WordTrace (prefixWord ++ tailWord_1796664) baseStart_1796664 baseEnd_1796664 := by
    simpa [prefixWord, tailWord_1796664, baseEnd_1796664] using wordTrace_append hprefix tailTrace_1796664
  have hstable : (prefixWord ++ tailWord_1796664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796664).length < 2 ^ (prefixWord ++ tailWord_1796664).sum := by decide
  have hdescent : baseEnd_1796664 < baseStart_1796664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796690 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1796690 : Nat := 118140960795 + 1796690 * 2 ^ 59
def prefixEnd_1796690 : Nat := 4983230072969 + 3 ^ 40 * 1796690 * 2
def baseEnd_1796690 : Nat := 922565557126680675812179

theorem tailTrace_1796690 : CollatzResearch.WordTrace tailWord_1796690 prefixEnd_1796690 922565557126680675812179 := by
  unfold tailWord_1796690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16382666965226613766878881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43687111907270970045010349 16382666965226613766878881)
  ·
    refine ⟨12287000223919960325159161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16382666965226613766878881 12287000223919960325159161)
    ·
      refine ⟨9215250167939970243869371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12287000223919960325159161 9215250167939970243869371)
      ·
        refine ⟨13822875251909955365804057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9215250167939970243869371 13822875251909955365804057)
        ·
          refine ⟨10367156438932466524353043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13822875251909955365804057 10367156438932466524353043)
          ·
            refine ⟨15550734658398699786529565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367156438932466524353043 15550734658398699786529565)
            ·
              refine ⟨5831525496899512419948587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15550734658398699786529565 5831525496899512419948587)
              ·
                refine ⟨8747288245349268629922881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5831525496899512419948587 8747288245349268629922881)
                ·
                  refine ⟨6560466184011951472442161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8747288245349268629922881 6560466184011951472442161)
                  ·
                    refine ⟨4920349638008963604331621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560466184011951472442161 4920349638008963604331621)
                    ·
                      refine ⟨922565557126680675812179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4920349638008963604331621 922565557126680675812179)
                      ·
                        rfl

theorem cell23_1796690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1796690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796690 prefixEnd_1796690 := by exact prefixLift 1796690
  have htrace : WordTrace (prefixWord ++ tailWord_1796690) baseStart_1796690 baseEnd_1796690 := by
    simpa [prefixWord, tailWord_1796690, baseEnd_1796690] using wordTrace_append hprefix tailTrace_1796690
  have hstable : (prefixWord ++ tailWord_1796690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796690).length < 2 ^ (prefixWord ++ tailWord_1796690).sum := by decide
  have hdescent : baseEnd_1796690 < baseStart_1796690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796717 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1796717 : Nat := 118140960795 + 1796717 * 2 ^ 59
def prefixEnd_1796717 : Nat := 4983230072969 + 3 ^ 40 * 1796717 * 2
def baseEnd_1796717 : Nat := 102508824567150230019395

theorem tailTrace_1796717 : CollatzResearch.WordTrace tailWord_1796717 prefixEnd_1796717 102508824567150230019395 := by
  unfold tailWord_1796717
  simp only [CollatzResearch.WordTrace]
  refine ⟨65531652631808638678748405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43687768421205759119165603 65531652631808638678748405)
  ·
    refine ⟨6143592434232059876132663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65531652631808638678748405 6143592434232059876132663)
    ·
      refine ⟨9215388651348089814198995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6143592434232059876132663 9215388651348089814198995)
      ·
        refine ⟨13823082977022134721298493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9215388651348089814198995 13823082977022134721298493)
        ·
          refine ⟨5183656116383300520486935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13823082977022134721298493 5183656116383300520486935)
          ·
            refine ⟨7775484174574950780730403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183656116383300520486935 7775484174574950780730403)
            ·
              refine ⟨11663226261862426171095605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775484174574950780730403 11663226261862426171095605)
              ·
                refine ⟨1093427462049602453540213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11663226261862426171095605 1093427462049602453540213)
                ·
                  refine ⟨102508824567150230019395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1093427462049602453540213 102508824567150230019395)
                  ·
                    rfl

theorem cell23_1796717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1796717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796717 prefixEnd_1796717 := by exact prefixLift 1796717
  have htrace : WordTrace (prefixWord ++ tailWord_1796717) baseStart_1796717 baseEnd_1796717 := by
    simpa [prefixWord, tailWord_1796717, baseEnd_1796717] using wordTrace_append hprefix tailTrace_1796717
  have hstable : (prefixWord ++ tailWord_1796717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796717).length < 2 ^ (prefixWord ++ tailWord_1796717).sum := by decide
  have hdescent : baseEnd_1796717 < baseStart_1796717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796723 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_1796723 : Nat := 118140960795 + 1796723 * 2 ^ 59
def prefixEnd_1796723 : Nat := 4983230072969 + 3 ^ 40 * 1796723 * 2
def baseEnd_1796723 : Nat := 922582501988279046699527

theorem tailTrace_1796723 : CollatzResearch.WordTrace tailWord_1796723 prefixEnd_1796723 922582501988279046699527 := by
  unfold tailWord_1796723
  simp only [CollatzResearch.WordTrace]
  refine ⟨65531871469786901703466823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43687914313191267802311215 65531871469786901703466823)
  ·
    refine ⟨98297807204680352555200235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65531871469786901703466823 98297807204680352555200235)
    ·
      refine ⟨147446710807020528832800353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98297807204680352555200235 147446710807020528832800353)
      ·
        refine ⟨110585033105265396624600265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147446710807020528832800353 110585033105265396624600265)
        ·
          refine ⟨82938774828949047468450199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110585033105265396624600265 82938774828949047468450199)
          ·
            refine ⟨124408162243423571202675299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82938774828949047468450199 124408162243423571202675299)
            ·
              refine ⟨186612243365135356804012949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124408162243423571202675299 186612243365135356804012949)
              ·
                refine ⟨8747448907740719850188107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186612243365135356804012949 8747448907740719850188107)
                ·
                  refine ⟨13121173361611079775282161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8747448907740719850188107 13121173361611079775282161)
                  ·
                    refine ⟨9840880021208309831461621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13121173361611079775282161 9840880021208309831461621)
                    ·
                      refine ⟨922582501988279046699527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9840880021208309831461621 922582501988279046699527)
                      ·
                        rfl

theorem cell23_1796723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_1796723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796723 prefixEnd_1796723 := by exact prefixLift 1796723
  have htrace : WordTrace (prefixWord ++ tailWord_1796723) baseStart_1796723 baseEnd_1796723 := by
    simpa [prefixWord, tailWord_1796723, baseEnd_1796723] using wordTrace_append hprefix tailTrace_1796723
  have hstable : (prefixWord ++ tailWord_1796723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796723).length < 2 ^ (prefixWord ++ tailWord_1796723).sum := by decide
  have hdescent : baseEnd_1796723 < baseStart_1796723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796750 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1796750 : Nat := 118140960795 + 1796750 * 2 ^ 59
def prefixEnd_1796750 : Nat := 4983230072969 + 3 ^ 40 * 1796750 * 2
def baseEnd_1796750 : Nat := 922596365965950441061903

theorem tailTrace_1796750 : CollatzResearch.WordTrace tailWord_1796750 prefixEnd_1796750 922596365965950441061903 := by
  unfold tailWord_1796750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191607030086135664337463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43688570827126056876466469 8191607030086135664337463)
  ·
    refine ⟨12287410545129203496506195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8191607030086135664337463 12287410545129203496506195)
    ·
      refine ⟨18431115817693805244759293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12287410545129203496506195 18431115817693805244759293)
      ·
        refine ⟨6911668431635176966784735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18431115817693805244759293 6911668431635176966784735)
        ·
          refine ⟨10367502647452765450177103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911668431635176966784735 10367502647452765450177103)
          ·
            refine ⟨15551253971179148175265655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367502647452765450177103 15551253971179148175265655)
            ·
              refine ⟨23326880956768722262898483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15551253971179148175265655 23326880956768722262898483)
              ·
                refine ⟨34990321435153083394347725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23326880956768722262898483 34990321435153083394347725)
                ·
                  refine ⟨13121370538182406272880397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34990321435153083394347725 13121370538182406272880397)
                  ·
                    refine ⟨4920513951818402352330149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13121370538182406272880397 4920513951818402352330149)
                    ·
                      refine ⟨922596365965950441061903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4920513951818402352330149 922596365965950441061903)
                      ·
                        rfl

theorem cell23_1796750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1796750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796750 prefixEnd_1796750 := by exact prefixLift 1796750
  have htrace : WordTrace (prefixWord ++ tailWord_1796750) baseStart_1796750 baseEnd_1796750 := by
    simpa [prefixWord, tailWord_1796750, baseEnd_1796750] using wordTrace_append hprefix tailTrace_1796750
  have hstable : (prefixWord ++ tailWord_1796750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796750).length < 2 ^ (prefixWord ++ tailWord_1796750).sum := by decide
  have hdescent : baseEnd_1796750 < baseStart_1796750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796753 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1796753 : Nat := 118140960795 + 1796753 * 2 ^ 59
def prefixEnd_1796753 : Nat := 4983230072969 + 3 ^ 40 * 1796753 * 2
def baseEnd_1796753 : Nat := 922597906407913929324389

theorem tailTrace_1796753 : CollatzResearch.WordTrace tailWord_1796753 prefixEnd_1796753 922597906407913929324389 := by
  unfold tailWord_1796753
  simp only [CollatzResearch.WordTrace]
  refine ⟨65532965659678216827058913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43688643773118811218039275 65532965659678216827058913)
  ·
    refine ⟨49149724244758662620294185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65532965659678216827058913 49149724244758662620294185)
    ·
      refine ⟨36862293183568996965220639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49149724244758662620294185 36862293183568996965220639)
      ·
        refine ⟨55293439775353495447830959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36862293183568996965220639 55293439775353495447830959)
        ·
          refine ⟨82940159663030243171746439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55293439775353495447830959 82940159663030243171746439)
          ·
            refine ⟨124410239494545364757619659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82940159663030243171746439 124410239494545364757619659)
            ·
              refine ⟨186615359241818047136429489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124410239494545364757619659 186615359241818047136429489)
              ·
                refine ⟨139961519431363535352322117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186615359241818047136429489 139961519431363535352322117)
                ·
                  refine ⟨26242784893380662878560397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139961519431363535352322117 26242784893380662878560397)
                  ·
                    refine ⟨9841044335017748579460149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26242784893380662878560397 9841044335017748579460149)
                    ·
                      refine ⟨922597906407913929324389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9841044335017748579460149 922597906407913929324389)
                      ·
                        rfl

theorem cell23_1796753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1796753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796753 prefixEnd_1796753 := by exact prefixLift 1796753
  have htrace : WordTrace (prefixWord ++ tailWord_1796753) baseStart_1796753 baseEnd_1796753 := by
    simpa [prefixWord, tailWord_1796753, baseEnd_1796753] using wordTrace_append hprefix tailTrace_1796753
  have hstable : (prefixWord ++ tailWord_1796753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796753).length < 2 ^ (prefixWord ++ tailWord_1796753).sum := by decide
  have hdescent : baseEnd_1796753 < baseStart_1796753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796787 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3]
def baseStart_1796787 : Nat := 118140960795 + 1796787 * 2 ^ 59
def prefixEnd_1796787 : Nat := 4983230072969 + 3 ^ 40 * 1796787 * 2
def baseEnd_1796787 : Nat := 922615364750166796299233

theorem tailTrace_1796787 : CollatzResearch.WordTrace tailWord_1796787 prefixEnd_1796787 922615364750166796299233 := by
  unfold tailWord_1796787
  simp only [CollatzResearch.WordTrace]
  refine ⟨65534205741555040633796615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43689470494370027089197743 65534205741555040633796615)
  ·
    refine ⟨98301308612332560950694923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65534205741555040633796615 98301308612332560950694923)
    ·
      refine ⟨147451962918498841426042385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98301308612332560950694923 147451962918498841426042385)
      ·
        refine ⟨110588972188874131069531789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147451962918498841426042385 110588972188874131069531789)
        ·
          refine ⟨41470864570827799151074421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110588972188874131069531789 41470864570827799151074421)
          ·
            refine ⟨3887893553515106170413227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41470864570827799151074421 3887893553515106170413227)
            ·
              refine ⟨5831840330272659255619841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887893553515106170413227 5831840330272659255619841)
              ·
                refine ⟨4373880247704494441714881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5831840330272659255619841 4373880247704494441714881)
                ·
                  refine ⟨3280410185778370831286161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373880247704494441714881 3280410185778370831286161)
                  ·
                    refine ⟨2460307639333778123464621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3280410185778370831286161 2460307639333778123464621)
                    ·
                      refine ⟨922615364750166796299233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2460307639333778123464621 922615364750166796299233)
                      ·
                        rfl

theorem cell23_1796787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_1796787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796787 prefixEnd_1796787 := by exact prefixLift 1796787
  have htrace : WordTrace (prefixWord ++ tailWord_1796787) baseStart_1796787 baseEnd_1796787 := by
    simpa [prefixWord, tailWord_1796787, baseEnd_1796787] using wordTrace_append hprefix tailTrace_1796787
  have hstable : (prefixWord ++ tailWord_1796787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796787).length < 2 ^ (prefixWord ++ tailWord_1796787).sum := by decide
  have hdescent : baseEnd_1796787 < baseStart_1796787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796817 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_1796817 : Nat := 118140960795 + 1796817 * 2 ^ 59
def prefixEnd_1796817 : Nat := 4983230072969 + 3 ^ 40 * 1796817 * 2
def baseEnd_1796817 : Nat := 922630769169801678924095

theorem tailTrace_1796817 : CollatzResearch.WordTrace tailWord_1796817 prefixEnd_1796817 922630769169801678924095 := by
  unfold tailWord_1796817
  simp only [CollatzResearch.WordTrace]
  refine ⟨65535299931446355757388705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43690199954297570504925803 65535299931446355757388705)
  ·
    refine ⟨49151474948584766818041529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65535299931446355757388705 49151474948584766818041529)
    ·
      refine ⟨36863606211438575113531147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49151474948584766818041529 36863606211438575113531147)
      ·
        refine ⟨55295409317157862670296721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36863606211438575113531147 55295409317157862670296721)
        ·
          refine ⟨41471556987868397002722541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55295409317157862670296721 41471556987868397002722541)
          ·
            refine ⟨15551833870450648876020953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41471556987868397002722541 15551833870450648876020953)
            ·
              refine ⟨11663875402837986657015715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15551833870450648876020953 11663875402837986657015715)
              ·
                refine ⟨17495813104256979985523573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11663875402837986657015715 17495813104256979985523573)
                ·
                  refine ⟨1640232478524091873642835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17495813104256979985523573 1640232478524091873642835)
                  ·
                    refine ⟨2460348717786137810464253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640232478524091873642835 2460348717786137810464253)
                    ·
                      refine ⟨922630769169801678924095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2460348717786137810464253 922630769169801678924095)
                      ·
                        rfl

theorem cell23_1796817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_1796817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796817 prefixEnd_1796817 := by exact prefixLift 1796817
  have htrace : WordTrace (prefixWord ++ tailWord_1796817) baseStart_1796817 baseEnd_1796817 := by
    simpa [prefixWord, tailWord_1796817, baseEnd_1796817] using wordTrace_append hprefix tailTrace_1796817
  have hstable : (prefixWord ++ tailWord_1796817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796817).length < 2 ^ (prefixWord ++ tailWord_1796817).sum := by decide
  have hdescent : baseEnd_1796817 < baseStart_1796817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796821 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1796821 : Nat := 118140960795 + 1796821 * 2 ^ 59
def prefixEnd_1796821 : Nat := 4983230072969 + 3 ^ 40 * 1796821 * 2
def baseEnd_1796821 : Nat := 922632823092419663274077

theorem tailTrace_1796821 : CollatzResearch.WordTrace tailWord_1796821 prefixEnd_1796821 922632823092419663274077 := by
  unfold tailWord_1796821
  simp only [CollatzResearch.WordTrace]
  refine ⟨65535445823431864440534317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43690297215621242960356211 65535445823431864440534317)
  ·
    refine ⟨24575792183786949165200369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65535445823431864440534317 24575792183786949165200369)
    ·
      refine ⟨18431844137840211873900277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24575792183786949165200369 18431844137840211873900277)
      ·
        refine ⟨1727985387922519863178151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18431844137840211873900277 1727985387922519863178151)
        ·
          refine ⟨2591978081883779794767227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727985387922519863178151 2591978081883779794767227)
          ·
            refine ⟨3887967122825669692150841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591978081883779794767227 3887967122825669692150841)
            ·
              refine ⟨2915975342119252269113131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887967122825669692150841 2915975342119252269113131)
              ·
                refine ⟨4373963013178878403669697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915975342119252269113131 4373963013178878403669697)
                ·
                  refine ⟨3280472259884158802752273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373963013178878403669697 3280472259884158802752273)
                  ·
                    refine ⟨2460354194913119102064205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3280472259884158802752273 2460354194913119102064205)
                    ·
                      refine ⟨922632823092419663274077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2460354194913119102064205 922632823092419663274077)
                      ·
                        rfl

theorem cell23_1796821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1796821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796821 prefixEnd_1796821 := by exact prefixLift 1796821
  have htrace : WordTrace (prefixWord ++ tailWord_1796821) baseStart_1796821 baseEnd_1796821 := by
    simpa [prefixWord, tailWord_1796821, baseEnd_1796821] using wordTrace_append hprefix tailTrace_1796821
  have hstable : (prefixWord ++ tailWord_1796821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796821).length < 2 ^ (prefixWord ++ tailWord_1796821).sum := by decide
  have hdescent : baseEnd_1796821 < baseStart_1796821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796918 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1796918 : Nat := 118140960795 + 1796918 * 2 ^ 59
def prefixEnd_1796918 : Nat := 4983230072969 + 3 ^ 40 * 1796918 * 2
def baseEnd_1796918 : Nat := 307560876905301927920377

theorem tailTrace_1796918 : CollatzResearch.WordTrace tailWord_1796918 prefixEnd_1796918 307560876905301927920377 := by
  unfold tailWord_1796918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096186481505028125425963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43692655802720300004543605 4096186481505028125425963)
  ·
    refine ⟨6144279722257542188138945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096186481505028125425963 6144279722257542188138945)
    ·
      refine ⟨4608209791693156641104209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6144279722257542188138945 4608209791693156641104209)
      ·
        refine ⟨3456157343769867480828157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608209791693156641104209 3456157343769867480828157)
        ·
          refine ⟨1296059003913700305310559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3456157343769867480828157 1296059003913700305310559)
          ·
            refine ⟨1944088505870550457965839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296059003913700305310559 1944088505870550457965839)
            ·
              refine ⟨2916132758805825686948759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944088505870550457965839 2916132758805825686948759)
              ·
                refine ⟨4374199138208738530423139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916132758805825686948759 4374199138208738530423139)
                ·
                  refine ⟨6561298707313107795634709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374199138208738530423139 6561298707313107795634709)
                  ·
                    refine ⟨307560876905301927920377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6561298707313107795634709 307560876905301927920377)
                    ·
                      rfl

theorem cell23_1796918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1796918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796918 prefixEnd_1796918 := by exact prefixLift 1796918
  have htrace : WordTrace (prefixWord ++ tailWord_1796918) baseStart_1796918 baseEnd_1796918 := by
    simpa [prefixWord, tailWord_1796918, baseEnd_1796918] using wordTrace_append hprefix tailTrace_1796918
  have hstable : (prefixWord ++ tailWord_1796918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796918).length < 2 ^ (prefixWord ++ tailWord_1796918).sum := by decide
  have hdescent : baseEnd_1796918 < baseStart_1796918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1796951 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_1796951 : Nat := 118140960795 + 1796951 * 2 ^ 59
def prefixEnd_1796951 : Nat := 4983230072969 + 3 ^ 40 * 1796951 * 2
def baseEnd_1796951 : Nat := 922699575577504154648479

theorem tailTrace_1796951 : CollatzResearch.WordTrace tailWord_1796951 prefixEnd_1796951 922699575577504154648479 := by
  unfold tailWord_1796951
  simp only [CollatzResearch.WordTrace]
  refine ⟨65540187312960896642766707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43693458208640597761844471 65540187312960896642766707)
  ·
    refine ⟨98310280969441344964150061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65540187312960896642766707 98310280969441344964150061)
    ·
      refine ⟨36866355363540504361556273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98310280969441344964150061 36866355363540504361556273)
      ·
        refine ⟨27649766522655378271167205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36866355363540504361556273 27649766522655378271167205)
        ·
          refine ⟨5184331222997883425843851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27649766522655378271167205 5184331222997883425843851)
          ·
            refine ⟨7776496834496825138765777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184331222997883425843851 7776496834496825138765777)
            ·
              refine ⟨5832372625872618854074333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7776496834496825138765777 5832372625872618854074333)
              ·
                refine ⟨2187139734702232070277875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5832372625872618854074333 2187139734702232070277875)
                ·
                  refine ⟨3280709602053348105416813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187139734702232070277875 3280709602053348105416813)
                  ·
                    refine ⟨1230266100770005539531305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280709602053348105416813 1230266100770005539531305)
                    ·
                      refine ⟨922699575577504154648479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230266100770005539531305 922699575577504154648479)
                      ·
                        rfl

theorem cell23_1796951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_1796951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1796951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1796951 prefixEnd_1796951 := by exact prefixLift 1796951
  have htrace : WordTrace (prefixWord ++ tailWord_1796951) baseStart_1796951 baseEnd_1796951 := by
    simpa [prefixWord, tailWord_1796951, baseEnd_1796951] using wordTrace_append hprefix tailTrace_1796951
  have hstable : (prefixWord ++ tailWord_1796951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1796951).length < 2 ^ (prefixWord ++ tailWord_1796951).sum := by decide
  have hdescent : baseEnd_1796951 < baseStart_1796951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1796951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797024 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2]
def baseStart_1797024 : Nat := 118140960795 + 1797024 * 2 ^ 59
def prefixEnd_1797024 : Nat := 4983230072969 + 3 ^ 40 * 1797024 * 2
def baseEnd_1797024 : Nat := 922737059665282369035643

theorem tailTrace_1797024 : CollatzResearch.WordTrace tailWord_1797024 prefixEnd_1797024 922737059665282369035643 := by
  unfold tailWord_1797024
  simp only [CollatzResearch.WordTrace]
  refine ⟨32771424920848215055087063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43695233227797620073449417 32771424920848215055087063)
  ·
    refine ⟨49157137381272322582630595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32771424920848215055087063 49157137381272322582630595)
    ·
      refine ⟨73735706071908483873945893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49157137381272322582630595 73735706071908483873945893)
      ·
        refine ⟨13825444888482840726364855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73735706071908483873945893 13825444888482840726364855)
        ·
          refine ⟨20738167332724261089547283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13825444888482840726364855 20738167332724261089547283)
          ·
            refine ⟨31107250999086391634320925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20738167332724261089547283 31107250999086391634320925)
            ·
              refine ⟨11665219124657396862870347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31107250999086391634320925 11665219124657396862870347)
              ·
                refine ⟨17497828686986095294305521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11665219124657396862870347 17497828686986095294305521)
                ·
                  refine ⟨13123371515239571470729141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17497828686986095294305521 13123371515239571470729141)
                  ·
                    refine ⟨1230316079553709825380857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13123371515239571470729141 1230316079553709825380857)
                    ·
                      refine ⟨922737059665282369035643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230316079553709825380857 922737059665282369035643)
                      ·
                        rfl

theorem cell23_1797024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_1797024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797024 prefixEnd_1797024 := by exact prefixLift 1797024
  have htrace : WordTrace (prefixWord ++ tailWord_1797024) baseStart_1797024 baseEnd_1797024 := by
    simpa [prefixWord, tailWord_1797024, baseEnd_1797024] using wordTrace_append hprefix tailTrace_1797024
  have hstable : (prefixWord ++ tailWord_1797024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797024).length < 2 ^ (prefixWord ++ tailWord_1797024).sum := by decide
  have hdescent : baseEnd_1797024 < baseStart_1797024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797027 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1797027 : Nat := 118140960795 + 1797027 * 2 ^ 59
def prefixEnd_1797027 : Nat := 4983230072969 + 3 ^ 40 * 1797027 * 2
def baseEnd_1797027 : Nat := 922738600107245857298129

theorem tailTrace_1797027 : CollatzResearch.WordTrace tailWord_1797027 prefixEnd_1797027 922738600107245857298129 := by
  unfold tailWord_1797027
  simp only [CollatzResearch.WordTrace]
  refine ⟨65542959260685561622533335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43695306173790374415022223 65542959260685561622533335)
  ·
    refine ⟨98314438891028342433800003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65542959260685561622533335 98314438891028342433800003)
    ·
      refine ⟨147471658336542513650700005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98314438891028342433800003 147471658336542513650700005)
      ·
        refine ⟨27650935938101721309506251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147471658336542513650700005 27650935938101721309506251)
        ·
          refine ⟨41476403907152581964259377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27650935938101721309506251 41476403907152581964259377)
          ·
            refine ⟨31107302930364436473194533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41476403907152581964259377 31107302930364436473194533)
            ·
              refine ⟨5832619299443331838723975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31107302930364436473194533 5832619299443331838723975)
              ·
                refine ⟨8748928949164997758085963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832619299443331838723975 8748928949164997758085963)
                ·
                  refine ⟨13123393423747496637128945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8748928949164997758085963 13123393423747496637128945)
                  ·
                    refine ⟨9842545067810622477846709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13123393423747496637128945 9842545067810622477846709)
                    ·
                      refine ⟨922738600107245857298129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9842545067810622477846709 922738600107245857298129)
                      ·
                        rfl

theorem cell23_1797027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1797027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797027 prefixEnd_1797027 := by exact prefixLift 1797027
  have htrace : WordTrace (prefixWord ++ tailWord_1797027) baseStart_1797027 baseEnd_1797027 := by
    simpa [prefixWord, tailWord_1797027, baseEnd_1797027] using wordTrace_append hprefix tailTrace_1797027
  have hstable : (prefixWord ++ tailWord_1797027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797027).length < 2 ^ (prefixWord ++ tailWord_1797027).sum := by decide
  have hdescent : baseEnd_1797027 < baseStart_1797027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797031 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1797031 : Nat := 118140960795 + 1797031 * 2 ^ 59
def prefixEnd_1797031 : Nat := 4983230072969 + 3 ^ 40 * 1797031 * 2
def baseEnd_1797031 : Nat := 922740654029863841648111

theorem tailTrace_1797031 : CollatzResearch.WordTrace tailWord_1797031 prefixEnd_1797031 922740654029863841648111 := by
  unfold tailWord_1797031
  simp only [CollatzResearch.WordTrace]
  refine ⟨65543105152671070305678947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43695403435114046870452631 65543105152671070305678947)
  ·
    refine ⟨98314657729006605458518421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65543105152671070305678947 98314657729006605458518421)
    ·
      refine ⟨4608499581047184630868051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98314657729006605458518421 4608499581047184630868051)
      ·
        refine ⟨6912749371570776946302077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608499581047184630868051 6912749371570776946302077)
        ·
          refine ⟨2592281014339041354863279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6912749371570776946302077 2592281014339041354863279)
          ·
            refine ⟨3888421521508562032294919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592281014339041354863279 3888421521508562032294919)
            ·
              refine ⟨5832632282262843048442379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888421521508562032294919 5832632282262843048442379)
              ·
                refine ⟨8748948423394264572663569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832632282262843048442379 8748948423394264572663569)
                ·
                  refine ⟨6561711317545698429497677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748948423394264572663569 6561711317545698429497677)
                  ·
                    refine ⟨2460641744079636911061629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6561711317545698429497677 2460641744079636911061629)
                    ·
                      refine ⟨922740654029863841648111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2460641744079636911061629 922740654029863841648111)
                      ·
                        rfl

theorem cell23_1797031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1797031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797031 prefixEnd_1797031 := by exact prefixLift 1797031
  have htrace : WordTrace (prefixWord ++ tailWord_1797031) baseStart_1797031 baseEnd_1797031 := by
    simpa [prefixWord, tailWord_1797031, baseEnd_1797031] using wordTrace_append hprefix tailTrace_1797031
  have hstable : (prefixWord ++ tailWord_1797031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797031).length < 2 ^ (prefixWord ++ tailWord_1797031).sum := by decide
  have hdescent : baseEnd_1797031 < baseStart_1797031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797054 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1797054 : Nat := 118140960795 + 1797054 * 2 ^ 59
def prefixEnd_1797054 : Nat := 4983230072969 + 3 ^ 40 * 1797054 * 2
def baseEnd_1797054 : Nat := 922752464084917251660505

theorem tailTrace_1797054 : CollatzResearch.WordTrace tailWord_1797054 prefixEnd_1797054 922752464084917251660505 := by
  unfold tailWord_1797054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192993003948468154220777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43695962687725163489177477 8192993003948468154220777)
  ·
    refine ⟨6144744752961351115665583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8192993003948468154220777 6144744752961351115665583)
    ·
      refine ⟨9217117129442026673498375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144744752961351115665583 9217117129442026673498375)
      ·
        refine ⟨13825675694163040010247563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217117129442026673498375 13825675694163040010247563)
        ·
          refine ⟨20738513541244560015371345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13825675694163040010247563 20738513541244560015371345)
          ·
            refine ⟨15553885155933420011528509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20738513541244560015371345 15553885155933420011528509)
            ·
              refine ⟨5832706933475032504323191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15553885155933420011528509 5832706933475032504323191)
              ·
                refine ⟨8749060400212548756484787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832706933475032504323191 8749060400212548756484787)
                ·
                  refine ⟨13123590600318823134727181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8749060400212548756484787 13123590600318823134727181)
                  ·
                    refine ⟨4921346475119558675522693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13123590600318823134727181 4921346475119558675522693)
                    ·
                      refine ⟨922752464084917251660505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4921346475119558675522693 922752464084917251660505)
                      ·
                        rfl

theorem cell23_1797054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1797054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797054 prefixEnd_1797054 := by exact prefixLift 1797054
  have htrace : WordTrace (prefixWord ++ tailWord_1797054) baseStart_1797054 baseEnd_1797054 := by
    simpa [prefixWord, tailWord_1797054, baseEnd_1797054] using wordTrace_append hprefix tailTrace_1797054
  have hstable : (prefixWord ++ tailWord_1797054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797054).length < 2 ^ (prefixWord ++ tailWord_1797054).sum := by decide
  have hdescent : baseEnd_1797054 < baseStart_1797054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797067 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_1797067 : Nat := 118140960795 + 1797067 * 2 ^ 59
def prefixEnd_1797067 : Nat := 4983230072969 + 3 ^ 40 * 1797067 * 2
def baseEnd_1797067 : Nat := 922759139333425700797945

theorem tailTrace_1797067 : CollatzResearch.WordTrace tailWord_1797067 prefixEnd_1797067 922759139333425700797945 := by
  unfold tailWord_1797067
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544418180540648453989455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43696278787027098969326303 65544418180540648453989455)
  ·
    refine ⟨98316627270810972680984183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65544418180540648453989455 98316627270810972680984183)
    ·
      refine ⟨147474940906216459021476275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98316627270810972680984183 147474940906216459021476275)
      ·
        refine ⟨221212411359324688532214413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147474940906216459021476275 221212411359324688532214413)
        ·
          refine ⟨82954654259746758199580405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221212411359324688532214413 82954654259746758199580405)
          ·
            refine ⟨7776998836851258581210663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82954654259746758199580405 7776998836851258581210663)
            ·
              refine ⟨11665498255276887871815995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7776998836851258581210663 11665498255276887871815995)
              ·
                refine ⟨17498247382915331807723993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11665498255276887871815995 17498247382915331807723993)
                ·
                  refine ⟨13123685537186498855792995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17498247382915331807723993 13123685537186498855792995)
                  ·
                    refine ⟨19685528305779748283689493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13123685537186498855792995 19685528305779748283689493)
                    ·
                      refine ⟨922759139333425700797945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19685528305779748283689493 922759139333425700797945)
                      ·
                        rfl

theorem cell23_1797067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_1797067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797067 prefixEnd_1797067 := by exact prefixLift 1797067
  have htrace : WordTrace (prefixWord ++ tailWord_1797067) baseStart_1797067 baseEnd_1797067 := by
    simpa [prefixWord, tailWord_1797067, baseEnd_1797067] using wordTrace_append hprefix tailTrace_1797067
  have hstable : (prefixWord ++ tailWord_1797067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797067).length < 2 ^ (prefixWord ++ tailWord_1797067).sum := by decide
  have hdescent : baseEnd_1797067 < baseStart_1797067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797081 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_1797081 : Nat := 118140960795 + 1797081 * 2 ^ 59
def prefixEnd_1797081 : Nat := 4983230072969 + 3 ^ 40 * 1797081 * 2
def baseEnd_1797081 : Nat := 307588776020862882007627

theorem tailTrace_1797081 : CollatzResearch.WordTrace tailWord_1797081 prefixEnd_1797081 307588776020862882007627 := by
  unfold tailWord_1797081
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544928802489928844999097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43696619201659952563332731 65544928802489928844999097)
  ·
    refine ⟨49158696601867446633749323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65544928802489928844999097 49158696601867446633749323)
    ·
      refine ⟨73738044902801169950623985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49158696601867446633749323 73738044902801169950623985)
      ·
        refine ⟨55303533677100877462967989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73738044902801169950623985 55303533677100877462967989)
        ·
          refine ⟨5184706282228207262153249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55303533677100877462967989 5184706282228207262153249)
          ·
            refine ⟨3888529711671155446614937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184706282228207262153249 3888529711671155446614937)
            ·
              refine ⟨2916397283753366584961203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888529711671155446614937 2916397283753366584961203)
              ·
                refine ⟨4374595925630049877441805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916397283753366584961203 4374595925630049877441805)
                ·
                  refine ⟨1640473472111268704040677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4374595925630049877441805 1640473472111268704040677)
                  ·
                    refine ⟨307588776020862882007627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1640473472111268704040677 307588776020862882007627)
                    ·
                      rfl

theorem cell23_1797081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_1797081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797081 prefixEnd_1797081 := by exact prefixLift 1797081
  have htrace : WordTrace (prefixWord ++ tailWord_1797081) baseStart_1797081 baseEnd_1797081 := by
    simpa [prefixWord, tailWord_1797081, baseEnd_1797081] using wordTrace_append hprefix tailTrace_1797081
  have hstable : (prefixWord ++ tailWord_1797081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797081).length < 2 ^ (prefixWord ++ tailWord_1797081).sum := by decide
  have hdescent : baseEnd_1797081 < baseStart_1797081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797131 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 4, 3, 2]
def baseStart_1797131 : Nat := 118140960795 + 1797131 * 2 ^ 59
def prefixEnd_1797131 : Nat := 4983230072969 + 3 ^ 40 * 1797131 * 2
def baseEnd_1797131 : Nat := 922792002095313450397651

theorem tailTrace_1797131 : CollatzResearch.WordTrace tailWord_1797131 prefixEnd_1797131 922792002095313450397651 := by
  unfold tailWord_1797131
  simp only [CollatzResearch.WordTrace]
  refine ⟨65546752452308787384319247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43697834968205858256212831 65546752452308787384319247)
  ·
    refine ⟨98320128678463181076478871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65546752452308787384319247 98320128678463181076478871)
    ·
      refine ⟨147480193017694771614718307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98320128678463181076478871 147480193017694771614718307)
      ·
        refine ⟨221220289526542157422077461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147480193017694771614718307 221220289526542157422077461)
        ·
          refine ⟨10369701071556663629159881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 221220289526542157422077461 10369701071556663629159881)
          ·
            refine ⟨7777275803667497721869911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10369701071556663629159881 7777275803667497721869911)
            ·
              refine ⟨11665913705501246582804867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777275803667497721869911 11665913705501246582804867)
              ·
                refine ⟨17498870558251869874207301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11665913705501246582804867 17498870558251869874207301)
                ·
                  refine ⟨3281038229672225601413869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17498870558251869874207301 3281038229672225601413869)
                  ·
                    refine ⟨1230389336127084600530201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281038229672225601413869 1230389336127084600530201)
                    ·
                      refine ⟨922792002095313450397651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230389336127084600530201 922792002095313450397651)
                      ·
                        rfl

theorem cell23_1797131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3, 2].length) (baseStart_1797131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797131 prefixEnd_1797131 := by exact prefixLift 1797131
  have htrace : WordTrace (prefixWord ++ tailWord_1797131) baseStart_1797131 baseEnd_1797131 := by
    simpa [prefixWord, tailWord_1797131, baseEnd_1797131] using wordTrace_append hprefix tailTrace_1797131
  have hstable : (prefixWord ++ tailWord_1797131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797131).length < 2 ^ (prefixWord ++ tailWord_1797131).sum := by decide
  have hdescent : baseEnd_1797131 < baseStart_1797131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797147 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_1797147 : Nat := 118140960795 + 1797147 * 2 ^ 59
def prefixEnd_1797147 : Nat := 4983230072969 + 3 ^ 40 * 1797147 * 2
def baseEnd_1797147 : Nat := 922800217785785387797577

theorem tailTrace_1797147 : CollatzResearch.WordTrace tailWord_1797147 prefixEnd_1797147 922800217785785387797577 := by
  unfold tailWord_1797147
  simp only [CollatzResearch.WordTrace]
  refine ⟨65547336020250822116901695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43698224013500548077934463 65547336020250822116901695)
  ·
    refine ⟨98321004030376233175352543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65547336020250822116901695 98321004030376233175352543)
    ·
      refine ⟨147481506045564349763028815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98321004030376233175352543 147481506045564349763028815)
      ·
        refine ⟨221222259068346524644543223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147481506045564349763028815 221222259068346524644543223)
        ·
          refine ⟨331833388602519786966814835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221222259068346524644543223 331833388602519786966814835)
          ·
            refine ⟨497750082903779680450222253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331833388602519786966814835 497750082903779680450222253)
            ·
              refine ⟨186656281088917380168833345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497750082903779680450222253 186656281088917380168833345)
              ·
                refine ⟨139992210816688035126625009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186656281088917380168833345 139992210816688035126625009)
                ·
                  refine ⟨104994158112516026344968757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139992210816688035126625009 104994158112516026344968757)
                  ·
                    refine ⟨9843202323048377469840821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104994158112516026344968757 9843202323048377469840821)
                    ·
                      refine ⟨922800217785785387797577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9843202323048377469840821 922800217785785387797577)
                      ·
                        rfl

theorem cell23_1797147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_1797147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797147 prefixEnd_1797147 := by exact prefixLift 1797147
  have htrace : WordTrace (prefixWord ++ tailWord_1797147) baseStart_1797147 baseEnd_1797147 := by
    simpa [prefixWord, tailWord_1797147, baseEnd_1797147] using wordTrace_append hprefix tailTrace_1797147
  have hstable : (prefixWord ++ tailWord_1797147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797147).length < 2 ^ (prefixWord ++ tailWord_1797147).sum := by decide
  have hdescent : baseEnd_1797147 < baseStart_1797147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797181 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1797181 : Nat := 118140960795 + 1797181 * 2 ^ 59
def prefixEnd_1797181 : Nat := 4983230072969 + 3 ^ 40 * 1797181 * 2
def baseEnd_1797181 : Nat := 922817676128038254772421

theorem tailTrace_1797181 : CollatzResearch.WordTrace tailWord_1797181 prefixEnd_1797181 922817676128038254772421 := by
  unfold tailWord_1797181
  simp only [CollatzResearch.WordTrace]
  refine ⟨65548576102127645923639397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43699050734751763949092931 65548576102127645923639397)
  ·
    refine ⟨12290358019148933610682387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65548576102127645923639397 12290358019148933610682387)
    ·
      refine ⟨18435537028723400416023581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12290358019148933610682387 18435537028723400416023581)
      ·
        refine ⟨6913326385771275156008843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18435537028723400416023581 6913326385771275156008843)
        ·
          refine ⟨10369989578656912734013265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913326385771275156008843 10369989578656912734013265)
          ·
            refine ⟨7777492183992684550509949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10369989578656912734013265 7777492183992684550509949)
            ·
              refine ⟨2916559568997256706441231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7777492183992684550509949 2916559568997256706441231)
              ·
                refine ⟨4374839353495885059661847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916559568997256706441231 4374839353495885059661847)
                ·
                  refine ⟨6562259030243827589492771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374839353495885059661847 6562259030243827589492771)
                  ·
                    refine ⟨9843388545365741384239157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6562259030243827589492771 9843388545365741384239157)
                    ·
                      refine ⟨922817676128038254772421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9843388545365741384239157 922817676128038254772421)
                      ·
                        rfl

theorem cell23_1797181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1797181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797181 prefixEnd_1797181 := by exact prefixLift 1797181
  have htrace : WordTrace (prefixWord ++ tailWord_1797181) baseStart_1797181 baseEnd_1797181 := by
    simpa [prefixWord, tailWord_1797181, baseEnd_1797181] using wordTrace_append hprefix tailTrace_1797181
  have hstable : (prefixWord ++ tailWord_1797181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797181).length < 2 ^ (prefixWord ++ tailWord_1797181).sum := by decide
  have hdescent : baseEnd_1797181 < baseStart_1797181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797204 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1797204 : Nat := 118140960795 + 1797204 * 2 ^ 59
def prefixEnd_1797204 : Nat := 4983230072969 + 3 ^ 40 * 1797204 * 2
def baseEnd_1797204 : Nat := 922829486183091664784815

theorem tailTrace_1797204 : CollatzResearch.WordTrace tailWord_1797204 prefixEnd_1797204 922829486183091664784815 := by
  unfold tailWord_1797204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32774707490522160425863333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43699609987362880567817777 32774707490522160425863333)
  ·
    refine ⟨6145257654472905079849375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32774707490522160425863333 6145257654472905079849375)
    ·
      refine ⟨9217886481709357619774063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145257654472905079849375 9217886481709357619774063)
      ·
        refine ⟨13826829722564036429661095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217886481709357619774063 13826829722564036429661095)
        ·
          refine ⟨20740244583846054644491643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826829722564036429661095 20740244583846054644491643)
          ·
            refine ⟨31110366875769081966737465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20740244583846054644491643 31110366875769081966737465)
            ·
              refine ⟨23332775156826811475053099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31110366875769081966737465 23332775156826811475053099)
              ·
                refine ⟨34999162735240217212579649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23332775156826811475053099 34999162735240217212579649)
                ·
                  refine ⟨26249372051430162909434737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34999162735240217212579649 26249372051430162909434737)
                  ·
                    refine ⟨19687029038572622182076053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26249372051430162909434737 19687029038572622182076053)
                    ·
                      refine ⟨922829486183091664784815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19687029038572622182076053 922829486183091664784815)
                      ·
                        rfl

theorem cell23_1797204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1797204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797204 prefixEnd_1797204 := by exact prefixLift 1797204
  have htrace : WordTrace (prefixWord ++ tailWord_1797204) baseStart_1797204 baseEnd_1797204 := by
    simpa [prefixWord, tailWord_1797204, baseEnd_1797204] using wordTrace_append hprefix tailTrace_1797204
  have hstable : (prefixWord ++ tailWord_1797204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797204).length < 2 ^ (prefixWord ++ tailWord_1797204).sum := by decide
  have hdescent : baseEnd_1797204 < baseStart_1797204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797218 : List Nat := [3, 3, 2, 2, 1, 2, 3, 7]
def baseStart_1797218 : Nat := 118140960795 + 1797218 * 2 ^ 59
def prefixEnd_1797218 : Nat := 4983230072969 + 3 ^ 40 * 1797218 * 2
def baseEnd_1797218 : Nat := 34179136107861281852213

theorem tailTrace_1797218 : CollatzResearch.WordTrace tailWord_1797218 prefixEnd_1797218 34179136107861281852213 := by
  unfold tailWord_1797218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16387481400748400310684077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43699950401995734161824205 16387481400748400310684077)
  ·
    refine ⟨6145305525280650116506529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16387481400748400310684077 6145305525280650116506529)
    ·
      refine ⟨4608979143960487587379897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6145305525280650116506529 4608979143960487587379897)
      ·
        refine ⟨3456734357970365690534923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608979143960487587379897 3456734357970365690534923)
        ·
          refine ⟨5185101536955548535802385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456734357970365690534923 5185101536955548535802385)
          ·
            refine ⟨3888826152716661401851789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185101536955548535802385 3888826152716661401851789)
            ·
              refine ⟨1458309807268748025694421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3888826152716661401851789 1458309807268748025694421)
              ·
                refine ⟨34179136107861281852213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1458309807268748025694421 34179136107861281852213)
                ·
                  rfl

theorem cell23_1797218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_1797218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797218 prefixEnd_1797218 := by exact prefixLift 1797218
  have htrace : WordTrace (prefixWord ++ tailWord_1797218) baseStart_1797218 baseEnd_1797218 := by
    simpa [prefixWord, tailWord_1797218, baseEnd_1797218] using wordTrace_append hprefix tailTrace_1797218
  have hstable : (prefixWord ++ tailWord_1797218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797218).length < 2 ^ (prefixWord ++ tailWord_1797218).sum := by decide
  have hdescent : baseEnd_1797218 < baseStart_1797218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797244 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1797244 : Nat := 118140960795 + 1797244 * 2 ^ 59
def prefixEnd_1797244 : Nat := 4983230072969 + 3 ^ 40 * 1797244 * 2
def baseEnd_1797244 : Nat := 307616675136423836094877

theorem tailTrace_1797244 : CollatzResearch.WordTrace tailWord_1797244 prefixEnd_1797244 307616675136423836094877 := by
  unfold tailWord_1797244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775436950449703841591393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43700582600599605122121857 32775436950449703841591393)
  ·
    refine ⟨24581577712837277881193545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32775436950449703841591393 24581577712837277881193545)
    ·
      refine ⟨18436183284627958410895159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24581577712837277881193545 18436183284627958410895159)
      ·
        refine ⟨27654274926941937616342739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18436183284627958410895159 27654274926941937616342739)
        ·
          refine ⟨41481412390412906424514109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27654274926941937616342739 41481412390412906424514109)
          ·
            refine ⟨15555529646404839909192791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41481412390412906424514109 15555529646404839909192791)
            ·
              refine ⟨23333294469607259863789187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15555529646404839909192791 23333294469607259863789187)
              ·
                refine ⟨34999941704410889795683781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23333294469607259863789187 34999941704410889795683781)
                ·
                  refine ⟨6562489069577041836690709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34999941704410889795683781 6562489069577041836690709)
                  ·
                    refine ⟨307616675136423836094877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6562489069577041836690709 307616675136423836094877)
                    ·
                      rfl

theorem cell23_1797244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1797244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797244 prefixEnd_1797244 := by exact prefixLift 1797244
  have htrace : WordTrace (prefixWord ++ tailWord_1797244) baseStart_1797244 baseEnd_1797244 := by
    simpa [prefixWord, tailWord_1797244, baseEnd_1797244] using wordTrace_append hprefix tailTrace_1797244
  have hstable : (prefixWord ++ tailWord_1797244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797244).length < 2 ^ (prefixWord ++ tailWord_1797244).sum := by decide
  have hdescent : baseEnd_1797244 < baseStart_1797244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797246 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1797246 : Nat := 118140960795 + 1797246 * 2 ^ 59
def prefixEnd_1797246 : Nat := 4983230072969 + 3 ^ 40 * 1797246 * 2
def baseEnd_1797246 : Nat := 922851052370580500459623

theorem tailTrace_1797246 : CollatzResearch.WordTrace tailWord_1797246 prefixEnd_1797246 922851052370580500459623 := by
  unfold tailWord_1797246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193868355861520253094449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43700631231261441349837061 8193868355861520253094449)
  ·
    refine ⟨6145401266896140189820837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8193868355861520253094449 6145401266896140189820837)
    ·
      refine ⟨1152262737543026285591407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6145401266896140189820837 1152262737543026285591407)
      ·
        refine ⟨1728394106314539428387111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152262737543026285591407 1728394106314539428387111)
        ·
          refine ⟨2592591159471809142580667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728394106314539428387111 2592591159471809142580667)
          ·
            refine ⟨3888886739207713713871001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592591159471809142580667 3888886739207713713871001)
            ·
              refine ⟨2916665054405785285403251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888886739207713713871001 2916665054405785285403251)
              ·
                refine ⟨4374997581608677928104877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916665054405785285403251 4374997581608677928104877)
                ·
                  refine ⟨1640624093103254223039329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4374997581608677928104877 1640624093103254223039329)
                  ·
                    refine ⟨1230468069827440667279497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1640624093103254223039329 1230468069827440667279497)
                    ·
                      refine ⟨922851052370580500459623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230468069827440667279497 922851052370580500459623)
                      ·
                        rfl

theorem cell23_1797246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1797246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797246 prefixEnd_1797246 := by exact prefixLift 1797246
  have htrace : WordTrace (prefixWord ++ tailWord_1797246) baseStart_1797246 baseEnd_1797246 := by
    simpa [prefixWord, tailWord_1797246, baseEnd_1797246] using wordTrace_append hprefix tailTrace_1797246
  have hstable : (prefixWord ++ tailWord_1797246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797246).length < 2 ^ (prefixWord ++ tailWord_1797246).sum := by decide
  have hdescent : baseEnd_1797246 < baseStart_1797246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797262 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1797262 : Nat := 118140960795 + 1797262 * 2 ^ 59
def prefixEnd_1797262 : Nat := 4983230072969 + 3 ^ 40 * 1797262 * 2
def baseEnd_1797262 : Nat := 922859268061052437859549

theorem tailTrace_1797262 : CollatzResearch.WordTrace tailWord_1797262 prefixEnd_1797262 922859268061052437859549 := by
  unfold tailWord_1797262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193941301854274594667255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43701020276556131171558693 8193941301854274594667255)
  ·
    refine ⟨12290911952781411892000883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8193941301854274594667255 12290911952781411892000883)
    ·
      refine ⟨18436367929172117838001325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12290911952781411892000883 18436367929172117838001325)
      ·
        refine ⟨6913637973439544189250497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18436367929172117838001325 6913637973439544189250497)
        ·
          refine ⟨5185228480079658141937873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6913637973439544189250497 5185228480079658141937873)
          ·
            refine ⟨3888921360059743606453405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185228480079658141937873 3888921360059743606453405)
            ·
              refine ⟨1458345510022403852420027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3888921360059743606453405 1458345510022403852420027)
              ·
                refine ⟨2187518265033605778630041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458345510022403852420027 2187518265033605778630041)
                ·
                  refine ⟨1640638698775204333972531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187518265033605778630041 1640638698775204333972531)
                  ·
                    refine ⟨2460958048162806500958797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640638698775204333972531 2460958048162806500958797)
                    ·
                      refine ⟨922859268061052437859549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2460958048162806500958797 922859268061052437859549)
                      ·
                        rfl

theorem cell23_1797262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1797262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797262 prefixEnd_1797262 := by exact prefixLift 1797262
  have htrace : WordTrace (prefixWord ++ tailWord_1797262) baseStart_1797262 baseEnd_1797262 := by
    simpa [prefixWord, tailWord_1797262, baseEnd_1797262] using wordTrace_append hprefix tailTrace_1797262
  have hstable : (prefixWord ++ tailWord_1797262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797262).length < 2 ^ (prefixWord ++ tailWord_1797262).sum := by decide
  have hdescent : baseEnd_1797262 < baseStart_1797262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797264 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1797264 : Nat := 118140960795 + 1797264 * 2 ^ 59
def prefixEnd_1797264 : Nat := 4983230072969 + 3 ^ 40 * 1797264 * 2
def baseEnd_1797264 : Nat := 922860295022361430034539

theorem tailTrace_1797264 : CollatzResearch.WordTrace tailWord_1797264 prefixEnd_1797264 922860295022361430034539 := by
  unfold tailWord_1797264
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775801680413475549455423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43701068907217967399273897 32775801680413475549455423)
  ·
    refine ⟨49163702520620213324183135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32775801680413475549455423 49163702520620213324183135)
    ·
      refine ⟨73745553780930319986274703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49163702520620213324183135 73745553780930319986274703)
      ·
        refine ⟨110618330671395479979412055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73745553780930319986274703 110618330671395479979412055)
        ·
          refine ⟨165927496007093219969118083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110618330671395479979412055 165927496007093219969118083)
          ·
            refine ⟨248891244010639829953677125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165927496007093219969118083 248891244010639829953677125)
            ·
              refine ⟨46667108251994968116314461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248891244010639829953677125 46667108251994968116314461)
              ·
                refine ⟨17500165594498113043617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46667108251994968116314461 17500165594498113043617923)
                ·
                  refine ⟨26250248391747169565426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17500165594498113043617923 26250248391747169565426885)
                  ·
                    refine ⟨4921921573452594293517541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26250248391747169565426885 4921921573452594293517541)
                    ·
                      refine ⟨922860295022361430034539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4921921573452594293517541 922860295022361430034539)
                      ·
                        rfl

theorem cell23_1797264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1797264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797264 prefixEnd_1797264 := by exact prefixLift 1797264
  have htrace : WordTrace (prefixWord ++ tailWord_1797264) baseStart_1797264 baseEnd_1797264 := by
    simpa [prefixWord, tailWord_1797264, baseEnd_1797264] using wordTrace_append hprefix tailTrace_1797264
  have hstable : (prefixWord ++ tailWord_1797264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797264).length < 2 ^ (prefixWord ++ tailWord_1797264).sum := by decide
  have hdescent : baseEnd_1797264 < baseStart_1797264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797304 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1797304 : Nat := 118140960795 + 1797304 * 2 ^ 59
def prefixEnd_1797304 : Nat := 4983230072969 + 3 ^ 40 * 1797304 * 2
def baseEnd_1797304 : Nat := 307626944749513757844785

theorem tailTrace_1797304 : CollatzResearch.WordTrace tailWord_1797304 prefixEnd_1797304 307626944749513757844785 := by
  unfold tailWord_1797304
  simp only [CollatzResearch.WordTrace]
  refine ⟨32776531140341018965183483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43702041520454691953577977 32776531140341018965183483)
  ·
    refine ⟨49164796710511528447775225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32776531140341018965183483 49164796710511528447775225)
    ·
      refine ⟨36873597532883646335831419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49164796710511528447775225 36873597532883646335831419)
      ·
        refine ⟨55310396299325469503747129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36873597532883646335831419 55310396299325469503747129)
        ·
          refine ⟨41482797224494102127810347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55310396299325469503747129 41482797224494102127810347)
          ·
            refine ⟨62224195836741153191715521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41482797224494102127810347 62224195836741153191715521)
            ·
              refine ⟨46668146877555864893786641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62224195836741153191715521 46668146877555864893786641)
              ·
                refine ⟨35001110158166898670339981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46668146877555864893786641 35001110158166898670339981)
                ·
                  refine ⟨13125416309312587001377493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35001110158166898670339981 13125416309312587001377493)
                  ·
                    refine ⟨307626944749513757844785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13125416309312587001377493 307626944749513757844785)
                    ·
                      rfl

theorem cell23_1797304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1797304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797304 prefixEnd_1797304 := by exact prefixLift 1797304
  have htrace : WordTrace (prefixWord ++ tailWord_1797304) baseStart_1797304 baseEnd_1797304 := by
    simpa [prefixWord, tailWord_1797304, baseEnd_1797304] using wordTrace_append hprefix tailTrace_1797304
  have hstable : (prefixWord ++ tailWord_1797304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797304).length < 2 ^ (prefixWord ++ tailWord_1797304).sum := by decide
  have hdescent : baseEnd_1797304 < baseStart_1797304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797308 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 7]
def baseStart_1797308 : Nat := 118140960795 + 1797308 * 2 ^ 59
def prefixEnd_1797308 : Nat := 4983230072969 + 3 ^ 40 * 1797308 * 2
def baseEnd_1797308 : Nat := 102542543130128806431593

theorem tailTrace_1797308 : CollatzResearch.WordTrace tailWord_1797308 prefixEnd_1797308 102542543130128806431593 := by
  unfold tailWord_1797308
  simp only [CollatzResearch.WordTrace]
  refine ⟨32776604086333773306756289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43702138781778364409008385 32776604086333773306756289)
  ·
    refine ⟨24582453064750329980067217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32776604086333773306756289 24582453064750329980067217)
    ·
      refine ⟨18436839798562747485050413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24582453064750329980067217 18436839798562747485050413)
      ·
        refine ⟨6913814924461030306893905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18436839798562747485050413 6913814924461030306893905)
        ·
          refine ⟨5185361193345772730170429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6913814924461030306893905 5185361193345772730170429)
          ·
            refine ⟨1944510447504664773813911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5185361193345772730170429 1944510447504664773813911)
            ·
              refine ⟨2916765671256997160720867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944510447504664773813911 2916765671256997160720867)
              ·
                refine ⟨4375148506885495741081301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916765671256997160720867 4375148506885495741081301)
                ·
                  refine ⟨102542543130128806431593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4375148506885495741081301 102542543130128806431593)
                  ·
                    rfl

theorem cell23_1797308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_1797308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797308 prefixEnd_1797308 := by exact prefixLift 1797308
  have htrace : WordTrace (prefixWord ++ tailWord_1797308) baseStart_1797308 baseEnd_1797308 := by
    simpa [prefixWord, tailWord_1797308, baseEnd_1797308] using wordTrace_append hprefix tailTrace_1797308
  have hstable : (prefixWord ++ tailWord_1797308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797308).length < 2 ^ (prefixWord ++ tailWord_1797308).sum := by decide
  have hdescent : baseEnd_1797308 < baseStart_1797308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797358 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1797358 : Nat := 118140960795 + 1797358 * 2 ^ 59
def prefixEnd_1797358 : Nat := 4983230072969 + 3 ^ 40 * 1797358 * 2
def baseEnd_1797358 : Nat := 922908562203884062259107

theorem tailTrace_1797358 : CollatzResearch.WordTrace tailWord_1797358 prefixEnd_1797358 922908562203884062259107 := by
  unfold tailWord_1797358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194378977810800644104091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43703354548324270101888485 8194378977810800644104091)
  ·
    refine ⟨12291568466716200966156137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8194378977810800644104091 12291568466716200966156137)
    ·
      refine ⟨9218676350037150724617103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12291568466716200966156137 9218676350037150724617103)
      ·
        refine ⟨13828014525055726086925655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218676350037150724617103 13828014525055726086925655)
        ·
          refine ⟨20742021787583589130388483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13828014525055726086925655 20742021787583589130388483)
          ·
            refine ⟨31113032681375383695582725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20742021787583589130388483 31113032681375383695582725)
            ·
              refine ⟨5833693627757884442921761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31113032681375383695582725 5833693627757884442921761)
              ·
                refine ⟨4375270220818413332191321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5833693627757884442921761 4375270220818413332191321)
                ·
                  refine ⟨3281452665613809999143491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4375270220818413332191321 3281452665613809999143491)
                  ·
                    refine ⟨4922178998420714998715237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281452665613809999143491 4922178998420714998715237)
                    ·
                      refine ⟨922908562203884062259107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4922178998420714998715237 922908562203884062259107)
                      ·
                        rfl

theorem cell23_1797358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1797358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797358 prefixEnd_1797358 := by exact prefixLift 1797358
  have htrace : WordTrace (prefixWord ++ tailWord_1797358) baseStart_1797358 baseEnd_1797358 := by
    simpa [prefixWord, tailWord_1797358, baseEnd_1797358] using wordTrace_append hprefix tailTrace_1797358
  have hstable : (prefixWord ++ tailWord_1797358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797358).length < 2 ^ (prefixWord ++ tailWord_1797358).sum := by decide
  have hdescent : baseEnd_1797358 < baseStart_1797358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797361 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_1797361 : Nat := 118140960795 + 1797361 * 2 ^ 59
def prefixEnd_1797361 : Nat := 4983230072969 + 3 ^ 40 * 1797361 * 2
def baseEnd_1797361 : Nat := 922910102645847550521593

theorem tailTrace_1797361 : CollatzResearch.WordTrace tailWord_1797361 prefixEnd_1797361 922910102645847550521593 := by
  unfold tailWord_1797361
  simp only [CollatzResearch.WordTrace]
  refine ⟨65555141241475536665191937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43703427494317024443461291 65555141241475536665191937)
  ·
    refine ⟨49166355931106652498893953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65555141241475536665191937 49166355931106652498893953)
    ·
      refine ⟨36874766948329989374170465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49166355931106652498893953 36874766948329989374170465)
      ·
        refine ⟨27656075211247492030627849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36874766948329989374170465 27656075211247492030627849)
        ·
          refine ⟨20742056408435619022970887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27656075211247492030627849 20742056408435619022970887)
          ·
            refine ⟨31113084612653428534456331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20742056408435619022970887 31113084612653428534456331)
            ·
              refine ⟨46669626918980142801684497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31113084612653428534456331 46669626918980142801684497)
              ·
                refine ⟨35002220189235107101263373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46669626918980142801684497 35002220189235107101263373)
                ·
                  refine ⟨13125832570963165162973765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35002220189235107101263373 13125832570963165162973765)
                  ·
                    refine ⟨2461093607055593468057581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13125832570963165162973765 2461093607055593468057581)
                    ·
                      refine ⟨922910102645847550521593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461093607055593468057581 922910102645847550521593)
                      ·
                        rfl

theorem cell23_1797361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_1797361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797361 prefixEnd_1797361 := by exact prefixLift 1797361
  have htrace : WordTrace (prefixWord ++ tailWord_1797361) baseStart_1797361 baseEnd_1797361 := by
    simpa [prefixWord, tailWord_1797361, baseEnd_1797361] using wordTrace_append hprefix tailTrace_1797361
  have hstable : (prefixWord ++ tailWord_1797361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797361).length < 2 ^ (prefixWord ++ tailWord_1797361).sum := by decide
  have hdescent : baseEnd_1797361 < baseStart_1797361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797381 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 6]
def baseStart_1797381 : Nat := 118140960795 + 1797381 * 2 ^ 59
def prefixEnd_1797381 : Nat := 4983230072969 + 3 ^ 40 * 1797381 * 2
def baseEnd_1797381 : Nat := 102546708028770830252389

theorem tailTrace_1797381 : CollatzResearch.WordTrace tailWord_1797381 prefixEnd_1797381 102546708028770830252389 := by
  unfold tailWord_1797381
  simp only [CollatzResearch.WordTrace]
  refine ⟨65555870701403080080919997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43703913800935386720613331 65555870701403080080919997)
  ·
    refine ⟨24583451513026155030344999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65555870701403080080919997 24583451513026155030344999)
    ·
      refine ⟨36875177269539232545517499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24583451513026155030344999 36875177269539232545517499)
      ·
        refine ⟨55312765904308848818276249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36875177269539232545517499 55312765904308848818276249)
        ·
          refine ⟨41484574428231636613707187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55312765904308848818276249 41484574428231636613707187)
          ·
            refine ⟨62226861642347454920560781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41484574428231636613707187 62226861642347454920560781)
            ·
              refine ⟨23335073115880295595210293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62226861642347454920560781 23335073115880295595210293)
              ·
                refine ⟨2187663104613777712050965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23335073115880295595210293 2187663104613777712050965)
                ·
                  refine ⟨102546708028770830252389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2187663104613777712050965 102546708028770830252389)
                  ·
                    rfl

theorem cell23_1797381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_1797381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797381 prefixEnd_1797381 := by exact prefixLift 1797381
  have htrace : WordTrace (prefixWord ++ tailWord_1797381) baseStart_1797381 baseEnd_1797381 := by
    simpa [prefixWord, tailWord_1797381, baseEnd_1797381] using wordTrace_append hprefix tailTrace_1797381
  have hstable : (prefixWord ++ tailWord_1797381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797381).length < 2 ^ (prefixWord ++ tailWord_1797381).sum := by decide
  have hdescent : baseEnd_1797381 < baseStart_1797381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797402 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_1797402 : Nat := 118140960795 + 1797402 * 2 ^ 59
def prefixEnd_1797402 : Nat := 4983230072969 + 3 ^ 40 * 1797402 * 2
def baseEnd_1797402 : Nat := 307643718450893963369635

theorem tailTrace_1797402 : CollatzResearch.WordTrace tailWord_1797402 prefixEnd_1797402 307643718450893963369635 := by
  unfold tailWord_1797402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389159158581750166858615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43704424422884667111622973 16389159158581750166858615)
  ·
    refine ⟨24583738737872625250287923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16389159158581750166858615 24583738737872625250287923)
    ·
      refine ⟨36875608106808937875431885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24583738737872625250287923 36875608106808937875431885)
      ·
        refine ⟨13828353040053351703286957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36875608106808937875431885 13828353040053351703286957)
        ·
          refine ⟨5185632390020006888732609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13828353040053351703286957 5185632390020006888732609)
          ·
            refine ⟨3889224292515005166549457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185632390020006888732609 3889224292515005166549457)
            ·
              refine ⟨2916918219386253874912093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889224292515005166549457 2916918219386253874912093)
              ·
                refine ⟨1093844332269845203092035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2916918219386253874912093 1093844332269845203092035)
                ·
                  refine ⟨1640766498404767804638053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093844332269845203092035 1640766498404767804638053)
                  ·
                    refine ⟨307643718450893963369635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1640766498404767804638053 307643718450893963369635)
                    ·
                      rfl

theorem cell23_1797402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_1797402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797402 prefixEnd_1797402 := by exact prefixLift 1797402
  have htrace : WordTrace (prefixWord ++ tailWord_1797402) baseStart_1797402 baseEnd_1797402 := by
    simpa [prefixWord, tailWord_1797402, baseEnd_1797402] using wordTrace_append hprefix tailTrace_1797402
  have hstable : (prefixWord ++ tailWord_1797402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797402).length < 2 ^ (prefixWord ++ tailWord_1797402).sum := by decide
  have hdescent : baseEnd_1797402 < baseStart_1797402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797418 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1797418 : Nat := 118140960795 + 1797418 * 2 ^ 59
def prefixEnd_1797418 : Nat := 4983230072969 + 3 ^ 40 * 1797418 * 2
def baseEnd_1797418 : Nat := 922939371043153827508831

theorem tailTrace_1797418 : CollatzResearch.WordTrace tailWord_1797418 prefixEnd_1797418 922939371043153827508831 := by
  unfold tailWord_1797418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389305050567258850004227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43704813468179356933344605 16389305050567258850004227)
  ·
    refine ⟨24583957575850888275006341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16389305050567258850004227 24583957575850888275006341)
    ·
      refine ⟨4609492045472041551563689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24583957575850888275006341 4609492045472041551563689)
      ·
        refine ⟨3457119034104031163672767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4609492045472041551563689 3457119034104031163672767)
        ·
          refine ⟨5185678551156046745509151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457119034104031163672767 5185678551156046745509151)
          ·
            refine ⟨7778517826734070118263727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185678551156046745509151 7778517826734070118263727)
            ·
              refine ⟨11667776740101105177395591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778517826734070118263727 11667776740101105177395591)
              ·
                refine ⟨17501665110151657766093387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11667776740101105177395591 17501665110151657766093387)
                ·
                  refine ⟨26252497665227486649140081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17501665110151657766093387 26252497665227486649140081)
                  ·
                    refine ⟨19689373248920614986855061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26252497665227486649140081 19689373248920614986855061)
                    ·
                      refine ⟨922939371043153827508831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19689373248920614986855061 922939371043153827508831)
                      ·
                        rfl

theorem cell23_1797418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1797418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797418 prefixEnd_1797418 := by exact prefixLift 1797418
  have htrace : WordTrace (prefixWord ++ tailWord_1797418) baseStart_1797418 baseEnd_1797418 := by
    simpa [prefixWord, tailWord_1797418, baseEnd_1797418] using wordTrace_append hprefix tailTrace_1797418
  have hstable : (prefixWord ++ tailWord_1797418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797418).length < 2 ^ (prefixWord ++ tailWord_1797418).sum := by decide
  have hdescent : baseEnd_1797418 < baseStart_1797418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797425 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_1797425 : Nat := 118140960795 + 1797425 * 2 ^ 59
def prefixEnd_1797425 : Nat := 4983230072969 + 3 ^ 40 * 1797425 * 2
def baseEnd_1797425 : Nat := 922942965407735300121299

theorem tailTrace_1797425 : CollatzResearch.WordTrace tailWord_1797425 prefixEnd_1797425 922942965407735300121299 := by
  unfold tailWord_1797425
  simp only [CollatzResearch.WordTrace]
  refine ⟨65557475513243675595521729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43704983675495783730347819 65557475513243675595521729)
  ·
    refine ⟨49168106634932756696641297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65557475513243675595521729 49168106634932756696641297)
    ·
      refine ⟨36876079976199567522480973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49168106634932756696641297 36876079976199567522480973)
      ·
        refine ⟨13828529991074837820930365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36876079976199567522480973 13828529991074837820930365)
        ·
          refine ⟨5185698746653064182848887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13828529991074837820930365 5185698746653064182848887)
          ·
            refine ⟨7778548119979596274273331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185698746653064182848887 7778548119979596274273331)
            ·
              refine ⟨11667822179969394411409997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778548119979596274273331 11667822179969394411409997)
              ·
                refine ⟨4375433317488522904278749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11667822179969394411409997 4375433317488522904278749)
                ·
                  refine ⟨1640787494058196089104531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4375433317488522904278749 1640787494058196089104531)
                  ·
                    refine ⟨2461181241087294133656797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640787494058196089104531 2461181241087294133656797)
                    ·
                      refine ⟨922942965407735300121299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461181241087294133656797 922942965407735300121299)
                      ·
                        rfl

theorem cell23_1797425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_1797425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797425 prefixEnd_1797425 := by exact prefixLift 1797425
  have htrace : WordTrace (prefixWord ++ tailWord_1797425) baseStart_1797425 baseEnd_1797425 := by
    simpa [prefixWord, tailWord_1797425, baseEnd_1797425] using wordTrace_append hprefix tailTrace_1797425
  have hstable : (prefixWord ++ tailWord_1797425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797425).length < 2 ^ (prefixWord ++ tailWord_1797425).sum := by decide
  have hdescent : baseEnd_1797425 < baseStart_1797425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797448 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_1797448 : Nat := 118140960795 + 1797448 * 2 ^ 59
def prefixEnd_1797448 : Nat := 4983230072969 + 3 ^ 40 * 1797448 * 2
def baseEnd_1797448 : Nat := 922954775462788710133693

theorem tailTrace_1797448 : CollatzResearch.WordTrace tailWord_1797448 prefixEnd_1797448 922954775462788710133693 := by
  unfold tailWord_1797448
  simp only [CollatzResearch.WordTrace]
  refine ⟨32779157196080175261804499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43705542928106900349072665 32779157196080175261804499)
  ·
    refine ⟨49168735794120262892706749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32779157196080175261804499 49168735794120262892706749)
    ·
      refine ⟨18438275922795098584765031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49168735794120262892706749 18438275922795098584765031)
      ·
        refine ⟨27657413884192647877147547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18438275922795098584765031 27657413884192647877147547)
        ·
          refine ⟨41486120826288971815721321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27657413884192647877147547 41486120826288971815721321)
          ·
            refine ⟨31114590619716728861790991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41486120826288971815721321 31114590619716728861790991)
            ·
              refine ⟨46671885929575093292686487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31114590619716728861790991 46671885929575093292686487)
              ·
                refine ⟨70007828894362639939029731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46671885929575093292686487 70007828894362639939029731)
                ·
                  refine ⟨105011743341543959908544597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70007828894362639939029731 105011743341543959908544597)
                  ·
                    refine ⟨1230606367283718280178257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105011743341543959908544597 1230606367283718280178257)
                    ·
                      refine ⟨922954775462788710133693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230606367283718280178257 922954775462788710133693)
                      ·
                        rfl

theorem cell23_1797448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_1797448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797448 prefixEnd_1797448 := by exact prefixLift 1797448
  have htrace : WordTrace (prefixWord ++ tailWord_1797448) baseStart_1797448 baseEnd_1797448 := by
    simpa [prefixWord, tailWord_1797448, baseEnd_1797448] using wordTrace_append hprefix tailTrace_1797448
  have hstable : (prefixWord ++ tailWord_1797448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797448).length < 2 ^ (prefixWord ++ tailWord_1797448).sum := by decide
  have hdescent : baseEnd_1797448 < baseStart_1797448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797453 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1797453 : Nat := 118140960795 + 1797453 * 2 ^ 59
def prefixEnd_1797453 : Nat := 4983230072969 + 3 ^ 40 * 1797453 * 2
def baseEnd_1797453 : Nat := 307652447622020396857057

theorem tailTrace_1797453 : CollatzResearch.WordTrace tailWord_1797453 prefixEnd_1797453 307652447622020396857057 := by
  unfold tailWord_1797453
  simp only [CollatzResearch.WordTrace]
  refine ⟨65558496757142236377541013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43705664504761490918360675 65558496757142236377541013)
  ·
    refine ⟨3073054535491042330197235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65558496757142236377541013 3073054535491042330197235)
    ·
      refine ⟨4609581803236563495295853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073054535491042330197235 4609581803236563495295853)
      ·
        refine ⟨1728593176213711310735945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4609581803236563495295853 1728593176213711310735945)
        ·
          refine ⟨1296444882160283483051959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1728593176213711310735945 1296444882160283483051959)
          ·
            refine ⟨1944667323240425224577939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296444882160283483051959 1944667323240425224577939)
            ·
              refine ⟨2917000984860637836866909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944667323240425224577939 2917000984860637836866909)
              ·
                refine ⟨1093875369322739188825091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2917000984860637836866909 1093875369322739188825091)
                ·
                  refine ⟨1640813053984108783237637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093875369322739188825091 1640813053984108783237637)
                  ·
                    refine ⟨307652447622020396857057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1640813053984108783237637 307652447622020396857057)
                    ·
                      rfl

theorem cell23_1797453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1797453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797453 prefixEnd_1797453 := by exact prefixLift 1797453
  have htrace : WordTrace (prefixWord ++ tailWord_1797453) baseStart_1797453 baseEnd_1797453 := by
    simpa [prefixWord, tailWord_1797453, baseEnd_1797453] using wordTrace_append hprefix tailTrace_1797453
  have hstable : (prefixWord ++ tailWord_1797453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797453).length < 2 ^ (prefixWord ++ tailWord_1797453).sum := by decide
  have hdescent : baseEnd_1797453 < baseStart_1797453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797465 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 5, 2, 2]
def baseStart_1797465 : Nat := 118140960795 + 1797465 * 2 ^ 59
def prefixEnd_1797465 : Nat := 4983230072969 + 3 ^ 40 * 1797465 * 2
def baseEnd_1797465 : Nat := 922963504633915143621115

theorem tailTrace_1797465 : CollatzResearch.WordTrace tailWord_1797465 prefixEnd_1797465 922963504633915143621115 := by
  unfold tailWord_1797465
  simp only [CollatzResearch.WordTrace]
  refine ⟨65558934433098762426977849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43705956288732508284651899 65558934433098762426977849)
  ·
    refine ⟨49169200824824071820233387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65558934433098762426977849 49169200824824071820233387)
    ·
      refine ⟨73753801237236107730350081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49169200824824071820233387 73753801237236107730350081)
      ·
        refine ⟨55315350927927080797762561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73753801237236107730350081 55315350927927080797762561)
        ·
          refine ⟨41486513195945310598321921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55315350927927080797762561 41486513195945310598321921)
          ·
            refine ⟨31114884896958982948741441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41486513195945310598321921 31114884896958982948741441)
            ·
              refine ⟨23336163672719237211556081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31114884896958982948741441 23336163672719237211556081)
              ·
                refine ⟨17502122754539427908667061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23336163672719237211556081 17502122754539427908667061)
                ·
                  refine ⟨1640824008238071366437537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17502122754539427908667061 1640824008238071366437537)
                  ·
                    refine ⟨1230618006178553524828153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1640824008238071366437537 1230618006178553524828153)
                    ·
                      refine ⟨922963504633915143621115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230618006178553524828153 922963504633915143621115)
                      ·
                        rfl

theorem cell23_1797465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_1797465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797465 prefixEnd_1797465 := by exact prefixLift 1797465
  have htrace : WordTrace (prefixWord ++ tailWord_1797465) baseStart_1797465 baseEnd_1797465 := by
    simpa [prefixWord, tailWord_1797465, baseEnd_1797465] using wordTrace_append hprefix tailTrace_1797465
  have hstable : (prefixWord ++ tailWord_1797465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797465).length < 2 ^ (prefixWord ++ tailWord_1797465).sum := by decide
  have hdescent : baseEnd_1797465 < baseStart_1797465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797521 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1797521 : Nat := 118140960795 + 1797521 * 2 ^ 59
def prefixEnd_1797521 : Nat := 4983230072969 + 3 ^ 40 * 1797521 * 2
def baseEnd_1797521 : Nat := 922992259550566924520857

theorem tailTrace_1797521 : CollatzResearch.WordTrace tailWord_1797521 prefixEnd_1797521 922992259550566924520857 := by
  unfold tailWord_1797521
  simp only [CollatzResearch.WordTrace]
  refine ⟨65560976920895883991016417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43707317947263922660677611 65560976920895883991016417)
  ·
    refine ⟨49170732690671912993262313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65560976920895883991016417 49170732690671912993262313)
    ·
      refine ⟨36878049518003934744946735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49170732690671912993262313 36878049518003934744946735)
      ·
        refine ⟨55317074277005902117420103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36878049518003934744946735 55317074277005902117420103)
        ·
          refine ⟨82975611415508853176130155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55317074277005902117420103 82975611415508853176130155)
          ·
            refine ⟨124463417123263279764195233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82975611415508853176130155 124463417123263279764195233)
            ·
              refine ⟨93347562842447459823146425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124463417123263279764195233 93347562842447459823146425)
              ·
                refine ⟨70010672131835594867359819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93347562842447459823146425 70010672131835594867359819)
                ·
                  refine ⟨105016008197753392301039729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70010672131835594867359819 105016008197753392301039729)
                  ·
                    refine ⟨78762006148315044225779797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105016008197753392301039729 78762006148315044225779797)
                    ·
                      refine ⟨922992259550566924520857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78762006148315044225779797 922992259550566924520857)
                      ·
                        rfl

theorem cell23_1797521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1797521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797521 prefixEnd_1797521 := by exact prefixLift 1797521
  have htrace : WordTrace (prefixWord ++ tailWord_1797521) baseStart_1797521 baseEnd_1797521 := by
    simpa [prefixWord, tailWord_1797521, baseEnd_1797521] using wordTrace_append hprefix tailTrace_1797521
  have hstable : (prefixWord ++ tailWord_1797521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797521).length < 2 ^ (prefixWord ++ tailWord_1797521).sum := by decide
  have hdescent : baseEnd_1797521 < baseStart_1797521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797533 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_1797533 : Nat := 118140960795 + 1797533 * 2 ^ 59
def prefixEnd_1797533 : Nat := 4983230072969 + 3 ^ 40 * 1797533 * 2
def baseEnd_1797533 : Nat := 922998421318420877570803

theorem tailTrace_1797533 : CollatzResearch.WordTrace tailWord_1797533 prefixEnd_1797533 922998421318420877570803 := by
  unfold tailWord_1797533
  simp only [CollatzResearch.WordTrace]
  refine ⟨65561414596852410040453253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43707609731234940026968835 65561414596852410040453253)
  ·
    refine ⟨12292765236909826882584985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65561414596852410040453253 12292765236909826882584985)
    ·
      refine ⟨9219573927682370161938739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12292765236909826882584985 9219573927682370161938739)
      ·
        refine ⟨13829360891523555242908109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219573927682370161938739 13829360891523555242908109)
        ·
          refine ⟨5186010334321333216090541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13829360891523555242908109 5186010334321333216090541)
          ·
            refine ⟨1944753875370499956033953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5186010334321333216090541 1944753875370499956033953)
            ·
              refine ⟨1458565406527874967025465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944753875370499956033953 1458565406527874967025465)
              ·
                refine ⟨1093924054895906225269099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458565406527874967025465 1093924054895906225269099)
                ·
                  refine ⟨1640886082343859337903649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093924054895906225269099 1640886082343859337903649)
                  ·
                    refine ⟨1230664561757894503427737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1640886082343859337903649 1230664561757894503427737)
                    ·
                      refine ⟨922998421318420877570803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230664561757894503427737 922998421318420877570803)
                      ·
                        rfl

theorem cell23_1797533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_1797533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797533 prefixEnd_1797533 := by exact prefixLift 1797533
  have htrace : WordTrace (prefixWord ++ tailWord_1797533) baseStart_1797533 baseEnd_1797533 := by
    simpa [prefixWord, tailWord_1797533, baseEnd_1797533] using wordTrace_append hprefix tailTrace_1797533
  have hstable : (prefixWord ++ tailWord_1797533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797533).length < 2 ^ (prefixWord ++ tailWord_1797533).sum := by decide
  have hdescent : baseEnd_1797533 < baseStart_1797533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797549 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1797549 : Nat := 118140960795 + 1797549 * 2 ^ 59
def prefixEnd_1797549 : Nat := 4983230072969 + 3 ^ 40 * 1797549 * 2
def baseEnd_1797549 : Nat := 923006637008892814970729

theorem tailTrace_1797549 : CollatzResearch.WordTrace tailWord_1797549 prefixEnd_1797549 923006637008892814970729 := by
  unfold tailWord_1797549
  simp only [CollatzResearch.WordTrace]
  refine ⟨65561998164794444773035701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43707998776529629848690467 65561998164794444773035701)
  ·
    refine ⟨6146437327949479197472097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65561998164794444773035701 6146437327949479197472097)
    ·
      refine ⟨4609827995962109398104073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6146437327949479197472097 4609827995962109398104073)
      ·
        refine ⟨3457370996971582048578055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4609827995962109398104073 3457370996971582048578055)
        ·
          refine ⟨5186056495457373072867083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457370996971582048578055 5186056495457373072867083)
          ·
            refine ⟨7779084743186059609300625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186056495457373072867083 7779084743186059609300625)
            ·
              refine ⟨5834313557389544706975469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779084743186059609300625 5834313557389544706975469)
              ·
                refine ⟨2187867584021079265115801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834313557389544706975469 2187867584021079265115801)
                ·
                  refine ⟨1640900688015809448836851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2187867584021079265115801 1640900688015809448836851)
                  ·
                    refine ⟨2461351032023714173255277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640900688015809448836851 2461351032023714173255277)
                    ·
                      refine ⟨923006637008892814970729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461351032023714173255277 923006637008892814970729)
                      ·
                        rfl

theorem cell23_1797549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1797549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797549 prefixEnd_1797549 := by exact prefixLift 1797549
  have htrace : WordTrace (prefixWord ++ tailWord_1797549) baseStart_1797549 baseEnd_1797549 := by
    simpa [prefixWord, tailWord_1797549, baseEnd_1797549] using wordTrace_append hprefix tailTrace_1797549
  have hstable : (prefixWord ++ tailWord_1797549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797549).length < 2 ^ (prefixWord ++ tailWord_1797549).sum := by decide
  have hdescent : baseEnd_1797549 < baseStart_1797549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797608 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1797608 : Nat := 118140960795 + 1797608 * 2 ^ 59
def prefixEnd_1797608 : Nat := 4983230072969 + 3 ^ 40 * 1797608 * 2
def baseEnd_1797608 : Nat := 307678977455836028044319

theorem tailTrace_1797608 : CollatzResearch.WordTrace tailWord_1797608 prefixEnd_1797608 307678977455836028044319 := by
  unfold tailWord_1797608
  simp only [CollatzResearch.WordTrace]
  refine ⟨32782075035790348924716739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43709433381053798566288985 32782075035790348924716739)
  ·
    refine ⟨49173112553685523387075109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32782075035790348924716739 49173112553685523387075109)
    ·
      refine ⟨9219958603816035635076583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49173112553685523387075109 9219958603816035635076583)
      ·
        refine ⟨13829937905724053452614875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219958603816035635076583 13829937905724053452614875)
        ·
          refine ⟨20744906858586080178922313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13829937905724053452614875 20744906858586080178922313)
          ·
            refine ⟨15558680143939560134191735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20744906858586080178922313 15558680143939560134191735)
            ·
              refine ⟨23338020215909340201287603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15558680143939560134191735 23338020215909340201287603)
              ·
                refine ⟨35007030323864010301931405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23338020215909340201287603 35007030323864010301931405)
                ·
                  refine ⟨13127636371449003863224277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35007030323864010301931405 13127636371449003863224277)
                  ·
                    refine ⟨307678977455836028044319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13127636371449003863224277 307678977455836028044319)
                    ·
                      rfl

theorem cell23_1797608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1797608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797608 prefixEnd_1797608 := by exact prefixLift 1797608
  have htrace : WordTrace (prefixWord ++ tailWord_1797608) baseStart_1797608 baseEnd_1797608 := by
    simpa [prefixWord, tailWord_1797608, baseEnd_1797608] using wordTrace_append hprefix tailTrace_1797608
  have hstable : (prefixWord ++ tailWord_1797608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797608).length < 2 ^ (prefixWord ++ tailWord_1797608).sum := by decide
  have hdescent : baseEnd_1797608 < baseStart_1797608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797615 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 5, 2]
def baseStart_1797615 : Nat := 118140960795 + 1797615 * 2 ^ 59
def prefixEnd_1797615 : Nat := 4983230072969 + 3 ^ 40 * 1797615 * 2
def baseEnd_1797615 : Nat := 923040526732089556745425

theorem tailTrace_1797615 : CollatzResearch.WordTrace tailWord_1797615 prefixEnd_1797615 923040526732089556745425 := by
  unfold tailWord_1797615
  simp only [CollatzResearch.WordTrace]
  refine ⟨65564405382555338044938299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43709603588370225363292199 65564405382555338044938299)
  ·
    refine ⟨98346608073833007067407449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65564405382555338044938299 98346608073833007067407449)
    ·
      refine ⟨73759956055374755300555587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98346608073833007067407449 73759956055374755300555587)
      ·
        refine ⟨110639934083062132950833381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73759956055374755300555587 110639934083062132950833381)
        ·
          refine ⟨20744987640574149928281259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110639934083062132950833381 20744987640574149928281259)
          ·
            refine ⟨31117481460861224892421889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20744987640574149928281259 31117481460861224892421889)
            ·
              refine ⟨23338111095645918669316417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31117481460861224892421889 23338111095645918669316417)
              ·
                refine ⟨17503583321734439001987313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23338111095645918669316417 17503583321734439001987313)
                ·
                  refine ⟨13127687491300829251490485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17503583321734439001987313 13127687491300829251490485)
                  ·
                    refine ⟨1230720702309452742327233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13127687491300829251490485 1230720702309452742327233)
                    ·
                      refine ⟨923040526732089556745425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230720702309452742327233 923040526732089556745425)
                      ·
                        rfl

theorem cell23_1797615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5, 2].length) (baseStart_1797615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797615 prefixEnd_1797615 := by exact prefixLift 1797615
  have htrace : WordTrace (prefixWord ++ tailWord_1797615) baseStart_1797615 baseEnd_1797615 := by
    simpa [prefixWord, tailWord_1797615, baseEnd_1797615] using wordTrace_append hprefix tailTrace_1797615
  have hstable : (prefixWord ++ tailWord_1797615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797615).length < 2 ^ (prefixWord ++ tailWord_1797615).sum := by decide
  have hdescent : baseEnd_1797615 < baseStart_1797615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797712 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3]
def baseStart_1797712 : Nat := 118140960795 + 1797712 * 2 ^ 59
def prefixEnd_1797712 : Nat := 4983230072969 + 3 ^ 40 * 1797712 * 2
def baseEnd_1797712 : Nat := 923090334355575677232479

theorem tailTrace_1797712 : CollatzResearch.WordTrace tailWord_1797712 prefixEnd_1797712 923090334355575677232479 := by
  unfold tailWord_1797712
  simp only [CollatzResearch.WordTrace]
  refine ⟨32783971631601961805609695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43711962175469282407479593 32783971631601961805609695)
  ·
    refine ⟨49175957447402942708414543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32783971631601961805609695 49175957447402942708414543)
    ·
      refine ⟨73763936171104414062621815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49175957447402942708414543 73763936171104414062621815)
      ·
        refine ⟨110645904256656621093932723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73763936171104414062621815 110645904256656621093932723)
        ·
          refine ⟨165968856384984931640899085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110645904256656621093932723 165968856384984931640899085)
          ·
            refine ⟨62238321144369349365337157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165968856384984931640899085 62238321144369349365337157)
            ·
              refine ⟨11669685214569253006000717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62238321144369349365337157 11669685214569253006000717)
              ·
                refine ⟨4376131955463469877250269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11669685214569253006000717 4376131955463469877250269)
                ·
                  refine ⟨1641049483298801203968851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4376131955463469877250269 1641049483298801203968851)
                  ·
                    refine ⟨2461574224948201805953277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641049483298801203968851 2461574224948201805953277)
                    ·
                      refine ⟨923090334355575677232479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461574224948201805953277 923090334355575677232479)
                      ·
                        rfl

theorem cell23_1797712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_1797712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797712 prefixEnd_1797712 := by exact prefixLift 1797712
  have htrace : WordTrace (prefixWord ++ tailWord_1797712) baseStart_1797712 baseEnd_1797712 := by
    simpa [prefixWord, tailWord_1797712, baseEnd_1797712] using wordTrace_append hprefix tailTrace_1797712
  have hstable : (prefixWord ++ tailWord_1797712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797712).length < 2 ^ (prefixWord ++ tailWord_1797712).sum := by decide
  have hdescent : baseEnd_1797712 < baseStart_1797712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797722 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_1797722 : Nat := 118140960795 + 1797722 * 2 ^ 59
def prefixEnd_1797722 : Nat := 4983230072969 + 3 ^ 40 * 1797722 * 2
def baseEnd_1797722 : Nat := 923095469162120638107433

theorem tailTrace_1797722 : CollatzResearch.WordTrace tailWord_1797722 prefixEnd_1797722 923095469162120638107433 := by
  unfold tailWord_1797722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392076998291923829770855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43712205328778463546055613 16392076998291923829770855)
  ·
    refine ⟨24588115497437885744656283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16392076998291923829770855 24588115497437885744656283)
    ·
      refine ⟨36882173246156828616984425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24588115497437885744656283 36882173246156828616984425)
      ·
        refine ⟨27661629934617621462738319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36882173246156828616984425 27661629934617621462738319)
        ·
          refine ⟨41492444901926432194107479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27661629934617621462738319 41492444901926432194107479)
          ·
            refine ⟨62238667352889648291161219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41492444901926432194107479 62238667352889648291161219)
            ·
              refine ⟨93358001029334472436741829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62238667352889648291161219 93358001029334472436741829)
              ·
                refine ⟨17504625193000213581889093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93358001029334472436741829 17504625193000213581889093)
                ·
                  refine ⟨3282117223687540046604205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17504625193000213581889093 3282117223687540046604205)
                  ·
                    refine ⟨1230793958882827517476577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282117223687540046604205 1230793958882827517476577)
                    ·
                      refine ⟨923095469162120638107433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230793958882827517476577 923095469162120638107433)
                      ·
                        rfl

theorem cell23_1797722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_1797722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797722 prefixEnd_1797722 := by exact prefixLift 1797722
  have htrace : WordTrace (prefixWord ++ tailWord_1797722) baseStart_1797722 baseEnd_1797722 := by
    simpa [prefixWord, tailWord_1797722, baseEnd_1797722] using wordTrace_append hprefix tailTrace_1797722
  have hstable : (prefixWord ++ tailWord_1797722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797722).length < 2 ^ (prefixWord ++ tailWord_1797722).sum := by decide
  have hdescent : baseEnd_1797722 < baseStart_1797722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797746 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_1797746 : Nat := 118140960795 + 1797746 * 2 ^ 59
def prefixEnd_1797746 : Nat := 4983230072969 + 3 ^ 40 * 1797746 * 2
def baseEnd_1797746 : Nat := 923107792697828544207323

theorem tailTrace_1797746 : CollatzResearch.WordTrace tailWord_1797746 prefixEnd_1797746 923107792697828544207323 := by
  unfold tailWord_1797746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392295836270186854489273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43712788896720498278638061 16392295836270186854489273)
  ·
    refine ⟨12294221877202640140866955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16392295836270186854489273 12294221877202640140866955)
    ·
      refine ⟨18441332815803960211300433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12294221877202640140866955 18441332815803960211300433)
      ·
        refine ⟨13830999611852970158475325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18441332815803960211300433 13830999611852970158475325)
        ·
          refine ⟨5186624854444863809428247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13830999611852970158475325 5186624854444863809428247)
          ·
            refine ⟨7779937281667295714142371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186624854444863809428247 7779937281667295714142371)
            ·
              refine ⟨11669905922500943571213557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779937281667295714142371 11669905922500943571213557)
              ·
                refine ⟨1094053680234463459801271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11669905922500943571213557 1094053680234463459801271)
                ·
                  refine ⟨1641080520351695189701907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094053680234463459801271 1641080520351695189701907)
                  ·
                    refine ⟨2461620780527542784552861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641080520351695189701907 2461620780527542784552861)
                    ·
                      refine ⟨923107792697828544207323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461620780527542784552861 923107792697828544207323)
                      ·
                        rfl

theorem cell23_1797746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_1797746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797746 prefixEnd_1797746 := by exact prefixLift 1797746
  have htrace : WordTrace (prefixWord ++ tailWord_1797746) baseStart_1797746 baseEnd_1797746 := by
    simpa [prefixWord, tailWord_1797746, baseEnd_1797746] using wordTrace_append hprefix tailTrace_1797746
  have hstable : (prefixWord ++ tailWord_1797746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797746).length < 2 ^ (prefixWord ++ tailWord_1797746).sum := by decide
  have hdescent : baseEnd_1797746 < baseStart_1797746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797749 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1797749 : Nat := 118140960795 + 1797749 * 2 ^ 59
def prefixEnd_1797749 : Nat := 4983230072969 + 3 ^ 40 * 1797749 * 2
def baseEnd_1797749 : Nat := 307703111046597344156603

theorem tailTrace_1797749 : CollatzResearch.WordTrace tailWord_1797749 prefixEnd_1797749 307703111046597344156603 := by
  unfold tailWord_1797749
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569292764069878930316301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43712861842713252620210867 65569292764069878930316301)
  ·
    refine ⟨24588484786526204598868613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65569292764069878930316301 24588484786526204598868613)
    ·
      refine ⟨4610340897473663362287865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24588484786526204598868613 4610340897473663362287865)
      ·
        refine ⟨3457755673105247521715899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4610340897473663362287865 3457755673105247521715899)
        ·
          refine ⟨5186633509657871282573849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457755673105247521715899 5186633509657871282573849)
          ·
            refine ⟨3889975132243403461930387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186633509657871282573849 3889975132243403461930387)
            ·
              refine ⟨5834962698365105192895581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889975132243403461930387 5834962698365105192895581)
              ·
                refine ⟨2188111011886914447335843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834962698365105192895581 2188111011886914447335843)
                ·
                  refine ⟨3282166517830371671003765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188111011886914447335843 3282166517830371671003765)
                  ·
                    refine ⟨307703111046597344156603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3282166517830371671003765 307703111046597344156603)
                    ·
                      rfl

theorem cell23_1797749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1797749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797749 prefixEnd_1797749 := by exact prefixLift 1797749
  have htrace : WordTrace (prefixWord ++ tailWord_1797749) baseStart_1797749 baseEnd_1797749 := by
    simpa [prefixWord, tailWord_1797749, baseEnd_1797749] using wordTrace_append hprefix tailTrace_1797749
  have hstable : (prefixWord ++ tailWord_1797749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797749).length < 2 ^ (prefixWord ++ tailWord_1797749).sum := by decide
  have hdescent : baseEnd_1797749 < baseStart_1797749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797755 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5]
def baseStart_1797755 : Nat := 118140960795 + 1797755 * 2 ^ 59
def prefixEnd_1797755 : Nat := 4983230072969 + 3 ^ 40 * 1797755 * 2
def baseEnd_1797755 : Nat := 923112414023719008994781

theorem tailTrace_1797755 : CollatzResearch.WordTrace tailWord_1797755 prefixEnd_1797755 923112414023719008994781 := by
  unfold tailWord_1797755
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569511602048141955034719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43713007734698761303356479 65569511602048141955034719)
  ·
    refine ⟨98354267403072212932552079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65569511602048141955034719 98354267403072212932552079)
    ·
      refine ⟨147531401104608319398828119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98354267403072212932552079 147531401104608319398828119)
      ·
        refine ⟨221297101656912479098242179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147531401104608319398828119 221297101656912479098242179)
        ·
          refine ⟨331945652485368718647363269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221297101656912479098242179 331945652485368718647363269)
          ·
            refine ⟨62239809841006634746380613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331945652485368718647363269 62239809841006634746380613)
            ·
              refine ⟨11669964345188744014946365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62239809841006634746380613 11669964345188744014946365)
              ·
                refine ⟨4376236629445779005604887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11669964345188744014946365 4376236629445779005604887)
                ·
                  refine ⟨6564354944168668508407331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376236629445779005604887 6564354944168668508407331)
                  ·
                    refine ⟨9846532416253002762610997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564354944168668508407331 9846532416253002762610997)
                    ·
                      refine ⟨923112414023719008994781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9846532416253002762610997 923112414023719008994781)
                      ·
                        rfl

theorem cell23_1797755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_1797755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797755 prefixEnd_1797755 := by exact prefixLift 1797755
  have htrace : WordTrace (prefixWord ++ tailWord_1797755) baseStart_1797755 baseEnd_1797755 := by
    simpa [prefixWord, tailWord_1797755, baseEnd_1797755] using wordTrace_append hprefix tailTrace_1797755
  have hstable : (prefixWord ++ tailWord_1797755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797755).length < 2 ^ (prefixWord ++ tailWord_1797755).sum := by decide
  have hdescent : baseEnd_1797755 < baseStart_1797755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797765 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1797765 : Nat := 118140960795 + 1797765 * 2 ^ 59
def prefixEnd_1797765 : Nat := 4983230072969 + 3 ^ 40 * 1797765 * 2
def baseEnd_1797765 : Nat := 923117548830263969869735

theorem tailTrace_1797765 : CollatzResearch.WordTrace tailWord_1797765 prefixEnd_1797765 923117548830263969869735 := by
  unfold tailWord_1797765
  simp only [CollatzResearch.WordTrace]
  refine ⟨65569876332011913662898749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43713250888007942441932499 65569876332011913662898749)
  ·
    refine ⟨24588703624504467623587031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65569876332011913662898749 24588703624504467623587031)
    ·
      refine ⟨36883055436756701435380547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24588703624504467623587031 36883055436756701435380547)
      ·
        refine ⟨55324583155135052153070821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36883055436756701435380547 55324583155135052153070821)
        ·
          refine ⟨10373359341587822278700779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55324583155135052153070821 10373359341587822278700779)
          ·
            refine ⟨15560039012381733418051169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373359341587822278700779 15560039012381733418051169)
            ·
              refine ⟨11670029259286300063538377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15560039012381733418051169 11670029259286300063538377)
              ·
                refine ⟨8752521944464725047653783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11670029259286300063538377 8752521944464725047653783)
                ·
                  refine ⟨13128782916697087571480675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8752521944464725047653783 13128782916697087571480675)
                  ·
                    refine ⟨19693174375045631357221013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13128782916697087571480675 19693174375045631357221013)
                    ·
                      refine ⟨923117548830263969869735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19693174375045631357221013 923117548830263969869735)
                      ·
                        rfl

theorem cell23_1797765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1797765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797765 prefixEnd_1797765 := by exact prefixLift 1797765
  have htrace : WordTrace (prefixWord ++ tailWord_1797765) baseStart_1797765 baseEnd_1797765 := by
    simpa [prefixWord, tailWord_1797765, baseEnd_1797765] using wordTrace_append hprefix tailTrace_1797765
  have hstable : (prefixWord ++ tailWord_1797765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797765).length < 2 ^ (prefixWord ++ tailWord_1797765).sum := by decide
  have hdescent : baseEnd_1797765 < baseStart_1797765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797769 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 3, 2, 2]
def baseStart_1797769 : Nat := 118140960795 + 1797769 * 2 ^ 59
def prefixEnd_1797769 : Nat := 4983230072969 + 3 ^ 40 * 1797769 * 2
def baseEnd_1797769 : Nat := 923119602752881954219717

theorem tailTrace_1797769 : CollatzResearch.WordTrace tailWord_1797769 prefixEnd_1797769 923119602752881954219717 := by
  unfold tailWord_1797769
  simp only [CollatzResearch.WordTrace]
  refine ⟨65570022223997422346044361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43713348149331614897362907 65570022223997422346044361)
  ·
    refine ⟨49177516667998066759533271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65570022223997422346044361 49177516667998066759533271)
    ·
      refine ⟨73766275001997100139299907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49177516667998066759533271 73766275001997100139299907)
      ·
        refine ⟨110649412502995650208949861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73766275001997100139299907 110649412502995650208949861)
        ·
          refine ⟨20746764844311684414178099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110649412502995650208949861 20746764844311684414178099)
          ·
            refine ⟨31120147266467526621267149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20746764844311684414178099 31120147266467526621267149)
            ·
              refine ⟨11670055224925322482975181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31120147266467526621267149 11670055224925322482975181)
              ·
                refine ⟨4376270709346995931115693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11670055224925322482975181 4376270709346995931115693)
                ·
                  refine ⟨1641101516005123474168385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4376270709346995931115693 1641101516005123474168385)
                  ·
                    refine ⟨1230826137003842605626289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641101516005123474168385 1230826137003842605626289)
                    ·
                      refine ⟨923119602752881954219717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230826137003842605626289 923119602752881954219717)
                      ·
                        rfl

theorem cell23_1797769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2, 2].length) (baseStart_1797769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797769 prefixEnd_1797769 := by exact prefixLift 1797769
  have htrace : WordTrace (prefixWord ++ tailWord_1797769) baseStart_1797769 baseEnd_1797769 := by
    simpa [prefixWord, tailWord_1797769, baseEnd_1797769] using wordTrace_append hprefix tailTrace_1797769
  have hstable : (prefixWord ++ tailWord_1797769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797769).length < 2 ^ (prefixWord ++ tailWord_1797769).sum := by decide
  have hdescent : baseEnd_1797769 < baseStart_1797769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797792 : List Nat := [2, 1, 1, 4, 3, 1, 4, 7]
def baseStart_1797792 : Nat := 118140960795 + 1797792 * 2 ^ 59
def prefixEnd_1797792 : Nat := 4983230072969 + 3 ^ 40 * 1797792 * 2
def baseEnd_1797792 : Nat := 34190052326219828304893

theorem tailTrace_1797792 : CollatzResearch.WordTrace tailWord_1797792 prefixEnd_1797792 34190052326219828304893 := by
  unfold tailWord_1797792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32785430551457048637065815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43713907401942731516087753 32785430551457048637065815)
  ·
    refine ⟨49178145827185572955598723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32785430551457048637065815 49178145827185572955598723)
    ·
      refine ⟨73767218740778359433398085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49178145827185572955598723 73767218740778359433398085)
      ·
        refine ⟨13831353513895942393762141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73767218740778359433398085 13831353513895942393762141)
        ·
          refine ⟨5186757567710978397660803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13831353513895942393762141 5186757567710978397660803)
          ·
            refine ⟨7780136351566467596491205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186757567710978397660803 7780136351566467596491205)
            ·
              refine ⟨1458775565918712674342101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7780136351566467596491205 1458775565918712674342101)
              ·
                refine ⟨34190052326219828304893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1458775565918712674342101 34190052326219828304893)
                ·
                  rfl

theorem cell23_1797792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 7].length) (baseStart_1797792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797792 prefixEnd_1797792 := by exact prefixLift 1797792
  have htrace : WordTrace (prefixWord ++ tailWord_1797792) baseStart_1797792 baseEnd_1797792 := by
    simpa [prefixWord, tailWord_1797792, baseEnd_1797792] using wordTrace_append hprefix tailTrace_1797792
  have hstable : (prefixWord ++ tailWord_1797792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797792).length < 2 ^ (prefixWord ++ tailWord_1797792).sum := by decide
  have hdescent : baseEnd_1797792 < baseStart_1797792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797806 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1797806 : Nat := 118140960795 + 1797806 * 2 ^ 59
def prefixEnd_1797806 : Nat := 4983230072969 + 3 ^ 40 * 1797806 * 2
def baseEnd_1797806 : Nat := 923138601537098309457047

theorem tailTrace_1797806 : CollatzResearch.WordTrace tailWord_1797806 prefixEnd_1797806 923138601537098309457047 := by
  unfold tailWord_1797806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196421465607922208142659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43714247816575585110094181 8196421465607922208142659)
  ·
    refine ⟨12294632198411883312213989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8196421465607922208142659 12294632198411883312213989)
    ·
      refine ⟨2305243537202228121040123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12294632198411883312213989 2305243537202228121040123)
      ·
        refine ⟨3457865305803342181560185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305243537202228121040123 3457865305803342181560185)
        ·
          refine ⟨2593398979352506636170139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3457865305803342181560185 2593398979352506636170139)
          ·
            refine ⟨3890098469028759954255209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593398979352506636170139 3890098469028759954255209)
            ·
              refine ⟨2917573851771569965691407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3890098469028759954255209 2917573851771569965691407)
              ·
                refine ⟨4376360777657354948537111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917573851771569965691407 4376360777657354948537111)
                ·
                  refine ⟨6564541166486032422805667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4376360777657354948537111 6564541166486032422805667)
                  ·
                    refine ⟨9846811749729048634208501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6564541166486032422805667 9846811749729048634208501)
                    ·
                      refine ⟨923138601537098309457047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9846811749729048634208501 923138601537098309457047)
                      ·
                        rfl

theorem cell23_1797806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1797806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797806 prefixEnd_1797806 := by exact prefixLift 1797806
  have htrace : WordTrace (prefixWord ++ tailWord_1797806) baseStart_1797806 baseEnd_1797806 := by
    simpa [prefixWord, tailWord_1797806, baseEnd_1797806] using wordTrace_append hprefix tailTrace_1797806
  have hstable : (prefixWord ++ tailWord_1797806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797806).length < 2 ^ (prefixWord ++ tailWord_1797806).sum := by decide
  have hdescent : baseEnd_1797806 < baseStart_1797806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797820 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1797820 : Nat := 118140960795 + 1797820 * 2 ^ 59
def prefixEnd_1797820 : Nat := 4983230072969 + 3 ^ 40 * 1797820 * 2
def baseEnd_1797820 : Nat := 923145790266261254681983

theorem tailTrace_1797820 : CollatzResearch.WordTrace tailWord_1797820 prefixEnd_1797820 923145790266261254681983 := by
  unfold tailWord_1797820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32785941173406329028075457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43714588231208438704100609 32785941173406329028075457)
  ·
    refine ⟨24589455880054746771056593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32785941173406329028075457 24589455880054746771056593)
    ·
      refine ⟨18442091910041060078292445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24589455880054746771056593 18442091910041060078292445)
      ·
        refine ⟨6915784466265397529359667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18442091910041060078292445 6915784466265397529359667)
        ·
          refine ⟨10373676699398096294039501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915784466265397529359667 10373676699398096294039501)
          ·
            refine ⟨3890128762274286110264813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10373676699398096294039501 3890128762274286110264813)
            ·
              refine ⟨1458798285852857291349305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3890128762274286110264813 1458798285852857291349305)
              ·
                refine ⟨1094098714389642968511979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458798285852857291349305 1094098714389642968511979)
                ·
                  refine ⟨1641148071584464452767969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094098714389642968511979 1641148071584464452767969)
                  ·
                    refine ⟨1230861053688348339575977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641148071584464452767969 1230861053688348339575977)
                    ·
                      refine ⟨923145790266261254681983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1230861053688348339575977 923145790266261254681983)
                      ·
                        rfl

theorem cell23_1797820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1797820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797820 prefixEnd_1797820 := by exact prefixLift 1797820
  have htrace : WordTrace (prefixWord ++ tailWord_1797820) baseStart_1797820 baseEnd_1797820 := by
    simpa [prefixWord, tailWord_1797820, baseEnd_1797820] using wordTrace_append hprefix tailTrace_1797820
  have hstable : (prefixWord ++ tailWord_1797820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797820).length < 2 ^ (prefixWord ++ tailWord_1797820).sum := by decide
  have hdescent : baseEnd_1797820 < baseStart_1797820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797830 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1797830 : Nat := 118140960795 + 1797830 * 2 ^ 59
def prefixEnd_1797830 : Nat := 4983230072969 + 3 ^ 40 * 1797830 * 2
def baseEnd_1797830 : Nat := 307716975024268738518979

theorem tailTrace_1797830 : CollatzResearch.WordTrace tailWord_1797830 prefixEnd_1797830 307716975024268738518979 := by
  unfold tailWord_1797830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049132721149263430125467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43714831384517619842676629 2049132721149263430125467)
  ·
    refine ⟨3073699081723895145188201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2049132721149263430125467 3073699081723895145188201)
    ·
      refine ⟨2305274311292921358891151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3073699081723895145188201 2305274311292921358891151)
      ·
        refine ⟨3457911466939382038336727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305274311292921358891151 3457911466939382038336727)
        ·
          refine ⟨5186867200409073057505091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457911466939382038336727 5186867200409073057505091)
          ·
            refine ⟨7780300800613609586257637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186867200409073057505091 7780300800613609586257637)
            ·
              refine ⟨1458806400115051797423307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7780300800613609586257637 1458806400115051797423307)
              ·
                refine ⟨2188209600172577696134961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458806400115051797423307 2188209600172577696134961)
                ·
                  refine ⟨1641157200129433272101221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2188209600172577696134961 1641157200129433272101221)
                  ·
                    refine ⟨307716975024268738518979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641157200129433272101221 307716975024268738518979)
                    ·
                      rfl

theorem cell23_1797830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1797830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797830 prefixEnd_1797830 := by exact prefixLift 1797830
  have htrace : WordTrace (prefixWord ++ tailWord_1797830) baseStart_1797830 baseEnd_1797830 := by
    simpa [prefixWord, tailWord_1797830, baseEnd_1797830] using wordTrace_append hprefix tailTrace_1797830
  have hstable : (prefixWord ++ tailWord_1797830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797830).length < 2 ^ (prefixWord ++ tailWord_1797830).sum := by decide
  have hdescent : baseEnd_1797830 < baseStart_1797830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797835 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 2, 6]
def baseStart_1797835 : Nat := 118140960795 + 1797835 * 2 ^ 59
def prefixEnd_1797835 : Nat := 4983230072969 + 3 ^ 40 * 1797835 * 2
def baseEnd_1797835 : Nat := 307717830825359565331471

theorem tailTrace_1797835 : CollatzResearch.WordTrace tailWord_1797835 prefixEnd_1797835 307717830825359565331471 := by
  unfold tailWord_1797835
  simp only [CollatzResearch.WordTrace]
  refine ⟨65572429441758315617946959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43714952961172210411964639 65572429441758315617946959)
  ·
    refine ⟨98358644162637473426920439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65572429441758315617946959 98358644162637473426920439)
    ·
      refine ⟨147537966243956210140380659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98358644162637473426920439 147537966243956210140380659)
      ·
        refine ⟨221306949365934315210570989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147537966243956210140380659 221306949365934315210570989)
        ·
          refine ⟨82990106012225368203964121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221306949365934315210570989 82990106012225368203964121)
          ·
            refine ⟨62242579509169026152973091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82990106012225368203964121 62242579509169026152973091)
            ·
              refine ⟨93363869263753539229459637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62242579509169026152973091 93363869263753539229459637)
              ·
                refine ⟨8752862743476894302761841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93363869263753539229459637 8752862743476894302761841)
                ·
                  refine ⟨6564647057607670727071381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8752862743476894302761841 6564647057607670727071381)
                  ·
                    refine ⟨307717830825359565331471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6564647057607670727071381 307717830825359565331471)
                    ·
                      rfl

theorem cell23_1797835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_1797835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797835 prefixEnd_1797835 := by exact prefixLift 1797835
  have htrace : WordTrace (prefixWord ++ tailWord_1797835) baseStart_1797835 baseEnd_1797835 := by
    simpa [prefixWord, tailWord_1797835, baseEnd_1797835] using wordTrace_append hprefix tailTrace_1797835
  have hstable : (prefixWord ++ tailWord_1797835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797835).length < 2 ^ (prefixWord ++ tailWord_1797835).sum := by decide
  have hdescent : baseEnd_1797835 < baseStart_1797835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797875 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_1797875 : Nat := 118140960795 + 1797875 * 2 ^ 59
def prefixEnd_1797875 : Nat := 4983230072969 + 3 ^ 40 * 1797875 * 2
def baseEnd_1797875 : Nat := 923174031702258539494229

theorem tailTrace_1797875 : CollatzResearch.WordTrace tailWord_1797875 prefixEnd_1797875 923174031702258539494229 := by
  unfold tailWord_1797875
  simp only [CollatzResearch.WordTrace]
  refine ⟨65573888361613402449403079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43715925574408934966268719 65573888361613402449403079)
  ·
    refine ⟨98360832542420103674104619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65573888361613402449403079 98360832542420103674104619)
    ·
      refine ⟨147541248813630155511156929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98360832542420103674104619 147541248813630155511156929)
      ·
        refine ⟨110655936610222616633367697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147541248813630155511156929 110655936610222616633367697)
        ·
          refine ⟨82991952457666962475025773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110655936610222616633367697 82991952457666962475025773)
          ·
            refine ⟨31121982171625110928134665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82991952457666962475025773 31121982171625110928134665)
            ·
              refine ⟨23341486628718833196100999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31121982171625110928134665 23341486628718833196100999)
              ·
                refine ⟨35012229943078249794151499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23341486628718833196100999 35012229943078249794151499)
                ·
                  refine ⟨52518344914617374691227249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35012229943078249794151499 52518344914617374691227249)
                  ·
                    refine ⟨39388758685963031018420437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52518344914617374691227249 39388758685963031018420437)
                    ·
                      refine ⟨923174031702258539494229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39388758685963031018420437 923174031702258539494229)
                      ·
                        rfl

theorem cell23_1797875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_1797875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797875 prefixEnd_1797875 := by exact prefixLift 1797875
  have htrace : WordTrace (prefixWord ++ tailWord_1797875) baseStart_1797875 baseEnd_1797875 := by
    simpa [prefixWord, tailWord_1797875, baseEnd_1797875] using wordTrace_append hprefix tailTrace_1797875
  have hstable : (prefixWord ++ tailWord_1797875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797875).length < 2 ^ (prefixWord ++ tailWord_1797875).sum := by decide
  have hdescent : baseEnd_1797875 < baseStart_1797875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797876 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1797876 : Nat := 118140960795 + 1797876 * 2 ^ 59
def prefixEnd_1797876 : Nat := 4983230072969 + 3 ^ 40 * 1797876 * 2
def baseEnd_1797876 : Nat := 923174545182913035581725

theorem tailTrace_1797876 : CollatzResearch.WordTrace tailWord_1797876 prefixEnd_1797876 923174545182913035581725 := by
  unfold tailWord_1797876
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786962417304889810094741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43715949889739853080126321 32786962417304889810094741)
  ·
    refine ⟨1536888863311166709848191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32786962417304889810094741 1536888863311166709848191)
    ·
      refine ⟨2305333294966750064772287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1536888863311166709848191 2305333294966750064772287)
      ·
        refine ⟨3457999942450125097158431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305333294966750064772287 3457999942450125097158431)
        ·
          refine ⟨5186999913675187645737647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457999942450125097158431 5186999913675187645737647)
          ·
            refine ⟨7780499870512781468606471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186999913675187645737647 7780499870512781468606471)
            ·
              refine ⟨11670749805769172202909707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780499870512781468606471 11670749805769172202909707)
              ·
                refine ⟨17506124708653758304364561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11670749805769172202909707 17506124708653758304364561)
                ·
                  refine ⟨13129593531490318728273421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17506124708653758304364561 13129593531490318728273421)
                  ·
                    refine ⟨4923597574308869523102533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13129593531490318728273421 4923597574308869523102533)
                    ·
                      refine ⟨923174545182913035581725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4923597574308869523102533 923174545182913035581725)
                      ·
                        rfl

theorem cell23_1797876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1797876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797876 prefixEnd_1797876 := by exact prefixLift 1797876
  have htrace : WordTrace (prefixWord ++ tailWord_1797876) baseStart_1797876 baseEnd_1797876 := by
    simpa [prefixWord, tailWord_1797876, baseEnd_1797876] using wordTrace_append hprefix tailTrace_1797876
  have hstable : (prefixWord ++ tailWord_1797876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797876).length < 2 ^ (prefixWord ++ tailWord_1797876).sum := by decide
  have hdescent : baseEnd_1797876 < baseStart_1797876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797949 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1797949 : Nat := 118140960795 + 1797949 * 2 ^ 59
def prefixEnd_1797949 : Nat := 4983230072969 + 3 ^ 40 * 1797949 * 2
def baseEnd_1797949 : Nat := 923212029270691249968889

theorem tailTrace_1797949 : CollatzResearch.WordTrace tailWord_1797949 prefixEnd_1797949 923212029270691249968889 := by
  unfold tailWord_1797949
  simp only [CollatzResearch.WordTrace]
  refine ⟨65576587363345313087596901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43717724908896875391731267 65576587363345313087596901)
  ·
    refine ⟨12295610130627246203924419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65576587363345313087596901 12295610130627246203924419)
    ·
      refine ⟨18443415195940869305886629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12295610130627246203924419 18443415195940869305886629)
      ·
        refine ⟨3458140349238912994853743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18443415195940869305886629 3458140349238912994853743)
        ·
          refine ⟨5187210523858369492280615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458140349238912994853743 5187210523858369492280615)
          ·
            refine ⟨7780815785787554238420923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187210523858369492280615 7780815785787554238420923)
            ·
              refine ⟨11671223678681331357631385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780815785787554238420923 11671223678681331357631385)
              ·
                refine ⟨8753417759010998518223539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11671223678681331357631385 8753417759010998518223539)
                ·
                  refine ⟨13130126638516497777335309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753417759010998518223539 13130126638516497777335309)
                  ·
                    refine ⟨4923797489443686666500741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13130126638516497777335309 4923797489443686666500741)
                    ·
                      refine ⟨923212029270691249968889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4923797489443686666500741 923212029270691249968889)
                      ·
                        rfl

theorem cell23_1797949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1797949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797949 prefixEnd_1797949 := by exact prefixLift 1797949
  have htrace : WordTrace (prefixWord ++ tailWord_1797949) baseStart_1797949 baseEnd_1797949 := by
    simpa [prefixWord, tailWord_1797949, baseEnd_1797949] using wordTrace_append hprefix tailTrace_1797949
  have hstable : (prefixWord ++ tailWord_1797949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797949).length < 2 ^ (prefixWord ++ tailWord_1797949).sum := by decide
  have hdescent : baseEnd_1797949 < baseStart_1797949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797959 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1797959 : Nat := 118140960795 + 1797959 * 2 ^ 59
def prefixEnd_1797959 : Nat := 4983230072969 + 3 ^ 40 * 1797959 * 2
def baseEnd_1797959 : Nat := 307739054692412070281281

theorem tailTrace_1797959 : CollatzResearch.WordTrace tailWord_1797959 prefixEnd_1797959 307739054692412070281281 := by
  unfold tailWord_1797959
  simp only [CollatzResearch.WordTrace]
  refine ⟨65576952093309084795460931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43717968062206056530307287 65576952093309084795460931)
  ·
    refine ⟨98365428139963627193191397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65576952093309084795460931 98365428139963627193191397)
    ·
      refine ⟨18443517776243180098723387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98365428139963627193191397 18443517776243180098723387)
      ·
        refine ⟨27665276664364770148085081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18443517776243180098723387 27665276664364770148085081)
        ·
          refine ⟨20748957498273577611063811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27665276664364770148085081 20748957498273577611063811)
          ·
            refine ⟨31123436247410366416595717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20748957498273577611063811 31123436247410366416595717)
            ·
              refine ⟨5835644296389443703111697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31123436247410366416595717 5835644296389443703111697)
              ·
                refine ⟨4376733222292082777333773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5835644296389443703111697 4376733222292082777333773)
                ·
                  refine ⟨1641274958359531041500165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4376733222292082777333773 1641274958359531041500165)
                  ·
                    refine ⟨307739054692412070281281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1641274958359531041500165 307739054692412070281281)
                    ·
                      rfl

theorem cell23_1797959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1797959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797959 prefixEnd_1797959 := by exact prefixLift 1797959
  have htrace : WordTrace (prefixWord ++ tailWord_1797959) baseStart_1797959 baseEnd_1797959 := by
    simpa [prefixWord, tailWord_1797959, baseEnd_1797959] using wordTrace_append hprefix tailTrace_1797959
  have hstable : (prefixWord ++ tailWord_1797959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797959).length < 2 ^ (prefixWord ++ tailWord_1797959).sum := by decide
  have hdescent : baseEnd_1797959 < baseStart_1797959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797962 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1797962 : Nat := 118140960795 + 1797962 * 2 ^ 59
def prefixEnd_1797962 : Nat := 4983230072969 + 3 ^ 40 * 1797962 * 2
def baseEnd_1797962 : Nat := 923218704519199699106329

theorem tailTrace_1797962 : CollatzResearch.WordTrace tailWord_1797962 prefixEnd_1797962 923218704519199699106329 := by
  unfold tailWord_1797962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394265378074554076955035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43718041008198810871880093 16394265378074554076955035)
  ·
    refine ⟨24591398067111831115432553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16394265378074554076955035 24591398067111831115432553)
    ·
      refine ⟨18443548550333873336574415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24591398067111831115432553 18443548550333873336574415)
      ·
        refine ⟨27665322825500810004861623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18443548550333873336574415 27665322825500810004861623)
        ·
          refine ⟨41497984238251215007292435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27665322825500810004861623 41497984238251215007292435)
          ·
            refine ⟨62246976357376822510938653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41497984238251215007292435 62246976357376822510938653)
            ·
              refine ⟨23342616134016308441601995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62246976357376822510938653 23342616134016308441601995)
              ·
                refine ⟨35013924201024462662402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23342616134016308441601995 35013924201024462662402993)
                ·
                  refine ⟨26260443150768346996802245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35013924201024462662402993 26260443150768346996802245)
                  ·
                    refine ⟨4923833090769065061900421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26260443150768346996802245 4923833090769065061900421)
                    ·
                      refine ⟨923218704519199699106329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4923833090769065061900421 923218704519199699106329)
                      ·
                        rfl

theorem cell23_1797962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1797962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797962 prefixEnd_1797962 := by exact prefixLift 1797962
  have htrace : WordTrace (prefixWord ++ tailWord_1797962) baseStart_1797962 baseEnd_1797962 := by
    simpa [prefixWord, tailWord_1797962, baseEnd_1797962] using wordTrace_append hprefix tailTrace_1797962
  have hstable : (prefixWord ++ tailWord_1797962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797962).length < 2 ^ (prefixWord ++ tailWord_1797962).sum := by decide
  have hdescent : baseEnd_1797962 < baseStart_1797962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797969 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_1797969 : Nat := 118140960795 + 1797969 * 2 ^ 59
def prefixEnd_1797969 : Nat := 4983230072969 + 3 ^ 40 * 1797969 * 2
def baseEnd_1797969 : Nat := 923222298883781171718797

theorem tailTrace_1797969 : CollatzResearch.WordTrace tailWord_1797969 prefixEnd_1797969 923222298883781171718797 := by
  unfold tailWord_1797969
  simp only [CollatzResearch.WordTrace]
  refine ⟨65577316823272856503324961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43718211215515237668883307 65577316823272856503324961)
  ·
    refine ⟨49182987617454642377493721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65577316823272856503324961 49182987617454642377493721)
    ·
      refine ⟨36887240713090981783120291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49182987617454642377493721 36887240713090981783120291)
      ·
        refine ⟨55330861069636472674680437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36887240713090981783120291 55330861069636472674680437)
        ·
          refine ⟨5187268225278419313251291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55330861069636472674680437 5187268225278419313251291)
          ·
            refine ⟨7780902337917628969876937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187268225278419313251291 7780902337917628969876937)
            ·
              refine ⟨5835676753438221727407703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780902337917628969876937 5835676753438221727407703)
              ·
                refine ⟨8753515130157332591111555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835676753438221727407703 8753515130157332591111555)
                ·
                  refine ⟨13130272695235998886667333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8753515130157332591111555 13130272695235998886667333)
                  ·
                    refine ⟨2461926130356749791250125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13130272695235998886667333 2461926130356749791250125)
                    ·
                      refine ⟨923222298883781171718797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461926130356749791250125 923222298883781171718797)
                      ·
                        rfl

theorem cell23_1797969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_1797969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797969 prefixEnd_1797969 := by exact prefixLift 1797969
  have htrace : WordTrace (prefixWord ++ tailWord_1797969) baseStart_1797969 baseEnd_1797969 := by
    simpa [prefixWord, tailWord_1797969, baseEnd_1797969] using wordTrace_append hprefix tailTrace_1797969
  have hstable : (prefixWord ++ tailWord_1797969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797969).length < 2 ^ (prefixWord ++ tailWord_1797969).sum := by decide
  have hdescent : baseEnd_1797969 < baseStart_1797969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1797986 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1797986 : Nat := 118140960795 + 1797986 * 2 ^ 59
def prefixEnd_1797986 : Nat := 4983230072969 + 3 ^ 40 * 1797986 * 2
def baseEnd_1797986 : Nat := 923231028054907605206219

theorem tailTrace_1797986 : CollatzResearch.WordTrace tailWord_1797986 prefixEnd_1797986 923231028054907605206219 := by
  unfold tailWord_1797986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394484216052817101673453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43718624576140845604462541 16394484216052817101673453)
  ·
    refine ⟨6147931581019806413127545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16394484216052817101673453 6147931581019806413127545)
    ·
      refine ⟨4610948685764854809845659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6147931581019806413127545 4610948685764854809845659)
      ·
        refine ⟨6916423028647282214768489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610948685764854809845659 6916423028647282214768489)
        ·
          refine ⟨5187317271485461661076367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6916423028647282214768489 5187317271485461661076367)
          ·
            refine ⟨7780975907228192491614551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187317271485461661076367 7780975907228192491614551)
            ·
              refine ⟨11671463860842288737421827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7780975907228192491614551 11671463860842288737421827)
              ·
                refine ⟨17507195791263433106132741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11671463860842288737421827 17507195791263433106132741)
                ·
                  refine ⟨3282599210861893707399889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17507195791263433106132741 3282599210861893707399889)
                  ·
                    refine ⟨2461949408146420280549917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3282599210861893707399889 2461949408146420280549917)
                    ·
                      refine ⟨923231028054907605206219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2461949408146420280549917 923231028054907605206219)
                      ·
                        rfl

theorem cell23_1797986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1797986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1797986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1797986 prefixEnd_1797986 := by exact prefixLift 1797986
  have htrace : WordTrace (prefixWord ++ tailWord_1797986) baseStart_1797986 baseEnd_1797986 := by
    simpa [prefixWord, tailWord_1797986, baseEnd_1797986] using wordTrace_append hprefix tailTrace_1797986
  have hstable : (prefixWord ++ tailWord_1797986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1797986).length < 2 ^ (prefixWord ++ tailWord_1797986).sum := by decide
  have hdescent : baseEnd_1797986 < baseStart_1797986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1797986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798002 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_1798002 : Nat := 118140960795 + 1798002 * 2 ^ 59
def prefixEnd_1798002 : Nat := 4983230072969 + 3 ^ 40 * 1798002 * 2
def baseEnd_1798002 : Nat := 307746414581793180868715

theorem tailTrace_1798002 : CollatzResearch.WordTrace tailWord_1798002 prefixEnd_1798002 307746414581793180868715 := by
  unfold tailWord_1798002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394630108038325784819065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43719013621435535426184173 16394630108038325784819065)
  ·
    refine ⟨12295972581028744338614299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16394630108038325784819065 12295972581028744338614299)
    ·
      refine ⟨18443958871543116507921449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12295972581028744338614299 18443958871543116507921449)
      ·
        refine ⟨13832969153657337380941087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18443958871543116507921449 13832969153657337380941087)
        ·
          refine ⟨20749453730486006071411631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13832969153657337380941087 20749453730486006071411631)
          ·
            refine ⟨31124180595729009107117447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20749453730486006071411631 31124180595729009107117447)
            ·
              refine ⟨46686270893593513660676171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31124180595729009107117447 46686270893593513660676171)
              ·
                refine ⟨70029406340390270491014257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46686270893593513660676171 70029406340390270491014257)
                ·
                  refine ⟨52522054755292702868260693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70029406340390270491014257 52522054755292702868260693)
                  ·
                    refine ⟨307746414581793180868715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 52522054755292702868260693 307746414581793180868715)
                    ·
                      rfl

theorem cell23_1798002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_1798002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798002 prefixEnd_1798002 := by exact prefixLift 1798002
  have htrace : WordTrace (prefixWord ++ tailWord_1798002) baseStart_1798002 baseEnd_1798002 := by
    simpa [prefixWord, tailWord_1798002, baseEnd_1798002] using wordTrace_append hprefix tailTrace_1798002
  have hstable : (prefixWord ++ tailWord_1798002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798002).length < 2 ^ (prefixWord ++ tailWord_1798002).sum := by decide
  have hdescent : baseEnd_1798002 < baseStart_1798002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798019 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 3, 5]
def baseStart_1798019 : Nat := 118140960795 + 1798019 * 2 ^ 59
def prefixEnd_1798019 : Nat := 4983230072969 + 3 ^ 40 * 1798019 * 2
def baseEnd_1798019 : Nat := 307749324305501992031189

theorem tailTrace_1798019 : CollatzResearch.WordTrace tailWord_1798019 prefixEnd_1798019 307749324305501992031189 := by
  unfold tailWord_1798019
  simp only [CollatzResearch.WordTrace]
  refine ⟨65579140473091715042645111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43719426982061143361763407 65579140473091715042645111)
  ·
    refine ⟨98368710709637572563967667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65579140473091715042645111 98368710709637572563967667)
    ·
      refine ⟨147553066064456358845951501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98368710709637572563967667 147553066064456358845951501)
      ·
        refine ⟨55332399774171134567231813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147553066064456358845951501 55332399774171134567231813)
        ·
          refine ⟨10374824957657087731355965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55332399774171134567231813 10374824957657087731355965)
          ·
            refine ⟨3890559359121407899258487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10374824957657087731355965 3890559359121407899258487)
            ·
              refine ⟨5835839038682111848887731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890559359121407899258487 5835839038682111848887731)
              ·
                refine ⟨8753758558023167773331597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835839038682111848887731 8753758558023167773331597)
                ·
                  refine ⟨3282659459258687914999349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8753758558023167773331597 3282659459258687914999349)
                  ·
                    refine ⟨307749324305501992031189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3282659459258687914999349 307749324305501992031189)
                    ·
                      rfl

theorem cell23_1798019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 5].length) (baseStart_1798019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798019 prefixEnd_1798019 := by exact prefixLift 1798019
  have htrace : WordTrace (prefixWord ++ tailWord_1798019) baseStart_1798019 baseEnd_1798019 := by
    simpa [prefixWord, tailWord_1798019, baseEnd_1798019] using wordTrace_append hprefix tailTrace_1798019
  have hstable : (prefixWord ++ tailWord_1798019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798019).length < 2 ^ (prefixWord ++ tailWord_1798019).sum := by decide
  have hdescent : baseEnd_1798019 < baseStart_1798019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_1798032 : Nat := 118140960795 + 1798032 * 2 ^ 59
def prefixEnd_1798032 : Nat := 4983230072969 + 3 ^ 40 * 1798032 * 2
def baseEnd_1798032 : Nat := 307751549388338141743669

theorem tailTrace_1798032 : CollatzResearch.WordTrace tailWord_1798032 prefixEnd_1798032 307751549388338141743669 := by
  unfold tailWord_1798032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789807311022309131434175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43719743081363078841912233 32789807311022309131434175)
  ·
    refine ⟨49184710966533463697151263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789807311022309131434175 49184710966533463697151263)
    ·
      refine ⟨73777066449800195545726895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49184710966533463697151263 73777066449800195545726895)
      ·
        refine ⟨110665599674700293318590343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73777066449800195545726895 110665599674700293318590343)
        ·
          refine ⟨165998399512050439977885515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110665599674700293318590343 165998399512050439977885515)
          ·
            refine ⟨248997599268075659966828273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165998399512050439977885515 248997599268075659966828273)
            ·
              refine ⟨186748199451056744975121205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248997599268075659966828273 186748199451056744975121205)
              ·
                refine ⟨17507643698536569841417613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186748199451056744975121205 17507643698536569841417613)
                ·
                  refine ⟨6565366386951213690531605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17507643698536569841417613 6565366386951213690531605)
                  ·
                    refine ⟨307751549388338141743669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6565366386951213690531605 307751549388338141743669)
                    ·
                      rfl

theorem cell23_1798032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_1798032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798032 prefixEnd_1798032 := by exact prefixLift 1798032
  have htrace : WordTrace (prefixWord ++ tailWord_1798032) baseStart_1798032 baseEnd_1798032 := by
    simpa [prefixWord, tailWord_1798032, baseEnd_1798032] using wordTrace_append hprefix tailTrace_1798032
  have hstable : (prefixWord ++ tailWord_1798032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798032).length < 2 ^ (prefixWord ++ tailWord_1798032).sum := by decide
  have hdescent : baseEnd_1798032 < baseStart_1798032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1798073 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1798073 : Nat := 118140960795 + 1798073 * 2 ^ 59
def prefixEnd_1798073 : Nat := 4983230072969 + 3 ^ 40 * 1798073 * 2
def baseEnd_1798073 : Nat := 923275700871848764818319

theorem tailTrace_1798073 : CollatzResearch.WordTrace tailWord_1798073 prefixEnd_1798073 923275700871848764818319 := by
  unfold tailWord_1798073
  simp only [CollatzResearch.WordTrace]
  refine ⟨65581110014896082265110873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43720740009930721510073915 65581110014896082265110873)
  ·
    refine ⟨49185832511172061698833155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65581110014896082265110873 49185832511172061698833155)
    ·
      refine ⟨73778748766758092548249733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49185832511172061698833155 73778748766758092548249733)
      ·
        refine ⟨13833515393767142352796825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73778748766758092548249733 13833515393767142352796825)
        ·
          refine ⟨10375136545325356764597619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13833515393767142352796825 10375136545325356764597619)
          ·
            refine ⟨15562704817988035146896429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10375136545325356764597619 15562704817988035146896429)
            ·
              refine ⟨5836014306745513180086161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15562704817988035146896429 5836014306745513180086161)
              ·
                refine ⟨4377010730059134885064621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5836014306745513180086161 4377010730059134885064621)
                ·
                  refine ⟨1641379023772175581899233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4377010730059134885064621 1641379023772175581899233)
                  ·
                    refine ⟨1231034267829131686424425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1641379023772175581899233 1231034267829131686424425)
                    ·
                      refine ⟨923275700871848764818319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1231034267829131686424425 923275700871848764818319)
                      ·
                        rfl

theorem cell23_1798073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1798073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1798073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1798073 prefixEnd_1798073 := by exact prefixLift 1798073
  have htrace : WordTrace (prefixWord ++ tailWord_1798073) baseStart_1798073 baseEnd_1798073 := by
    simpa [prefixWord, tailWord_1798073, baseEnd_1798073] using wordTrace_append hprefix tailTrace_1798073
  have hstable : (prefixWord ++ tailWord_1798073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1798073).length < 2 ^ (prefixWord ++ tailWord_1798073).sum := by decide
  have hdescent : baseEnd_1798073 < baseStart_1798073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1798073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
