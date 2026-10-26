import V185TrunkScan21Chunk106

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1300260 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1300260 : Nat := 118140960795 + 1300260 * 2 ^ 59
def prefixEnd_1300260 : Nat := 4983230072969 + 3 ^ 40 * 1300260 * 2
def baseEnd_1300260 : Nat := 296737047028972426875653

theorem tailTrace_1300260 : CollatzResearch.WordTrace tailWord_1300260 prefixEnd_1300260 296737047028972426875653 := by
  unfold tailWord_1300260
  simp only [CollatzResearch.WordTrace]
  refine ⟨23712189134693780786737117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31616252179591707715649489 23712189134693780786737117)
  ·
    refine ⟨8892070925510167795026419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23712189134693780786737117 8892070925510167795026419)
    ·
      refine ⟨13338106388265251692539629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8892070925510167795026419 13338106388265251692539629)
      ·
        refine ⟨5001789895599469384702361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13338106388265251692539629 5001789895599469384702361)
        ·
          refine ⟨3751342421699602038526771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5001789895599469384702361 3751342421699602038526771)
          ·
            refine ⟨5627013632549403057790157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751342421699602038526771 5627013632549403057790157)
            ·
              refine ⟨2110130112206026146671309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5627013632549403057790157 2110130112206026146671309)
              ·
                refine ⟨791298792077259805001741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2110130112206026146671309 791298792077259805001741)
                ·
                  refine ⟨296737047028972426875653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791298792077259805001741 296737047028972426875653)
                  ·
                    rfl

theorem cell21_1300260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1300260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300260 prefixEnd_1300260 := by exact prefixLift 1300260
  have htrace : WordTrace (prefixWord ++ tailWord_1300260) baseStart_1300260 baseEnd_1300260 := by
    simpa [prefixWord, tailWord_1300260, baseEnd_1300260] using wordTrace_append hprefix tailTrace_1300260
  have hstable : (prefixWord ++ tailWord_1300260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300260).length < 2 ^ (prefixWord ++ tailWord_1300260).sum := by decide
  have hdescent : baseEnd_1300260 < baseStart_1300260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300277 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 3]
def baseStart_1300277 : Nat := 118140960795 + 1300277 * 2 ^ 59
def prefixEnd_1300277 : Nat := 4983230072969 + 3 ^ 40 * 1300277 * 2
def baseEnd_1300277 : Nat := 296740926660584175092285

theorem tailTrace_1300277 : CollatzResearch.WordTrace tailWord_1300277 prefixEnd_1300277 296740926660584175092285 := by
  unfold tailWord_1300277
  simp only [CollatzResearch.WordTrace]
  refine ⟨47424998310325973476843085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31616665540217315651228723 47424998310325973476843085)
  ·
    refine ⟨17784374366372240053816157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47424998310325973476843085 17784374366372240053816157)
    ·
      refine ⟨6669140387389590020181059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17784374366372240053816157 6669140387389590020181059)
      ·
        refine ⟨10003710581084385030271589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6669140387389590020181059 10003710581084385030271589)
        ·
          refine ⟨1875695733953322193175923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10003710581084385030271589 1875695733953322193175923)
          ·
            refine ⟨2813543600929983289763885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875695733953322193175923 2813543600929983289763885)
            ·
              refine ⟨1055078850348743733661457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2813543600929983289763885 1055078850348743733661457)
              ·
                refine ⟨791309137761557800246093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055078850348743733661457 791309137761557800246093)
                ·
                  refine ⟨296740926660584175092285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791309137761557800246093 296740926660584175092285)
                  ·
                    rfl

theorem cell21_1300277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_1300277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300277 prefixEnd_1300277 := by exact prefixLift 1300277
  have htrace : WordTrace (prefixWord ++ tailWord_1300277) baseStart_1300277 baseEnd_1300277 := by
    simpa [prefixWord, tailWord_1300277, baseEnd_1300277] using wordTrace_append hprefix tailTrace_1300277
  have hstable : (prefixWord ++ tailWord_1300277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300277).length < 2 ^ (prefixWord ++ tailWord_1300277).sum := by decide
  have hdescent : baseEnd_1300277 < baseStart_1300277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300333 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1300333 : Nat := 118140960795 + 1300333 * 2 ^ 59
def prefixEnd_1300333 : Nat := 4983230072969 + 3 ^ 40 * 1300333 * 2
def baseEnd_1300333 : Nat := 296753706623540522158837

theorem tailTrace_1300333 : CollatzResearch.WordTrace tailWord_1300333 prefixEnd_1300333 296753706623540522158837 := by
  unfold tailWord_1300333
  simp only [CollatzResearch.WordTrace]
  refine ⟨47427040798123095040881653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31618027198748730027254435 47427040798123095040881653)
  ·
    refine ⟨4446285074824040160082655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47427040798123095040881653 4446285074824040160082655)
    ·
      refine ⟨6669427612236060240123983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446285074824040160082655 6669427612236060240123983)
      ·
        refine ⟨10004141418354090360185975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6669427612236060240123983 10004141418354090360185975)
        ·
          refine ⟨15006212127531135540278963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004141418354090360185975 15006212127531135540278963)
          ·
            refine ⟨22509318191296703310418445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15006212127531135540278963 22509318191296703310418445)
            ·
              refine ⟨8440994321736263741406917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22509318191296703310418445 8440994321736263741406917)
              ·
                refine ⟨1582686435325549451513797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8440994321736263741406917 1582686435325549451513797)
                ·
                  refine ⟨296753706623540522158837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1582686435325549451513797 296753706623540522158837)
                  ·
                    rfl

theorem cell21_1300333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1300333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300333 prefixEnd_1300333 := by exact prefixLift 1300333
  have htrace : WordTrace (prefixWord ++ tailWord_1300333) baseStart_1300333 baseEnd_1300333 := by
    simpa [prefixWord, tailWord_1300333, baseEnd_1300333] using wordTrace_append hprefix tailTrace_1300333
  have hstable : (prefixWord ++ tailWord_1300333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300333).length < 2 ^ (prefixWord ++ tailWord_1300333).sum := by decide
  have hdescent : baseEnd_1300333 < baseStart_1300333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300530 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1300530 : Nat := 118140960795 + 1300530 * 2 ^ 59
def prefixEnd_1300530 : Nat := 4983230072969 + 3 ^ 40 * 1300530 * 2
def baseEnd_1300530 : Nat := 296798664707511957375101

theorem tailTrace_1300530 : CollatzResearch.WordTrace tailWord_1300530 prefixEnd_1300530 296798664707511957375101 := by
  unfold tailWord_1300530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11858556494602349421450761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31622817318939598457202029 11858556494602349421450761)
  ·
    refine ⟨8893917370951762066088071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11858556494602349421450761 8893917370951762066088071)
    ·
      refine ⟨13340876056427643099132107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8893917370951762066088071 13340876056427643099132107)
      ·
        refine ⟨20011314084641464648698161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13340876056427643099132107 20011314084641464648698161)
        ·
          refine ⟨15008485563481098486523621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20011314084641464648698161 15008485563481098486523621)
          ·
            refine ⟨2814091043152705966223179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15008485563481098486523621 2814091043152705966223179)
            ·
              refine ⟨4221136564729058949334769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814091043152705966223179 4221136564729058949334769)
              ·
                refine ⟨3165852423546794212001077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4221136564729058949334769 3165852423546794212001077)
                ·
                  refine ⟨296798664707511957375101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3165852423546794212001077 296798664707511957375101)
                  ·
                    rfl

theorem cell21_1300530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1300530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300530 prefixEnd_1300530 := by exact prefixLift 1300530
  have htrace : WordTrace (prefixWord ++ tailWord_1300530) baseStart_1300530 baseEnd_1300530 := by
    simpa [prefixWord, tailWord_1300530, baseEnd_1300530] using wordTrace_append hprefix tailTrace_1300530
  have hstable : (prefixWord ++ tailWord_1300530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300530).length < 2 ^ (prefixWord ++ tailWord_1300530).sum := by decide
  have hdescent : baseEnd_1300530 < baseStart_1300530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300592 : List Nat := [2, 1, 1, 1, 5, 4, 2, 5]
def baseStart_1300592 : Nat := 118140960795 + 1300592 * 2 ^ 59
def prefixEnd_1300592 : Nat := 4983230072969 + 3 ^ 40 * 1300592 * 2
def baseEnd_1300592 : Nat := 98937604650737875780547

theorem tailTrace_1300592 : CollatzResearch.WordTrace tailWord_1300592 prefixEnd_1300592 98937604650737875780547 := by
  unfold tailWord_1300592
  simp only [CollatzResearch.WordTrace]
  refine ⟨23718243652092391137280015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31624324869456521516373353 23718243652092391137280015)
  ·
    refine ⟨35577365478138586705920023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23718243652092391137280015 35577365478138586705920023)
    ·
      refine ⟨53366048217207880058880035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35577365478138586705920023 53366048217207880058880035)
      ·
        refine ⟨80049072325811820088320053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53366048217207880058880035 80049072325811820088320053)
        ·
          refine ⟨7504600530544858133280005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80049072325811820088320053 7504600530544858133280005)
          ·
            refine ⟨1407112599477160899990001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7504600530544858133280005 1407112599477160899990001)
            ·
              refine ⟨1055334449607870674992501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407112599477160899990001 1055334449607870674992501)
              ·
                refine ⟨98937604650737875780547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1055334449607870674992501 98937604650737875780547)
                ·
                  rfl

theorem cell21_1300592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_1300592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300592 prefixEnd_1300592 := by exact prefixLift 1300592
  have htrace : WordTrace (prefixWord ++ tailWord_1300592) baseStart_1300592 baseEnd_1300592 := by
    simpa [prefixWord, tailWord_1300592, baseEnd_1300592] using wordTrace_append hprefix tailTrace_1300592
  have hstable : (prefixWord ++ tailWord_1300592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300592).length < 2 ^ (prefixWord ++ tailWord_1300592).sum := by decide
  have hdescent : baseEnd_1300592 < baseStart_1300592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300637 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1300637 : Nat := 118140960795 + 1300637 * 2 ^ 59
def prefixEnd_1300637 : Nat := 4983230072969 + 3 ^ 40 * 1300637 * 2
def baseEnd_1300637 : Nat := 296823083565303549091549

theorem tailTrace_1300637 : CollatzResearch.WordTrace tailWord_1300637 prefixEnd_1300637 296823083565303549091549 := by
  unfold tailWord_1300637
  simp only [CollatzResearch.WordTrace]
  refine ⟨47438128589021754959948165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31625419059347836639965443 47438128589021754959948165)
  ·
    refine ⟨8894649110441579054990281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47438128589021754959948165 8894649110441579054990281)
    ·
      refine ⟨6670986832831184291242711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8894649110441579054990281 6670986832831184291242711)
      ·
        refine ⟨10006480249246776436864067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6670986832831184291242711 10006480249246776436864067)
        ·
          refine ⟨15009720373870164655296101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006480249246776436864067 15009720373870164655296101)
          ·
            refine ⟨2814322570100655872868019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15009720373870164655296101 2814322570100655872868019)
            ·
              refine ⟨4221483855150983809302029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814322570100655872868019 4221483855150983809302029)
              ·
                refine ⟨1583056445681618928488261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4221483855150983809302029 1583056445681618928488261)
                ·
                  refine ⟨296823083565303549091549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583056445681618928488261 296823083565303549091549)
                  ·
                    rfl

theorem cell21_1300637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1300637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300637 prefixEnd_1300637 := by exact prefixLift 1300637
  have htrace : WordTrace (prefixWord ++ tailWord_1300637) baseStart_1300637 baseEnd_1300637 := by
    simpa [prefixWord, tailWord_1300637, baseEnd_1300637] using wordTrace_append hprefix tailTrace_1300637
  have hstable : (prefixWord ++ tailWord_1300637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300637).length < 2 ^ (prefixWord ++ tailWord_1300637).sum := by decide
  have hdescent : baseEnd_1300637 < baseStart_1300637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300674 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1300674 : Nat := 118140960795 + 1300674 * 2 ^ 59
def prefixEnd_1300674 : Nat := 4983230072969 + 3 ^ 40 * 1300674 * 2
def baseEnd_1300674 : Nat := 296831527469399706974807

theorem tailTrace_1300674 : CollatzResearch.WordTrace tailWord_1300674 prefixEnd_1300674 296831527469399706974807 := by
  unfold tailWord_1300674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859869522471927569761269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31626318726591806852696717 11859869522471927569761269)
  ·
    refine ⟨1111862767731743209665119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11859869522471927569761269 1111862767731743209665119)
    ·
      refine ⟨1667794151597614814497679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111862767731743209665119 1667794151597614814497679)
      ·
        refine ⟨2501691227396422221746519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667794151597614814497679 2501691227396422221746519)
        ·
          refine ⟨3752536841094633332619779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501691227396422221746519 3752536841094633332619779)
          ·
            refine ⟨5628805261641949998929669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752536841094633332619779 5628805261641949998929669)
            ·
              refine ⟨1055400986557865624799313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5628805261641949998929669 1055400986557865624799313)
              ·
                refine ⟨791550739918399218599485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055400986557865624799313 791550739918399218599485)
                ·
                  refine ⟨296831527469399706974807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791550739918399218599485 296831527469399706974807)
                  ·
                    rfl

theorem cell21_1300674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1300674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300674 prefixEnd_1300674 := by exact prefixLift 1300674
  have htrace : WordTrace (prefixWord ++ tailWord_1300674) baseStart_1300674 baseEnd_1300674 := by
    simpa [prefixWord, tailWord_1300674, baseEnd_1300674] using wordTrace_append hprefix tailTrace_1300674
  have hstable : (prefixWord ++ tailWord_1300674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300674).length < 2 ^ (prefixWord ++ tailWord_1300674).sum := by decide
  have hdescent : baseEnd_1300674 < baseStart_1300674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300772 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1300772 : Nat := 118140960795 + 1300772 * 2 ^ 59
def prefixEnd_1300772 : Nat := 4983230072969 + 3 ^ 40 * 1300772 * 2
def baseEnd_1300772 : Nat := 296853892404573314341273

theorem tailTrace_1300772 : CollatzResearch.WordTrace tailWord_1300772 prefixEnd_1300772 296853892404573314341273 := by
  unfold tailWord_1300772
  simp only [CollatzResearch.WordTrace]
  refine ⟨23721526221766336508056285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31628701629021782010741713 23721526221766336508056285)
  ·
    refine ⟨8895572333162376190521107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23721526221766336508056285 8895572333162376190521107)
    ·
      refine ⟨13343358499743564285781661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895572333162376190521107 13343358499743564285781661)
      ·
        refine ⟨5003759437403836607168123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13343358499743564285781661 5003759437403836607168123)
        ·
          refine ⟨7505639156105754910752185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003759437403836607168123 7505639156105754910752185)
          ·
            refine ⟨5629229367079316183064139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7505639156105754910752185 5629229367079316183064139)
            ·
              refine ⟨8443844050618974274596209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629229367079316183064139 8443844050618974274596209)
              ·
                refine ⟨6332883037964230705947157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443844050618974274596209 6332883037964230705947157)
                ·
                  refine ⟨296853892404573314341273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6332883037964230705947157 296853892404573314341273)
                  ·
                    rfl

theorem cell21_1300772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1300772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300772 prefixEnd_1300772 := by exact prefixLift 1300772
  have htrace : WordTrace (prefixWord ++ tailWord_1300772) baseStart_1300772 baseEnd_1300772 := by
    simpa [prefixWord, tailWord_1300772, baseEnd_1300772] using wordTrace_append hprefix tailTrace_1300772
  have hstable : (prefixWord ++ tailWord_1300772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300772).length < 2 ^ (prefixWord ++ tailWord_1300772).sum := by decide
  have hdescent : baseEnd_1300772 < baseStart_1300772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300831 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_1300831 : Nat := 118140960795 + 1300831 * 2 ^ 59
def prefixEnd_1300831 : Nat := 4983230072969 + 3 ^ 40 * 1300831 * 2
def baseEnd_1300831 : Nat := 296867357008402322857819

theorem tailTrace_1300831 : CollatzResearch.WordTrace tailWord_1300831 prefixEnd_1300831 296867357008402322857819 := by
  unfold tailWord_1300831
  simp only [CollatzResearch.WordTrace]
  refine ⟨47445204350318926092510347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31630136233545950728340231 47445204350318926092510347)
  ·
    refine ⟨71167806525478389138765521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47445204350318926092510347 71167806525478389138765521)
    ·
      refine ⟨53375854894108791854074141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71167806525478389138765521 53375854894108791854074141)
      ·
        refine ⟨20015945585290796945277803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53375854894108791854074141 20015945585290796945277803)
        ·
          refine ⟨30023918377936195417916705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20015945585290796945277803 30023918377936195417916705)
          ·
            refine ⟨22517938783452146563437529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30023918377936195417916705 22517938783452146563437529)
            ·
              refine ⟨16888454087589109922578147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22517938783452146563437529 16888454087589109922578147)
              ·
                refine ⟨25332681131383664883867221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16888454087589109922578147 25332681131383664883867221)
                ·
                  refine ⟨296867357008402322857819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25332681131383664883867221 296867357008402322857819)
                  ·
                    rfl

theorem cell21_1300831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_1300831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300831 prefixEnd_1300831 := by exact prefixLift 1300831
  have htrace : WordTrace (prefixWord ++ tailWord_1300831) baseStart_1300831 baseEnd_1300831 := by
    simpa [prefixWord, tailWord_1300831, baseEnd_1300831] using wordTrace_append hprefix tailTrace_1300831
  have hstable : (prefixWord ++ tailWord_1300831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300831).length < 2 ^ (prefixWord ++ tailWord_1300831).sum := by decide
  have hdescent : baseEnd_1300831 < baseStart_1300831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300848 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1300848 : Nat := 118140960795 + 1300848 * 2 ^ 59
def prefixEnd_1300848 : Nat := 4983230072969 + 3 ^ 40 * 1300848 * 2
def baseEnd_1300848 : Nat := 296871236640014071074451

theorem tailTrace_1300848 : CollatzResearch.WordTrace tailWord_1300848 prefixEnd_1300848 296871236640014071074451 := by
  unfold tailWord_1300848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23722912195628668997939599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31630549594171558663919465 23722912195628668997939599)
  ·
    refine ⟨35584368293443003496909399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23722912195628668997939599 35584368293443003496909399)
    ·
      refine ⟨53376552440164505245364099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35584368293443003496909399 53376552440164505245364099)
      ·
        refine ⟨80064828660246757868046149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53376552440164505245364099 80064828660246757868046149)
        ·
          refine ⟨15012155373796267100258653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80064828660246757868046149 15012155373796267100258653)
          ·
            refine ⟨5629558265173600162596995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15012155373796267100258653 5629558265173600162596995)
            ·
              refine ⟨8444337397760400243895493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629558265173600162596995 8444337397760400243895493)
              ·
                refine ⟨1583313262080075045730405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8444337397760400243895493 1583313262080075045730405)
                ·
                  refine ⟨296871236640014071074451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583313262080075045730405 296871236640014071074451)
                  ·
                    rfl

theorem cell21_1300848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1300848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300848 prefixEnd_1300848 := by exact prefixLift 1300848
  have htrace : WordTrace (prefixWord ++ tailWord_1300848) baseStart_1300848 baseEnd_1300848 := by
    simpa [prefixWord, tailWord_1300848, baseEnd_1300848] using wordTrace_append hprefix tailTrace_1300848
  have hstable : (prefixWord ++ tailWord_1300848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300848).length < 2 ^ (prefixWord ++ tailWord_1300848).sum := by decide
  have hdescent : baseEnd_1300848 < baseStart_1300848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300854 : List Nat := [5, 1, 1, 4, 2, 1, 1, 6]
def baseStart_1300854 : Nat := 118140960795 + 1300854 * 2 ^ 59
def prefixEnd_1300854 : Nat := 4983230072969 + 3 ^ 40 * 1300854 * 2
def baseEnd_1300854 : Nat := 98957535307253131324813

theorem tailTrace_1300854 : CollatzResearch.WordTrace tailWord_1300854 prefixEnd_1300854 98957535307253131324813 := by
  unfold tailWord_1300854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965377701827225063787351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31630695486157067347065077 2965377701827225063787351)
  ·
    refine ⟨4448066552740837595681027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2965377701827225063787351 4448066552740837595681027)
    ·
      refine ⟨6672099829111256393521541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448066552740837595681027 6672099829111256393521541)
      ·
        refine ⟨1251018717958360573785289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6672099829111256393521541 1251018717958360573785289)
        ·
          refine ⟨938264038468770430338967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251018717958360573785289 938264038468770430338967)
          ·
            refine ⟨1407396057703155645508451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938264038468770430338967 1407396057703155645508451)
            ·
              refine ⟨2111094086554733468262677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407396057703155645508451 2111094086554733468262677)
              ·
                refine ⟨98957535307253131324813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2111094086554733468262677 98957535307253131324813)
                ·
                  rfl

theorem cell21_1300854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_1300854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300854 prefixEnd_1300854 := by exact prefixLift 1300854
  have htrace : WordTrace (prefixWord ++ tailWord_1300854) baseStart_1300854 baseEnd_1300854 := by
    simpa [prefixWord, tailWord_1300854, baseEnd_1300854] using wordTrace_append hprefix tailTrace_1300854
  have hstable : (prefixWord ++ tailWord_1300854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300854).length < 2 ^ (prefixWord ++ tailWord_1300854).sum := by decide
  have hdescent : baseEnd_1300854 < baseStart_1300854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300865 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_1300865 : Nat := 118140960795 + 1300865 * 2 ^ 59
def prefixEnd_1300865 : Nat := 4983230072969 + 3 ^ 40 * 1300865 * 2
def baseEnd_1300865 : Nat := 296875116271625819291083

theorem tailTrace_1300865 : CollatzResearch.WordTrace tailWord_1300865 prefixEnd_1300865 296875116271625819291083 := by
  unfold tailWord_1300865
  simp only [CollatzResearch.WordTrace]
  refine ⟨47446444432195749899248049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31630962954797166599498699 47446444432195749899248049)
  ·
    refine ⟨35584833324146812424436037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47446444432195749899248049 35584833324146812424436037)
    ·
      refine ⟨6672156248277527329581757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35584833324146812424436037 6672156248277527329581757)
      ·
        refine ⟨2502058593104072748593159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6672156248277527329581757 2502058593104072748593159)
        ·
          refine ⟨3753087889656109122889739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502058593104072748593159 3753087889656109122889739)
          ·
            refine ⟨5629631834484163684334609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753087889656109122889739 5629631834484163684334609)
            ·
              refine ⟨4222223875863122763250957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5629631834484163684334609 4222223875863122763250957)
              ·
                refine ⟨1583333953448671036219109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4222223875863122763250957 1583333953448671036219109)
                ·
                  refine ⟨296875116271625819291083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583333953448671036219109 296875116271625819291083)
                  ·
                    rfl

theorem cell21_1300865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_1300865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300865 prefixEnd_1300865 := by exact prefixLift 1300865
  have htrace : WordTrace (prefixWord ++ tailWord_1300865) baseStart_1300865 baseEnd_1300865 := by
    simpa [prefixWord, tailWord_1300865, baseEnd_1300865] using wordTrace_append hprefix tailTrace_1300865
  have hstable : (prefixWord ++ tailWord_1300865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300865).length < 2 ^ (prefixWord ++ tailWord_1300865).sum := by decide
  have hdescent : baseEnd_1300865 < baseStart_1300865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300916 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1300916 : Nat := 118140960795 + 1300916 * 2 ^ 59
def prefixEnd_1300916 : Nat := 4983230072969 + 3 ^ 40 * 1300916 * 2
def baseEnd_1300916 : Nat := 296886755166461063940979

theorem tailTrace_1300916 : CollatzResearch.WordTrace tailWord_1300916 prefixEnd_1300916 296886755166461063940979 := by
  unfold tailWord_1300916
  simp only [CollatzResearch.WordTrace]
  refine ⟨23724152277505492804677301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31632203036673990406236401 23724152277505492804677301)
  ·
    refine ⟨2224139276016139950438497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23724152277505492804677301 2224139276016139950438497)
    ·
      refine ⟨1668104457012104962828873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2224139276016139950438497 1668104457012104962828873)
      ·
        refine ⟨1251078342759078722121655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668104457012104962828873 1251078342759078722121655)
        ·
          refine ⟨1876617514138618083182483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251078342759078722121655 1876617514138618083182483)
          ·
            refine ⟨2814926271207927124773725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876617514138618083182483 2814926271207927124773725)
            ·
              refine ⟨1055597351702972671790147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2814926271207927124773725 1055597351702972671790147)
              ·
                refine ⟨1583396027554459007685221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055597351702972671790147 1583396027554459007685221)
                ·
                  refine ⟨296886755166461063940979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583396027554459007685221 296886755166461063940979)
                  ·
                    rfl

theorem cell21_1300916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1300916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300916 prefixEnd_1300916 := by exact prefixLift 1300916
  have htrace : WordTrace (prefixWord ++ tailWord_1300916) baseStart_1300916 baseEnd_1300916 := by
    simpa [prefixWord, tailWord_1300916, baseEnd_1300916] using wordTrace_append hprefix tailTrace_1300916
  have hstable : (prefixWord ++ tailWord_1300916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300916).length < 2 ^ (prefixWord ++ tailWord_1300916).sum := by decide
  have hdescent : baseEnd_1300916 < baseStart_1300916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300938 : List Nat := [3, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1300938 : Nat := 118140960795 + 1300938 * 2 ^ 59
def prefixEnd_1300938 : Nat := 4983230072969 + 3 ^ 40 * 1300938 * 2
def baseEnd_1300938 : Nat := 98963925288731304858089

theorem tailTrace_1300938 : CollatzResearch.WordTrace tailWord_1300938 prefixEnd_1300938 98963925288731304858089 := by
  unfold tailWord_1300938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862276740232820841663867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31632737973954188911103645 11862276740232820841663867)
  ·
    refine ⟨17793415110349231262495801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11862276740232820841663867 17793415110349231262495801)
    ·
      refine ⟨13345061332761923446871851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17793415110349231262495801 13345061332761923446871851)
      ·
        refine ⟨20017591999142885170307777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13345061332761923446871851 20017591999142885170307777)
        ·
          refine ⟨15013193999357163877730833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20017591999142885170307777 15013193999357163877730833)
          ·
            refine ⟨11259895499517872908298125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15013193999357163877730833 11259895499517872908298125)
            ·
              refine ⟨4222460812319202340611797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11259895499517872908298125 4222460812319202340611797)
              ·
                refine ⟨98963925288731304858089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4222460812319202340611797 98963925288731304858089)
                ·
                  rfl

theorem cell21_1300938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1300938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300938 prefixEnd_1300938 := by exact prefixLift 1300938
  have htrace : WordTrace (prefixWord ++ tailWord_1300938) baseStart_1300938 baseEnd_1300938 := by
    simpa [prefixWord, tailWord_1300938, baseEnd_1300938] using wordTrace_append hprefix tailTrace_1300938
  have hstable : (prefixWord ++ tailWord_1300938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300938).length < 2 ^ (prefixWord ++ tailWord_1300938).sum := by decide
  have hdescent : baseEnd_1300938 < baseStart_1300938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301020 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1301020 : Nat := 118140960795 + 1301020 * 2 ^ 59
def prefixEnd_1301020 : Nat := 4983230072969 + 3 ^ 40 * 1301020 * 2
def baseEnd_1301020 : Nat := 296910489383379994207433

theorem tailTrace_1301020 : CollatzResearch.WordTrace tailWord_1301020 prefixEnd_1301020 296910489383379994207433 := by
  unfold tailWord_1301020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726048873317105685570257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31634731831089474247427009 23726048873317105685570257)
  ·
    refine ⟨17794536654987829264177693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23726048873317105685570257 17794536654987829264177693)
    ·
      refine ⟨6672951245620435974066635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17794536654987829264177693 6672951245620435974066635)
      ·
        refine ⟨10009426868430653961099953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672951245620435974066635 10009426868430653961099953)
        ·
          refine ⟨7507070151322990470824965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10009426868430653961099953 7507070151322990470824965)
          ·
            refine ⟨1407575653373060713279681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7507070151322990470824965 1407575653373060713279681)
            ·
              refine ⟨1055681740029795534959761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407575653373060713279681 1055681740029795534959761)
              ·
                refine ⟨791761305022346651219821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055681740029795534959761 791761305022346651219821)
                ·
                  refine ⟨296910489383379994207433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791761305022346651219821 296910489383379994207433)
                  ·
                    rfl

theorem cell21_1301020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1301020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301020 prefixEnd_1301020 := by exact prefixLift 1301020
  have htrace : WordTrace (prefixWord ++ tailWord_1301020) baseStart_1301020 baseEnd_1301020 := by
    simpa [prefixWord, tailWord_1301020, baseEnd_1301020] using wordTrace_append hprefix tailTrace_1301020
  have hstable : (prefixWord ++ tailWord_1301020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301020).length < 2 ^ (prefixWord ++ tailWord_1301020).sum := by decide
  have hdescent : baseEnd_1301020 < baseStart_1301020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301045 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1301045 : Nat := 118140960795 + 1301045 * 2 ^ 59
def prefixEnd_1301045 : Nat := 4983230072969 + 3 ^ 40 * 1301045 * 2
def baseEnd_1301045 : Nat := 296916194723985506290715

theorem tailTrace_1301045 : CollatzResearch.WordTrace tailWord_1301045 prefixEnd_1301045 296916194723985506290715 := by
  unfold tailWord_1301045
  simp only [CollatzResearch.WordTrace]
  refine ⟨47453009571543640640800589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31635339714362427093867059 47453009571543640640800589)
  ·
    refine ⟨17794878589328865240300221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47453009571543640640800589 17794878589328865240300221)
    ·
      refine ⟨6673079470998324465112583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17794878589328865240300221 6673079470998324465112583)
      ·
        refine ⟨10009619206497486697668875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6673079470998324465112583 10009619206497486697668875)
        ·
          refine ⟨15014428809746230046503313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009619206497486697668875 15014428809746230046503313)
          ·
            refine ⟨11260821607309672534877485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15014428809746230046503313 11260821607309672534877485)
            ·
              refine ⟨4222808102741127200579057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11260821607309672534877485 4222808102741127200579057)
              ·
                refine ⟨3167106077055845400434293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4222808102741127200579057 3167106077055845400434293)
                ·
                  refine ⟨296916194723985506290715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3167106077055845400434293 296916194723985506290715)
                  ·
                    rfl

theorem cell21_1301045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1301045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301045 prefixEnd_1301045 := by exact prefixLift 1301045
  have htrace : WordTrace (prefixWord ++ tailWord_1301045) baseStart_1301045 baseEnd_1301045 := by
    simpa [prefixWord, tailWord_1301045, baseEnd_1301045] using wordTrace_append hprefix tailTrace_1301045
  have hstable : (prefixWord ++ tailWord_1301045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301045).length < 2 ^ (prefixWord ++ tailWord_1301045).sum := by decide
  have hdescent : baseEnd_1301045 < baseStart_1301045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301076 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1301076 : Nat := 118140960795 + 1301076 * 2 ^ 59
def prefixEnd_1301076 : Nat := 4983230072969 + 3 ^ 40 * 1301076 * 2
def baseEnd_1301076 : Nat := 296923269346336341273985

theorem tailTrace_1301076 : CollatzResearch.WordTrace tailWord_1301076 prefixEnd_1301076 296923269346336341273985 := by
  unfold tailWord_1301076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23727070117215666467589541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31636093489620888623452721 23727070117215666467589541)
  ·
    refine ⟨4448825646977937462673039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23727070117215666467589541 4448825646977937462673039)
    ·
      refine ⟨6673238470466906194009559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448825646977937462673039 6673238470466906194009559)
      ·
        refine ⟨10009857705700359291014339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6673238470466906194009559 10009857705700359291014339)
        ·
          refine ⟨15014786558550538936521509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009857705700359291014339 15014786558550538936521509)
          ·
            refine ⟨2815272479728226050597783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15014786558550538936521509 2815272479728226050597783)
            ·
              refine ⟨4222908719592339075896675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815272479728226050597783 4222908719592339075896675)
              ·
                refine ⟨6334363079388508613845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222908719592339075896675 6334363079388508613845013)
                ·
                  refine ⟨296923269346336341273985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6334363079388508613845013 296923269346336341273985)
                  ·
                    rfl

theorem cell21_1301076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1301076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301076 prefixEnd_1301076 := by exact prefixLift 1301076
  have htrace : WordTrace (prefixWord ++ tailWord_1301076) baseStart_1301076 baseEnd_1301076 := by
    simpa [prefixWord, tailWord_1301076, baseEnd_1301076] using wordTrace_append hprefix tailTrace_1301076
  have hstable : (prefixWord ++ tailWord_1301076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301076).length < 2 ^ (prefixWord ++ tailWord_1301076).sum := by decide
  have hdescent : baseEnd_1301076 < baseStart_1301076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301138 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1301138 : Nat := 118140960795 + 1301138 * 2 ^ 59
def prefixEnd_1301138 : Nat := 4983230072969 + 3 ^ 40 * 1301138 * 2
def baseEnd_1301138 : Nat := 296937418591038011240525

theorem tailTrace_1301138 : CollatzResearch.WordTrace tailWord_1301138 prefixEnd_1301138 296937418591038011240525 := by
  unfold tailWord_1301138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11864100390051679380984017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31637601040137811682624045 11864100390051679380984017)
  ·
    refine ⟨8898075292538759535738013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11864100390051679380984017 8898075292538759535738013)
    ·
      refine ⟨3336778234702034825901755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8898075292538759535738013 3336778234702034825901755)
      ·
        refine ⟨5005167352053052238852633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336778234702034825901755 5005167352053052238852633)
        ·
          refine ⟨3753875514039789179139475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005167352053052238852633 3753875514039789179139475)
          ·
            refine ⟨5630813271059683768709213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753875514039789179139475 5630813271059683768709213)
            ·
              refine ⟨2111554976647381413265955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5630813271059683768709213 2111554976647381413265955)
              ·
                refine ⟨3167332464971072119898933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111554976647381413265955 3167332464971072119898933)
                ·
                  refine ⟨296937418591038011240525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3167332464971072119898933 296937418591038011240525)
                  ·
                    rfl

theorem cell21_1301138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1301138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301138 prefixEnd_1301138 := by exact prefixLift 1301138
  have htrace : WordTrace (prefixWord ++ tailWord_1301138) baseStart_1301138 baseEnd_1301138 := by
    simpa [prefixWord, tailWord_1301138, baseEnd_1301138] using wordTrace_append hprefix tailTrace_1301138
  have hstable : (prefixWord ++ tailWord_1301138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301138).length < 2 ^ (prefixWord ++ tailWord_1301138).sum := by decide
  have hdescent : baseEnd_1301138 < baseStart_1301138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301225 : List Nat := [1, 2, 1, 1, 1, 2, 4, 9]
def baseStart_1301225 : Nat := 118140960795 + 1301225 * 2 ^ 59
def prefixEnd_1301225 : Nat := 4983230072969 + 3 ^ 40 * 1301225 * 2
def baseEnd_1301225 : Nat := 98985757725448397763449

theorem tailTrace_1301225 : CollatzResearch.WordTrace tailWord_1301225 prefixEnd_1301225 98985757725448397763449 := by
  unfold tailWord_1301225
  simp only [CollatzResearch.WordTrace]
  refine ⟨47459574710891531382353129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31639716473927687588235419 47459574710891531382353129)
  ·
    refine ⟨35594681033168648536764847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47459574710891531382353129 35594681033168648536764847)
    ·
      refine ⟨53392021549752972805147271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35594681033168648536764847 53392021549752972805147271)
      ·
        refine ⟨80088032324629459207720907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53392021549752972805147271 80088032324629459207720907)
        ·
          refine ⟨120132048486944188811581361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80088032324629459207720907 120132048486944188811581361)
          ·
            refine ⟨90099036365208141608686021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120132048486944188811581361 90099036365208141608686021)
            ·
              refine ⟨16893569318476526551628629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90099036365208141608686021 16893569318476526551628629)
              ·
                refine ⟨98985757725448397763449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16893569318476526551628629 98985757725448397763449)
                ·
                  rfl

theorem cell21_1301225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_1301225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301225 prefixEnd_1301225 := by exact prefixLift 1301225
  have htrace : WordTrace (prefixWord ++ tailWord_1301225) baseStart_1301225 baseEnd_1301225 := by
    simpa [prefixWord, tailWord_1301225, baseEnd_1301225] using wordTrace_append hprefix tailTrace_1301225
  have hstable : (prefixWord ++ tailWord_1301225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301225).length < 2 ^ (prefixWord ++ tailWord_1301225).sum := by decide
  have hdescent : baseEnd_1301225 < baseStart_1301225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301293 : List Nat := [1, 5, 3, 2, 2, 1, 7]
def baseStart_1301293 : Nat := 118140960795 + 1301293 * 2 ^ 59
def prefixEnd_1301293 : Nat := 4983230072969 + 3 ^ 40 * 1301293 * 2
def baseEnd_1301293 : Nat := 32996976855865798461875

theorem tailTrace_1301293 : CollatzResearch.WordTrace tailWord_1301293 prefixEnd_1301293 32996976855865798461875 := by
  unfold tailWord_1301293
  simp only [CollatzResearch.WordTrace]
  refine ⟨47462054874645178995828533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31641369916430119330552355 47462054874645178995828533)
  ·
    refine ⟨4449567644497985530858925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47462054874645178995828533 4449567644497985530858925)
    ·
      refine ⟨1668587866686744574072097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4449567644497985530858925 1668587866686744574072097)
      ·
        refine ⟨1251440900015058430554073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668587866686744574072097 1251440900015058430554073)
        ·
          refine ⟨938580675011293822915555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251440900015058430554073 938580675011293822915555)
          ·
            refine ⟨1407871012516940734373333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938580675011293822915555 1407871012516940734373333)
            ·
              refine ⟨32996976855865798461875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1407871012516940734373333 32996976855865798461875)
              ·
                rfl

theorem cell21_1301293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 7].length) (baseStart_1301293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301293 prefixEnd_1301293 := by exact prefixLift 1301293
  have htrace : WordTrace (prefixWord ++ tailWord_1301293) baseStart_1301293 baseEnd_1301293 := by
    simpa [prefixWord, tailWord_1301293, baseEnd_1301293] using wordTrace_append hprefix tailTrace_1301293
  have hstable : (prefixWord ++ tailWord_1301293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301293).length < 2 ^ (prefixWord ++ tailWord_1301293).sum := by decide
  have hdescent : baseEnd_1301293 < baseStart_1301293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301321 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 4]
def baseStart_1301321 : Nat := 118140960795 + 1301321 * 2 ^ 59
def prefixEnd_1301321 : Nat := 4983230072969 + 3 ^ 40 * 1301321 * 2
def baseEnd_1301321 : Nat := 296979181684270359690151

theorem tailTrace_1301321 : CollatzResearch.WordTrace tailWord_1301321 prefixEnd_1301321 296979181684270359690151 := by
  unfold tailWord_1301321
  simp only [CollatzResearch.WordTrace]
  refine ⟨47463076118543739777847817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31642050745695826518565211 47463076118543739777847817)
  ·
    refine ⟨35597307088907804833385863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47463076118543739777847817 35597307088907804833385863)
    ·
      refine ⟨53395960633361707250078795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35597307088907804833385863 53395960633361707250078795)
      ·
        refine ⟨80093940950042560875118193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53395960633361707250078795 80093940950042560875118193)
        ·
          refine ⟨60070455712531920656338645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80093940950042560875118193 60070455712531920656338645)
          ·
            refine ⟨1407901305762466890382937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60070455712531920656338645 1407901305762466890382937)
            ·
              refine ⟨1055925979321850167787203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407901305762466890382937 1055925979321850167787203)
              ·
                refine ⟨1583888968982775251680805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055925979321850167787203 1583888968982775251680805)
                ·
                  refine ⟨296979181684270359690151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583888968982775251680805 296979181684270359690151)
                  ·
                    rfl

theorem cell21_1301321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_1301321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301321 prefixEnd_1301321 := by exact prefixLift 1301321
  have htrace : WordTrace (prefixWord ++ tailWord_1301321) baseStart_1301321 baseEnd_1301321 := by
    simpa [prefixWord, tailWord_1301321, baseEnd_1301321] using wordTrace_append hprefix tailTrace_1301321
  have hstable : (prefixWord ++ tailWord_1301321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301321).length < 2 ^ (prefixWord ++ tailWord_1301321).sum := by decide
  have hdescent : baseEnd_1301321 < baseStart_1301321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301363 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_1301363 : Nat := 118140960795 + 1301363 * 2 ^ 59
def prefixEnd_1301363 : Nat := 4983230072969 + 3 ^ 40 * 1301363 * 2
def baseEnd_1301363 : Nat := 296988766656487619990065

theorem tailTrace_1301363 : CollatzResearch.WordTrace tailWord_1301363 prefixEnd_1301363 296988766656487619990065 := by
  unfold tailWord_1301363
  simp only [CollatzResearch.WordTrace]
  refine ⟨47464607984391580950876743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31643071989594387300584495 47464607984391580950876743)
  ·
    refine ⟨71196911976587371426315115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47464607984391580950876743 71196911976587371426315115)
    ·
      refine ⟨106795367964881057139472673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71196911976587371426315115 106795367964881057139472673)
      ·
        refine ⟨80096525973660792854604505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106795367964881057139472673 80096525973660792854604505)
        ·
          refine ⟨60072394480245594640953379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80096525973660792854604505 60072394480245594640953379)
          ·
            refine ⟨90108591720368391961430069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60072394480245594640953379 90108591720368391961430069)
            ·
              refine ⟨8447680473784536746384069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90108591720368391961430069 8447680473784536746384069)
              ·
                refine ⟨1583940088834600639947013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8447680473784536746384069 1583940088834600639947013)
                ·
                  refine ⟨296988766656487619990065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1583940088834600639947013 296988766656487619990065)
                  ·
                    rfl

theorem cell21_1301363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_1301363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301363 prefixEnd_1301363 := by exact prefixLift 1301363
  have htrace : WordTrace (prefixWord ++ tailWord_1301363) baseStart_1301363 baseEnd_1301363 := by
    simpa [prefixWord, tailWord_1301363, baseEnd_1301363] using wordTrace_append hprefix tailTrace_1301363
  have hstable : (prefixWord ++ tailWord_1301363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301363).length < 2 ^ (prefixWord ++ tailWord_1301363).sum := by decide
  have hdescent : baseEnd_1301363 < baseStart_1301363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301535 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 3]
def baseStart_1301535 : Nat := 118140960795 + 1301535 * 2 ^ 59
def prefixEnd_1301535 : Nat := 4983230072969 + 3 ^ 40 * 1301535 * 2
def baseEnd_1301535 : Nat := 297028019399853543123047

theorem tailTrace_1301535 : CollatzResearch.WordTrace tailWord_1301535 prefixEnd_1301535 297028019399853543123047 := by
  unfold tailWord_1301535
  simp only [CollatzResearch.WordTrace]
  refine ⟨47470881339768454326138059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31647254226512302884092039 47470881339768454326138059)
  ·
    refine ⟨71206322009652681489207089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47470881339768454326138059 71206322009652681489207089)
    ·
      refine ⟨53404741507239511116905317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71206322009652681489207089 53404741507239511116905317)
      ·
        refine ⟨10013389032607408334419747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53404741507239511116905317 10013389032607408334419747)
        ·
          refine ⟨15020083548911112501629621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013389032607408334419747 15020083548911112501629621)
          ·
            refine ⟨1408132832710416797027777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15020083548911112501629621 1408132832710416797027777)
            ·
              refine ⟨1056099624532812597770833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408132832710416797027777 1056099624532812597770833)
              ·
                refine ⟨792074718399609448328125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056099624532812597770833 792074718399609448328125)
                ·
                  refine ⟨297028019399853543123047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792074718399609448328125 297028019399853543123047)
                  ·
                    rfl

theorem cell21_1301535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3].length) (baseStart_1301535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301535 prefixEnd_1301535 := by exact prefixLift 1301535
  have htrace : WordTrace (prefixWord ++ tailWord_1301535) baseStart_1301535 baseEnd_1301535 := by
    simpa [prefixWord, tailWord_1301535, baseEnd_1301535] using wordTrace_append hprefix tailTrace_1301535
  have hstable : (prefixWord ++ tailWord_1301535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301535).length < 2 ^ (prefixWord ++ tailWord_1301535).sum := by decide
  have hdescent : baseEnd_1301535 < baseStart_1301535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301560 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_1301560 : Nat := 118140960795 + 1301560 * 2 ^ 59
def prefixEnd_1301560 : Nat := 4983230072969 + 3 ^ 40 * 1301560 * 2
def baseEnd_1301560 : Nat := 297033724740459055206329

theorem tailTrace_1301560 : CollatzResearch.WordTrace tailWord_1301560 prefixEnd_1301560 297033724740459055206329 := by
  unfold tailWord_1301560
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735896582338941797899067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31647862109785255730532089 23735896582338941797899067)
  ·
    refine ⟨35603844873508412696848601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23735896582338941797899067 35603844873508412696848601)
    ·
      refine ⟨26702883655131309522636451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35603844873508412696848601 26702883655131309522636451)
      ·
        refine ⟨40054325482696964283954677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702883655131309522636451 40054325482696964283954677)
        ·
          refine ⟨3755093014002840401620751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40054325482696964283954677 3755093014002840401620751)
          ·
            refine ⟨5632639521004260602431127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755093014002840401620751 5632639521004260602431127)
            ·
              refine ⟨8448959281506390903646691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632639521004260602431127 8448959281506390903646691)
              ·
                refine ⟨12673438922259586355470037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448959281506390903646691 12673438922259586355470037)
                ·
                  refine ⟨297033724740459055206329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12673438922259586355470037 297033724740459055206329)
                  ·
                    rfl

theorem cell21_1301560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_1301560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301560 prefixEnd_1301560 := by exact prefixLift 1301560
  have htrace : WordTrace (prefixWord ++ tailWord_1301560) baseStart_1301560 baseEnd_1301560 := by
    simpa [prefixWord, tailWord_1301560, baseEnd_1301560] using wordTrace_append hprefix tailTrace_1301560
  have hstable : (prefixWord ++ tailWord_1301560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301560).length < 2 ^ (prefixWord ++ tailWord_1301560).sum := by decide
  have hdescent : baseEnd_1301560 < baseStart_1301560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301605 : List Nat := [1, 3, 1, 3, 2, 1, 2, 8]
def baseStart_1301605 : Nat := 118140960795 + 1301605 * 2 ^ 59
def prefixEnd_1301605 : Nat := 4983230072969 + 3 ^ 40 * 1301605 * 2
def baseEnd_1301605 : Nat := 99014664784516325652079

theorem tailTrace_1301605 : CollatzResearch.WordTrace tailWord_1301605 prefixEnd_1301605 99014664784516325652079 := by
  unfold tailWord_1301605
  simp only [CollatzResearch.WordTrace]
  refine ⟨47473434449514856281186269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31648956299676570854124179 47473434449514856281186269)
  ·
    refine ⟨17802537918568071105444851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47473434449514856281186269 17802537918568071105444851)
    ·
      refine ⟨26703806877852106658167277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17802537918568071105444851 26703806877852106658167277)
      ·
        refine ⟨10013927579194539996812729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26703806877852106658167277 10013927579194539996812729)
        ·
          refine ⟨7510445684395904997609547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10013927579194539996812729 7510445684395904997609547)
          ·
            refine ⟨11265668526593857496414321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510445684395904997609547 11265668526593857496414321)
            ·
              refine ⟨8449251394945393122310741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11265668526593857496414321 8449251394945393122310741)
              ·
                refine ⟨99014664784516325652079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8449251394945393122310741 99014664784516325652079)
                ·
                  rfl

theorem cell21_1301605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_1301605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301605 prefixEnd_1301605 := by exact prefixLift 1301605
  have htrace : WordTrace (prefixWord ++ tailWord_1301605) baseStart_1301605 baseEnd_1301605 := by
    simpa [prefixWord, tailWord_1301605, baseEnd_1301605] using wordTrace_append hprefix tailTrace_1301605
  have hstable : (prefixWord ++ tailWord_1301605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301605).length < 2 ^ (prefixWord ++ tailWord_1301605).sum := by decide
  have hdescent : baseEnd_1301605 < baseStart_1301605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301622 : List Nat := [5, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1301622 : Nat := 118140960795 + 1301622 * 2 ^ 59
def prefixEnd_1301622 : Nat := 4983230072969 + 3 ^ 40 * 1301622 * 2
def baseEnd_1301622 : Nat := 99015957995053575057623

theorem tailTrace_1301622 : CollatzResearch.WordTrace tailWord_1301622 prefixEnd_1301622 99015957995053575057623 := by
  unfold tailWord_1301622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967128405653329261534695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31649369660302178789703413 2967128405653329261534695)
  ·
    refine ⟨4450692608479993892302043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2967128405653329261534695 4450692608479993892302043)
    ·
      refine ⟨6676038912719990838453065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4450692608479993892302043 6676038912719990838453065)
      ·
        refine ⟨5007029184539993128839799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6676038912719990838453065 5007029184539993128839799)
        ·
          refine ⟨7510543776809989693259699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007029184539993128839799 7510543776809989693259699)
          ·
            refine ⟨11265815665214984539889549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510543776809989693259699 11265815665214984539889549)
            ·
              refine ⟨4224680874455619202458581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11265815665214984539889549 4224680874455619202458581)
              ·
                refine ⟨99015957995053575057623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4224680874455619202458581 99015957995053575057623)
                ·
                  rfl

theorem cell21_1301622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1301622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301622 prefixEnd_1301622 := by exact prefixLift 1301622
  have htrace : WordTrace (prefixWord ++ tailWord_1301622) baseStart_1301622 baseEnd_1301622 := by
    simpa [prefixWord, tailWord_1301622, baseEnd_1301622] using wordTrace_append hprefix tailTrace_1301622
  have hstable : (prefixWord ++ tailWord_1301622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301622).length < 2 ^ (prefixWord ++ tailWord_1301622).sum := by decide
  have hdescent : baseEnd_1301622 < baseStart_1301622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301788 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1301788 : Nat := 118140960795 + 1301788 * 2 ^ 59
def prefixEnd_1301788 : Nat := 4983230072969 + 3 ^ 40 * 1301788 * 2
def baseEnd_1301788 : Nat := 297085757446781325405863

theorem tailTrace_1301788 : CollatzResearch.WordTrace tailWord_1301788 prefixEnd_1301788 297085757446781325405863 := by
  unfold tailWord_1301788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23740054503925939267549009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31653406005234585690065345 23740054503925939267549009)
  ·
    refine ⟨17805040877944454450661757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23740054503925939267549009 17805040877944454450661757)
    ·
      refine ⟨6676890329229170418998159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17805040877944454450661757 6676890329229170418998159)
      ·
        refine ⟨10015335493843755628497239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676890329229170418998159 10015335493843755628497239)
        ·
          refine ⟨15023003240765633442745859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10015335493843755628497239 15023003240765633442745859)
          ·
            refine ⟨22534504861148450164118789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15023003240765633442745859 22534504861148450164118789)
            ·
              refine ⟨4225219661465334405772273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22534504861148450164118789 4225219661465334405772273)
              ·
                refine ⟨3168914746099000804329205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4225219661465334405772273 3168914746099000804329205)
                ·
                  refine ⟨297085757446781325405863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3168914746099000804329205 297085757446781325405863)
                  ·
                    rfl

theorem cell21_1301788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1301788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301788 prefixEnd_1301788 := by exact prefixLift 1301788
  have htrace : WordTrace (prefixWord ++ tailWord_1301788) baseStart_1301788 baseEnd_1301788 := by
    simpa [prefixWord, tailWord_1301788, baseEnd_1301788] using wordTrace_append hprefix tailTrace_1301788
  have hstable : (prefixWord ++ tailWord_1301788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301788).length < 2 ^ (prefixWord ++ tailWord_1301788).sum := by decide
  have hdescent : baseEnd_1301788 < baseStart_1301788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301791 : List Nat := [1, 1, 2, 4, 4, 2, 2, 5]
def baseStart_1301791 : Nat := 118140960795 + 1301791 * 2 ^ 59
def prefixEnd_1301791 : Nat := 4983230072969 + 3 ^ 40 * 1301791 * 2
def baseEnd_1301791 : Nat := 99028814029217995618619

theorem tailTrace_1301791 : CollatzResearch.WordTrace tailWord_1301791 prefixEnd_1301791 99028814029217995618619 := by
  unfold tailWord_1301791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47480218426841010047457227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31653478951227340031638151 47480218426841010047457227)
  ·
    refine ⟨71220327640261515071185841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47480218426841010047457227 71220327640261515071185841)
    ·
      refine ⟨53415245730196136303389381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71220327640261515071185841 53415245730196136303389381)
      ·
        refine ⟨10015358574411775556885509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53415245730196136303389381 10015358574411775556885509)
        ·
          refine ⟨1877879732702207916916033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10015358574411775556885509 1877879732702207916916033)
          ·
            refine ⟨1408409799526655937687025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1877879732702207916916033 1408409799526655937687025)
            ·
              refine ⟨1056307349644991953265269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408409799526655937687025 1056307349644991953265269)
              ·
                refine ⟨99028814029217995618619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1056307349644991953265269 99028814029217995618619)
                ·
                  rfl

theorem cell21_1301791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 5].length) (baseStart_1301791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301791 prefixEnd_1301791 := by exact prefixLift 1301791
  have htrace : WordTrace (prefixWord ++ tailWord_1301791) baseStart_1301791 baseEnd_1301791 := by
    simpa [prefixWord, tailWord_1301791, baseEnd_1301791] using wordTrace_append hprefix tailTrace_1301791
  have hstable : (prefixWord ++ tailWord_1301791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301791).length < 2 ^ (prefixWord ++ tailWord_1301791).sum := by decide
  have hdescent : baseEnd_1301791 < baseStart_1301791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301836 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1301836 : Nat := 118140960795 + 1301836 * 2 ^ 59
def prefixEnd_1301836 : Nat := 4983230072969 + 3 ^ 40 * 1301836 * 2
def baseEnd_1301836 : Nat := 297096711700743908605765

theorem tailTrace_1301836 : CollatzResearch.WordTrace tailWord_1301836 prefixEnd_1301836 297096711700743908605765 := by
  unfold tailWord_1301836
  simp only [CollatzResearch.WordTrace]
  refine ⟨23740929855838991366422681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31654573141118655155230241 23740929855838991366422681)
  ·
    refine ⟨17805697391879243524817011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23740929855838991366422681 17805697391879243524817011)
    ·
      refine ⟨26708546087818865287225517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17805697391879243524817011 26708546087818865287225517)
      ·
        refine ⟨10015704782932074482709569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26708546087818865287225517 10015704782932074482709569)
        ·
          refine ⟨7511778587199055862032177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10015704782932074482709569 7511778587199055862032177)
          ·
            refine ⟨5633833940399291896524133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7511778587199055862032177 5633833940399291896524133)
            ·
              refine ⟨1056343863824867230598275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5633833940399291896524133 1056343863824867230598275)
              ·
                refine ⟨1584515795737300845897413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056343863824867230598275 1584515795737300845897413)
                ·
                  refine ⟨297096711700743908605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584515795737300845897413 297096711700743908605765)
                  ·
                    rfl

theorem cell21_1301836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1301836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301836 prefixEnd_1301836 := by exact prefixLift 1301836
  have htrace : WordTrace (prefixWord ++ tailWord_1301836) baseStart_1301836 baseEnd_1301836 := by
    simpa [prefixWord, tailWord_1301836, baseEnd_1301836] using wordTrace_append hprefix tailTrace_1301836
  have hstable : (prefixWord ++ tailWord_1301836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301836).length < 2 ^ (prefixWord ++ tailWord_1301836).sum := by decide
  have hdescent : baseEnd_1301836 < baseStart_1301836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301895 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_1301895 : Nat := 118140960795 + 1301895 * 2 ^ 59
def prefixEnd_1301895 : Nat := 4983230072969 + 3 ^ 40 * 1301895 * 2
def baseEnd_1301895 : Nat := 297110176304572917122311

theorem tailTrace_1301895 : CollatzResearch.WordTrace tailWord_1301895 prefixEnd_1301895 297110176304572917122311 := by
  unfold tailWord_1301895
  simp only [CollatzResearch.WordTrace]
  refine ⟨47484011618464235809243139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31656007745642823872828759 47484011618464235809243139)
  ·
    refine ⟨71226017427696353713864709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47484011618464235809243139 71226017427696353713864709)
    ·
      refine ⟨13354878267693066321349633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71226017427696353713864709 13354878267693066321349633)
      ·
        refine ⟨10016158700769799741012225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13354878267693066321349633 10016158700769799741012225)
        ·
          refine ⟨7512119025577349805759169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10016158700769799741012225 7512119025577349805759169)
          ·
            refine ⟨5634089269183012354319377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512119025577349805759169 5634089269183012354319377)
            ·
              refine ⟨4225566951887259265739533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634089269183012354319377 4225566951887259265739533)
              ·
                refine ⟨1584587606957722224652325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4225566951887259265739533 1584587606957722224652325)
                ·
                  refine ⟨297110176304572917122311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584587606957722224652325 297110176304572917122311)
                  ·
                    rfl

theorem cell21_1301895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_1301895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301895 prefixEnd_1301895 := by exact prefixLift 1301895
  have htrace : WordTrace (prefixWord ++ tailWord_1301895) baseStart_1301895 baseEnd_1301895 := by
    simpa [prefixWord, tailWord_1301895, baseEnd_1301895] using wordTrace_append hprefix tailTrace_1301895
  have hstable : (prefixWord ++ tailWord_1301895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301895).length < 2 ^ (prefixWord ++ tailWord_1301895).sum := by decide
  have hdescent : baseEnd_1301895 < baseStart_1301895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301923 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_1301923 : Nat := 118140960795 + 1301923 * 2 ^ 59
def prefixEnd_1301923 : Nat := 4983230072969 + 3 ^ 40 * 1301923 * 2
def baseEnd_1301923 : Nat := 297116566286051090655587

theorem tailTrace_1301923 : CollatzResearch.WordTrace tailWord_1301923 prefixEnd_1301923 297116566286051090655587 := by
  unfold tailWord_1301923
  simp only [CollatzResearch.WordTrace]
  refine ⟨47485032862362796591262423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31656688574908531060841615 47485032862362796591262423)
  ·
    refine ⟨71227549293544194886893635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47485032862362796591262423 71227549293544194886893635)
    ·
      refine ⟨106841323940316292330340453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71227549293544194886893635 106841323940316292330340453)
      ·
        refine ⟨20032748238809304811938835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106841323940316292330340453 20032748238809304811938835)
        ·
          refine ⟨30049122358213957217908253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20032748238809304811938835 30049122358213957217908253)
          ·
            refine ⟨11268420884330233956715595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30049122358213957217908253 11268420884330233956715595)
            ·
              refine ⟨16902631326495350935073393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11268420884330233956715595 16902631326495350935073393)
              ·
                refine ⟨12676973494871513201305045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16902631326495350935073393 12676973494871513201305045)
                ·
                  refine ⟨297116566286051090655587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12676973494871513201305045 297116566286051090655587)
                  ·
                    rfl

theorem cell21_1301923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_1301923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301923 prefixEnd_1301923 := by exact prefixLift 1301923
  have htrace : WordTrace (prefixWord ++ tailWord_1301923) baseStart_1301923 baseEnd_1301923 := by
    simpa [prefixWord, tailWord_1301923, baseEnd_1301923] using wordTrace_append hprefix tailTrace_1301923
  have hstable : (prefixWord ++ tailWord_1301923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301923).length < 2 ^ (prefixWord ++ tailWord_1301923).sum := by decide
  have hdescent : baseEnd_1301923 < baseStart_1301923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301968 : List Nat := [2, 1, 1, 1, 1, 2, 2, 11]
def baseStart_1301968 : Nat := 118140960795 + 1301968 * 2 ^ 59
def prefixEnd_1301968 : Nat := 4983230072969 + 3 ^ 40 * 1301968 * 2
def baseEnd_1301968 : Nat := 99042278633047004135165

theorem tailTrace_1301968 : CollatzResearch.WordTrace tailWord_1301968 prefixEnd_1301968 99042278633047004135165 := by
  unfold tailWord_1301968
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743337073599884638325279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31657782764799846184433705 23743337073599884638325279)
  ·
    refine ⟨35615005610399826957487919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743337073599884638325279 35615005610399826957487919)
    ·
      refine ⟨53422508415599740436231879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35615005610399826957487919 53422508415599740436231879)
      ·
        refine ⟨80133762623399610654347819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53422508415599740436231879 80133762623399610654347819)
        ·
          refine ⟨120200643935099415981521729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80133762623399610654347819 120200643935099415981521729)
          ·
            refine ⟨90150482951324561986141297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120200643935099415981521729 90150482951324561986141297)
            ·
              refine ⟨67612862213493421489605973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90150482951324561986141297 67612862213493421489605973)
              ·
                refine ⟨99042278633047004135165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67612862213493421489605973 99042278633047004135165)
                ·
                  rfl

theorem cell21_1301968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_1301968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301968 prefixEnd_1301968 := by exact prefixLift 1301968
  have htrace : WordTrace (prefixWord ++ tailWord_1301968) baseStart_1301968 baseEnd_1301968 := by
    simpa [prefixWord, tailWord_1301968, baseEnd_1301968] using wordTrace_append hprefix tailTrace_1301968
  have hstable : (prefixWord ++ tailWord_1301968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301968).length < 2 ^ (prefixWord ++ tailWord_1301968).sum := by decide
  have hdescent : baseEnd_1301968 < baseStart_1301968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301985 : List Nat := [1, 2, 3, 1, 2, 5, 7]
def baseStart_1301985 : Nat := 118140960795 + 1301985 * 2 ^ 59
def prefixEnd_1301985 : Nat := 4983230072969 + 3 ^ 40 * 1301985 * 2
def baseEnd_1301985 : Nat := 33014523947861417846903

theorem tailTrace_1301985 : CollatzResearch.WordTrace tailWord_1301985 prefixEnd_1301985 33014523947861417846903 := by
  unfold tailWord_1301985
  simp only [CollatzResearch.WordTrace]
  refine ⟨47487294188138181180019409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31658196125425454120012939 47487294188138181180019409)
  ·
    refine ⟨35615470641103635885014557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47487294188138181180019409 35615470641103635885014557)
    ·
      refine ⟨13355801490413863456880459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35615470641103635885014557 13355801490413863456880459)
      ·
        refine ⟨20033702235620795185320689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355801490413863456880459 20033702235620795185320689)
        ·
          refine ⟨15025276676715596388990517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20033702235620795185320689 15025276676715596388990517)
          ·
            refine ⟨1408619688442087161467861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15025276676715596388990517 1408619688442087161467861)
            ·
              refine ⟨33014523947861417846903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1408619688442087161467861 33014523947861417846903)
              ·
                rfl

theorem cell21_1301985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 7].length) (baseStart_1301985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1301985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1301985 prefixEnd_1301985 := by exact prefixLift 1301985
  have htrace : WordTrace (prefixWord ++ tailWord_1301985) baseStart_1301985 baseEnd_1301985 := by
    simpa [prefixWord, tailWord_1301985, baseEnd_1301985] using wordTrace_append hprefix tailTrace_1301985
  have hstable : (prefixWord ++ tailWord_1301985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301985).length < 2 ^ (prefixWord ++ tailWord_1301985).sum := by decide
  have hdescent : baseEnd_1301985 < baseStart_1301985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302002 : List Nat := [3, 2, 1, 4, 1, 2, 2, 6]
def baseStart_1302002 : Nat := 118140960795 + 1302002 * 2 ^ 59
def prefixEnd_1302002 : Nat := 4983230072969 + 3 ^ 40 * 1302002 * 2
def baseEnd_1302002 : Nat := 99044865054121502946253

theorem tailTrace_1302002 : CollatzResearch.WordTrace tailWord_1302002 prefixEnd_1302002 99044865054121502946253 := by
  unfold tailWord_1302002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871978557269148270847065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31658609486051062055592173 11871978557269148270847065)
  ·
    refine ⟨8903983917951861203135299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11871978557269148270847065 8903983917951861203135299)
    ·
      refine ⟨13355975876927791804702949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8903983917951861203135299 13355975876927791804702949)
      ·
        refine ⟨2504245476923960963381803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13355975876927791804702949 2504245476923960963381803)
        ·
          refine ⟨3756368215385941445072705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504245476923960963381803 3756368215385941445072705)
          ·
            refine ⟨2817276161539456083804529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3756368215385941445072705 2817276161539456083804529)
            ·
              refine ⟨2112957121154592062853397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2817276161539456083804529 2112957121154592062853397)
              ·
                refine ⟨99044865054121502946253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2112957121154592062853397 99044865054121502946253)
                ·
                  rfl

theorem cell21_1302002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_1302002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302002 prefixEnd_1302002 := by exact prefixLift 1302002
  have htrace : WordTrace (prefixWord ++ tailWord_1302002) baseStart_1302002 baseEnd_1302002 := by
    simpa [prefixWord, tailWord_1302002, baseEnd_1302002] using wordTrace_append hprefix tailTrace_1302002
  have hstable : (prefixWord ++ tailWord_1302002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302002).length < 2 ^ (prefixWord ++ tailWord_1302002).sum := by decide
  have hdescent : baseEnd_1302002 < baseStart_1302002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302005 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 4]
def baseStart_1302005 : Nat := 118140960795 + 1302005 * 2 ^ 59
def prefixEnd_1302005 : Nat := 4983230072969 + 3 ^ 40 * 1302005 * 2
def baseEnd_1302005 : Nat := 297135279803237170288753

theorem tailTrace_1302005 : CollatzResearch.WordTrace tailWord_1302005 prefixEnd_1302005 297135279803237170288753 := by
  unfold tailWord_1302005
  simp only [CollatzResearch.WordTrace]
  refine ⟨47488023648065724595747469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31658682432043816397164979 47488023648065724595747469)
  ·
    refine ⟨17808008868024646723405301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47488023648065724595747469 17808008868024646723405301)
    ·
      refine ⟨1669500831377310630319247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17808008868024646723405301 1669500831377310630319247)
      ·
        refine ⟨2504251247065965945478871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669500831377310630319247 2504251247065965945478871)
        ·
          refine ⟨3756376870598948918218307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504251247065965945478871 3756376870598948918218307)
          ·
            refine ⟨5634565305898423377327461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756376870598948918218307 5634565305898423377327461)
            ·
              refine ⟨1056480994855954383248899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5634565305898423377327461 1056480994855954383248899)
              ·
                refine ⟨1584721492283931574873349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056480994855954383248899 1584721492283931574873349)
                ·
                  refine ⟨297135279803237170288753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1584721492283931574873349 297135279803237170288753)
                  ·
                    rfl

theorem cell21_1302005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_1302005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302005 prefixEnd_1302005 := by exact prefixLift 1302005
  have htrace : WordTrace (prefixWord ++ tailWord_1302005) baseStart_1302005 baseEnd_1302005 := by
    simpa [prefixWord, tailWord_1302005, baseEnd_1302005] using wordTrace_append hprefix tailTrace_1302005
  have hstable : (prefixWord ++ tailWord_1302005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302005).length < 2 ^ (prefixWord ++ tailWord_1302005).sum := by decide
  have hdescent : baseEnd_1302005 < baseStart_1302005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302050 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1302050 : Nat := 118140960795 + 1302050 * 2 ^ 59
def prefixEnd_1302050 : Nat := 4983230072969 + 3 ^ 40 * 1302050 * 2
def baseEnd_1302050 : Nat := 297145549416327092038661

theorem tailTrace_1302050 : CollatzResearch.WordTrace tailWord_1302050 prefixEnd_1302050 297145549416327092038661 := by
  unfold tailWord_1302050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872416233225674320283901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31659776621935131520757069 11872416233225674320283901)
  ·
    refine ⟨4452156087459627870106463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11872416233225674320283901 4452156087459627870106463)
    ·
      refine ⟨6678234131189441805159695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4452156087459627870106463 6678234131189441805159695)
      ·
        refine ⟨10017351196784162707739543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678234131189441805159695 10017351196784162707739543)
        ·
          refine ⟨15026026795176244061609315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10017351196784162707739543 15026026795176244061609315)
          ·
            refine ⟨22539040192764366092413973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15026026795176244061609315 22539040192764366092413973)
            ·
              refine ⟨1056517509035829660581905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22539040192764366092413973 1056517509035829660581905)
              ·
                refine ⟨792388131776872245436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056517509035829660581905 792388131776872245436429)
                ·
                  refine ⟨297145549416327092038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792388131776872245436429 297145549416327092038661)
                  ·
                    rfl

theorem cell21_1302050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1302050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302050 prefixEnd_1302050 := by exact prefixLift 1302050
  have htrace : WordTrace (prefixWord ++ tailWord_1302050) baseStart_1302050 baseEnd_1302050 := by
    simpa [prefixWord, tailWord_1302050, baseEnd_1302050] using wordTrace_append hprefix tailTrace_1302050
  have hstable : (prefixWord ++ tailWord_1302050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302050).length < 2 ^ (prefixWord ++ tailWord_1302050).sum := by decide
  have hdescent : baseEnd_1302050 < baseStart_1302050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302168 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_1302168 : Nat := 118140960795 + 1302168 * 2 ^ 59
def prefixEnd_1302168 : Nat := 4983230072969 + 3 ^ 40 * 1302168 * 2
def baseEnd_1302168 : Nat := 297172478623985109071753

theorem tailTrace_1302168 : CollatzResearch.WordTrace tailWord_1302168 prefixEnd_1302168 297172478623985109071753 := by
  unfold tailWord_1302168
  simp only [CollatzResearch.WordTrace]
  refine ⟨23746984373237601716965579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31662645830983468955954105 23746984373237601716965579)
  ·
    refine ⟨35620476559856402575448369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23746984373237601716965579 35620476559856402575448369)
    ·
      refine ⟨26715357419892301931586277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35620476559856402575448369 26715357419892301931586277)
      ·
        refine ⟨5009129516229806612172427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26715357419892301931586277 5009129516229806612172427)
        ·
          refine ⟨7513694274344709918258641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009129516229806612172427 7513694274344709918258641)
          ·
            refine ⟨5635270705758532438693981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7513694274344709918258641 5635270705758532438693981)
            ·
              refine ⟨2113226514659449664510243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5635270705758532438693981 2113226514659449664510243)
              ·
                refine ⟨3169839771989174496765365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113226514659449664510243 3169839771989174496765365)
                ·
                  refine ⟨297172478623985109071753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3169839771989174496765365 297172478623985109071753)
                  ·
                    rfl

theorem cell21_1302168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_1302168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302168 prefixEnd_1302168 := by exact prefixLift 1302168
  have htrace : WordTrace (prefixWord ++ tailWord_1302168) baseStart_1302168 baseEnd_1302168 := by
    simpa [prefixWord, tailWord_1302168, baseEnd_1302168] using wordTrace_append hprefix tailTrace_1302168
  have hstable : (prefixWord ++ tailWord_1302168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302168).length < 2 ^ (prefixWord ++ tailWord_1302168).sum := by decide
  have hdescent : baseEnd_1302168 < baseStart_1302168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302247 : List Nat := [1, 1, 5, 4, 1, 1, 3, 5]
def baseStart_1302247 : Nat := 118140960795 + 1302247 * 2 ^ 59
def prefixEnd_1302247 : Nat := 4983230072969 + 3 ^ 40 * 1302247 * 2
def baseEnd_1302247 : Nat := 99063502500099509084975

theorem tailTrace_1302247 : CollatzResearch.WordTrace tailWord_1302247 prefixEnd_1302247 99063502500099509084975 := by
  unfold tailWord_1302247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47496850113188999926056995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31664566742125999950704663 47496850113188999926056995)
  ·
    refine ⟨71245275169783499889085493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47496850113188999926056995 71245275169783499889085493)
    ·
      refine ⟨6679244547167203114601765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71245275169783499889085493 6679244547167203114601765)
      ·
        refine ⟨1252358352593850583987831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6679244547167203114601765 1252358352593850583987831)
        ·
          refine ⟨1878537528890775875981747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252358352593850583987831 1878537528890775875981747)
          ·
            refine ⟨2817806293336163813972621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878537528890775875981747 2817806293336163813972621)
            ·
              refine ⟨1056677360001061430239733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2817806293336163813972621 1056677360001061430239733)
              ·
                refine ⟨99063502500099509084975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1056677360001061430239733 99063502500099509084975)
                ·
                  rfl

theorem cell21_1302247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 5].length) (baseStart_1302247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302247 prefixEnd_1302247 := by exact prefixLift 1302247
  have htrace : WordTrace (prefixWord ++ tailWord_1302247) baseStart_1302247 baseEnd_1302247 := by
    simpa [prefixWord, tailWord_1302247, baseEnd_1302247] using wordTrace_append hprefix tailTrace_1302247
  have hstable : (prefixWord ++ tailWord_1302247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302247).length < 2 ^ (prefixWord ++ tailWord_1302247).sum := by decide
  have hdescent : baseEnd_1302247 < baseStart_1302247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302258 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1302258 : Nat := 118140960795 + 1302258 * 2 ^ 59
def prefixEnd_1302258 : Nat := 4983230072969 + 3 ^ 40 * 1302258 * 2
def baseEnd_1302258 : Nat := 297193017850164952571569

theorem tailTrace_1302258 : CollatzResearch.WordTrace tailWord_1302258 prefixEnd_1302258 297193017850164952571569 := by
  unfold tailWord_1302258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874312829037287201176857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31664834210766099203138285 11874312829037287201176857)
  ·
    refine ⟨8905734621777965400882643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11874312829037287201176857 8905734621777965400882643)
    ·
      refine ⟨13358601932666948101323965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8905734621777965400882643 13358601932666948101323965)
      ·
        refine ⟨5009475724750105537996487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13358601932666948101323965 5009475724750105537996487)
        ·
          refine ⟨7514213587125158306994731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009475724750105537996487 7514213587125158306994731)
          ·
            refine ⟨11271320380687737460492097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514213587125158306994731 11271320380687737460492097)
            ·
              refine ⟨8453490285515803095369073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11271320380687737460492097 8453490285515803095369073)
              ·
                refine ⟨6340117714136852321526805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8453490285515803095369073 6340117714136852321526805)
                ·
                  refine ⟨297193017850164952571569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6340117714136852321526805 297193017850164952571569)
                  ·
                    rfl

theorem cell21_1302258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1302258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302258 prefixEnd_1302258 := by exact prefixLift 1302258
  have htrace : WordTrace (prefixWord ++ tailWord_1302258) baseStart_1302258 baseEnd_1302258 := by
    simpa [prefixWord, tailWord_1302258, baseEnd_1302258] using wordTrace_append hprefix tailTrace_1302258
  have hstable : (prefixWord ++ tailWord_1302258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302258).length < 2 ^ (prefixWord ++ tailWord_1302258).sum := by decide
  have hdescent : baseEnd_1302258 < baseStart_1302258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302303 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_1302303 : Nat := 118140960795 + 1302303 * 2 ^ 59
def prefixEnd_1302303 : Nat := 4983230072969 + 3 ^ 40 * 1302303 * 2
def baseEnd_1302303 : Nat := 297203287463254874321477

theorem tailTrace_1302303 : CollatzResearch.WordTrace tailWord_1302303 prefixEnd_1302303 297203287463254874321477 := by
  unfold tailWord_1302303
  simp only [CollatzResearch.WordTrace]
  refine ⟨47498892600986121490095563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31665928400657414326730375 47498892600986121490095563)
  ·
    refine ⟨71248338901479182235143345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47498892600986121490095563 71248338901479182235143345)
    ·
      refine ⟨53436254176109386676357509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71248338901479182235143345 53436254176109386676357509)
      ·
        refine ⟨10019297658020510001817033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53436254176109386676357509 10019297658020510001817033)
        ·
          refine ⟨7514473243515382501362775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10019297658020510001817033 7514473243515382501362775)
          ·
            refine ⟨11271709865273073752044163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514473243515382501362775 11271709865273073752044163)
            ·
              refine ⟨16907564797909610628066245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11271709865273073752044163 16907564797909610628066245)
              ·
                refine ⟨3170168399608051992762421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16907564797909610628066245 3170168399608051992762421)
                ·
                  refine ⟨297203287463254874321477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170168399608051992762421 297203287463254874321477)
                  ·
                    rfl

theorem cell21_1302303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_1302303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302303 prefixEnd_1302303 := by exact prefixLift 1302303
  have htrace : WordTrace (prefixWord ++ tailWord_1302303) baseStart_1302303 baseEnd_1302303 := by
    simpa [prefixWord, tailWord_1302303, baseEnd_1302303] using wordTrace_append hprefix tailTrace_1302303
  have hstable : (prefixWord ++ tailWord_1302303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302303).length < 2 ^ (prefixWord ++ tailWord_1302303).sum := by decide
  have hdescent : baseEnd_1302303 < baseStart_1302303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302492 : List Nat := [2, 2, 6, 1, 2, 1, 7]
def baseStart_1302492 : Nat := 118140960795 + 1302492 * 2 ^ 59
def prefixEnd_1302492 : Nat := 4983230072969 + 3 ^ 40 * 1302492 * 2
def baseEnd_1302492 : Nat := 33027379982025838407899

theorem tailTrace_1302492 : CollatzResearch.WordTrace tailWord_1302492 prefixEnd_1302492 33027379982025838407899 := by
  unfold tailWord_1302492
  simp only [CollatzResearch.WordTrace]
  refine ⟨23752892998650703384362865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31670523998200937845817153 23752892998650703384362865)
  ·
    refine ⟨17814669748988027538272149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23752892998650703384362865 17814669748988027538272149)
    ·
      refine ⟨835062644483813790856507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17814669748988027538272149 835062644483813790856507)
      ·
        refine ⟨1252593966725720686284761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835062644483813790856507 1252593966725720686284761)
        ·
          refine ⟨939445475044290514713571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252593966725720686284761 939445475044290514713571)
          ·
            refine ⟨1409168212566435772070357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939445475044290514713571 1409168212566435772070357)
            ·
              refine ⟨33027379982025838407899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1409168212566435772070357 33027379982025838407899)
              ·
                rfl

theorem cell21_1302492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 7].length) (baseStart_1302492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302492 prefixEnd_1302492 := by exact prefixLift 1302492
  have htrace : WordTrace (prefixWord ++ tailWord_1302492) baseStart_1302492 baseEnd_1302492 := by
    simpa [prefixWord, tailWord_1302492, baseEnd_1302492] using wordTrace_append hprefix tailTrace_1302492
  have hstable : (prefixWord ++ tailWord_1302492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302492).length < 2 ^ (prefixWord ++ tailWord_1302492).sum := by decide
  have hdescent : baseEnd_1302492 < baseStart_1302492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302565 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1302565 : Nat := 118140960795 + 1302565 * 2 ^ 59
def prefixEnd_1302565 : Nat := 4983230072969 + 3 ^ 40 * 1302565 * 2
def baseEnd_1302565 : Nat := 297263079432800640954275

theorem tailTrace_1302565 : CollatzResearch.WordTrace tailWord_1302565 prefixEnd_1302565 297263079432800640954275 := by
  unfold tailWord_1302565
  simp only [CollatzResearch.WordTrace]
  refine ⟨47508448526036940236133149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31672299017357960157422099 47508448526036940236133149)
  ·
    refine ⟨17815668197263852588549931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47508448526036940236133149 17815668197263852588549931)
    ·
      refine ⟨26723502295895778882824897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17815668197263852588549931 26723502295895778882824897)
      ·
        refine ⟨20042626721921834162118673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26723502295895778882824897 20042626721921834162118673)
        ·
          refine ⟨15031970041441375621589005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20042626721921834162118673 15031970041441375621589005)
          ·
            refine ⟨5636988765540515858095877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15031970041441375621589005 5636988765540515858095877)
            ·
              refine ⟨1056935393538846723392977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5636988765540515858095877 1056935393538846723392977)
              ·
                refine ⟨792701545154135042544733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056935393538846723392977 792701545154135042544733)
                ·
                  refine ⟨297263079432800640954275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792701545154135042544733 297263079432800640954275)
                  ·
                    rfl

theorem cell21_1302565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1302565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302565 prefixEnd_1302565 := by exact prefixLift 1302565
  have htrace : WordTrace (prefixWord ++ tailWord_1302565) baseStart_1302565 baseEnd_1302565 := by
    simpa [prefixWord, tailWord_1302565, baseEnd_1302565] using wordTrace_append hprefix tailTrace_1302565
  have hstable : (prefixWord ++ tailWord_1302565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302565).length < 2 ^ (prefixWord ++ tailWord_1302565).sum := by decide
  have hdescent : baseEnd_1302565 < baseStart_1302565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302576 : List Nat := [2, 1, 1, 1, 2, 5, 3, 6]
def baseStart_1302576 : Nat := 118140960795 + 1302576 * 2 ^ 59
def prefixEnd_1302576 : Nat := 4983230072969 + 3 ^ 40 * 1302576 * 2
def baseEnd_1302576 : Nat := 99088529927555688756973

theorem tailTrace_1302576 : CollatzResearch.WordTrace tailWord_1302576 prefixEnd_1302576 99088529927555688756973 := by
  unfold tailWord_1302576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23754424864498544557391791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31672566485998059409855721 23754424864498544557391791)
  ·
    refine ⟨35631637296747816836087687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23754424864498544557391791 35631637296747816836087687)
    ·
      refine ⟨53447455945121725254131531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35631637296747816836087687 53447455945121725254131531)
      ·
        refine ⟨80171183917682587881197297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53447455945121725254131531 80171183917682587881197297)
        ·
          refine ⟨60128387938261940910897973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80171183917682587881197297 60128387938261940910897973)
          ·
            refine ⟨5637036369212056960396685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60128387938261940910897973 5637036369212056960396685)
            ·
              refine ⟨2113888638454521360148757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5637036369212056960396685 2113888638454521360148757)
              ·
                refine ⟨99088529927555688756973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2113888638454521360148757 99088529927555688756973)
                ·
                  rfl

theorem cell21_1302576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_1302576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302576 prefixEnd_1302576 := by exact prefixLift 1302576
  have htrace : WordTrace (prefixWord ++ tailWord_1302576) baseStart_1302576 baseEnd_1302576 := by
    simpa [prefixWord, tailWord_1302576, baseEnd_1302576] using wordTrace_append hprefix tailTrace_1302576
  have hstable : (prefixWord ++ tailWord_1302576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302576).length < 2 ^ (prefixWord ++ tailWord_1302576).sum := by decide
  have hdescent : baseEnd_1302576 < baseStart_1302576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302624 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_1302624 : Nat := 118140960795 + 1302624 * 2 ^ 59
def prefixEnd_1302624 : Nat := 4983230072969 + 3 ^ 40 * 1302624 * 2
def baseEnd_1302624 : Nat := 297276544036629649470821

theorem tailTrace_1302624 : CollatzResearch.WordTrace tailWord_1302624 prefixEnd_1302624 297276544036629649470821 := by
  unfold tailWord_1302624
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755300216411596656265463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31673733621882128875020617 23755300216411596656265463)
  ·
    refine ⟨35632950324617394984398195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23755300216411596656265463 35632950324617394984398195)
    ·
      refine ⟨53449425486926092476597293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35632950324617394984398195 53449425486926092476597293)
      ·
        refine ⟨20043534557597284678723985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53449425486926092476597293 20043534557597284678723985)
        ·
          refine ⟨15032650918197963509042989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20043534557597284678723985 15032650918197963509042989)
          ·
            refine ⟨5637244094324236315891121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15032650918197963509042989 5637244094324236315891121)
            ·
              refine ⟨4227933070743177236918341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637244094324236315891121 4227933070743177236918341)
              ·
                refine ⟨792737450764345731922189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4227933070743177236918341 792737450764345731922189)
                ·
                  refine ⟨297276544036629649470821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792737450764345731922189 297276544036629649470821)
                  ·
                    rfl

theorem cell21_1302624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_1302624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302624 prefixEnd_1302624 := by exact prefixLift 1302624
  have htrace : WordTrace (prefixWord ++ tailWord_1302624) baseStart_1302624 baseEnd_1302624 := by
    simpa [prefixWord, tailWord_1302624, baseEnd_1302624] using wordTrace_append hprefix tailTrace_1302624
  have hstable : (prefixWord ++ tailWord_1302624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302624).length < 2 ^ (prefixWord ++ tailWord_1302624).sum := by decide
  have hdescent : baseEnd_1302624 < baseStart_1302624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302652 : List Nat := [2, 2, 2, 1, 1, 5, 1, 7]
def baseStart_1302652 : Nat := 118140960795 + 1302652 * 2 ^ 59
def prefixEnd_1302652 : Nat := 4983230072969 + 3 ^ 40 * 1302652 * 2
def baseEnd_1302652 : Nat := 99094311339369274334699

theorem tailTrace_1302652 : CollatzResearch.WordTrace tailWord_1302652 prefixEnd_1302652 99094311339369274334699 := by
  unfold tailWord_1302652
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755810838360877047275105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31674414451147836063033473 23755810838360877047275105)
  ·
    refine ⟨17816858128770657785456329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23755810838360877047275105 17816858128770657785456329)
    ·
      refine ⟨13362643596577993339092247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17816858128770657785456329 13362643596577993339092247)
      ·
        refine ⟨20043965394866990008638371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13362643596577993339092247 20043965394866990008638371)
        ·
          refine ⟨30065948092300485012957557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20043965394866990008638371 30065948092300485012957557)
          ·
            refine ⟨2818682633653170469964771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30065948092300485012957557 2818682633653170469964771)
            ·
              refine ⟨4228023950479755704947157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818682633653170469964771 4228023950479755704947157)
              ·
                refine ⟨99094311339369274334699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4228023950479755704947157 99094311339369274334699)
                ·
                  rfl

theorem cell21_1302652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_1302652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302652 prefixEnd_1302652 := by exact prefixLift 1302652
  have htrace : WordTrace (prefixWord ++ tailWord_1302652) baseStart_1302652 baseEnd_1302652 := by
    simpa [prefixWord, tailWord_1302652, baseEnd_1302652] using wordTrace_append hprefix tailTrace_1302652
  have hstable : (prefixWord ++ tailWord_1302652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302652).length < 2 ^ (prefixWord ++ tailWord_1302652).sum := by decide
  have hdescent : baseEnd_1302652 < baseStart_1302652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302686 : List Nat := [4, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1302686 : Nat := 118140960795 + 1302686 * 2 ^ 59
def prefixEnd_1302686 : Nat := 4983230072969 + 3 ^ 40 * 1302686 * 2
def baseEnd_1302686 : Nat := 99096897760443773145787

theorem tailTrace_1302686 : CollatzResearch.WordTrace tailWord_1302686 prefixEnd_1302686 99096897760443773145787 := by
  unfold tailWord_1302686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939107719824822237660989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31675241172399051934191941 5939107719824822237660989)
  ·
    refine ⟨2227165394934308339122871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5939107719824822237660989 2227165394934308339122871)
    ·
      refine ⟨3340748092401462508684307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227165394934308339122871 3340748092401462508684307)
      ·
        refine ⟨5011122138602193763026461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340748092401462508684307 5011122138602193763026461)
        ·
          refine ⟨1879170801975822661134923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5011122138602193763026461 1879170801975822661134923)
          ·
            refine ⟨2818756202963733991702385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879170801975822661134923 2818756202963733991702385)
            ·
              refine ⟨2114067152222800493776789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818756202963733991702385 2114067152222800493776789)
              ·
                refine ⟨99096897760443773145787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2114067152222800493776789 99096897760443773145787)
                ·
                  rfl

theorem cell21_1302686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1302686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302686 prefixEnd_1302686 := by exact prefixLift 1302686
  have htrace : WordTrace (prefixWord ++ tailWord_1302686) baseStart_1302686 baseEnd_1302686 := by
    simpa [prefixWord, tailWord_1302686, baseEnd_1302686] using wordTrace_append hprefix tailTrace_1302686
  have hstable : (prefixWord ++ tailWord_1302686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302686).length < 2 ^ (prefixWord ++ tailWord_1302686).sum := by decide
  have hdescent : baseEnd_1302686 < baseStart_1302686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302734 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_1302734 : Nat := 118140960795 + 1302734 * 2 ^ 59
def prefixEnd_1302734 : Nat := 4983230072969 + 3 ^ 40 * 1302734 * 2
def baseEnd_1302734 : Nat := 297301647535293902637263

theorem tailTrace_1302734 : CollatzResearch.WordTrace tailWord_1302734 prefixEnd_1302734 297301647535293902637263 := by
  unfold tailWord_1302734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939326557803085262379407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31676408308283121399356837 5939326557803085262379407)
  ·
    refine ⟨8908989836704627893569111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5939326557803085262379407 8908989836704627893569111)
    ·
      refine ⟨13363484755056941840353667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8908989836704627893569111 13363484755056941840353667)
      ·
        refine ⟨20045227132585412760530501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13363484755056941840353667 20045227132585412760530501)
        ·
          refine ⟨3758480087359764892599469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20045227132585412760530501 3758480087359764892599469)
          ·
            refine ⟨1409430032759911834724801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3758480087359764892599469 1409430032759911834724801)
            ·
              refine ⟨1057072524569933876043601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409430032759911834724801 1057072524569933876043601)
              ·
                refine ⟨792804393427450407032701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057072524569933876043601 792804393427450407032701)
                ·
                  refine ⟨297301647535293902637263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792804393427450407032701 297301647535293902637263)
                  ·
                    rfl

theorem cell21_1302734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_1302734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302734 prefixEnd_1302734 := by exact prefixLift 1302734
  have htrace : WordTrace (prefixWord ++ tailWord_1302734) baseStart_1302734 baseEnd_1302734 := by
    simpa [prefixWord, tailWord_1302734, baseEnd_1302734] using wordTrace_append hprefix tailTrace_1302734
  have hstable : (prefixWord ++ tailWord_1302734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302734).length < 2 ^ (prefixWord ++ tailWord_1302734).sum := by decide
  have hdescent : baseEnd_1302734 < baseStart_1302734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302759 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_1302759 : Nat := 118140960795 + 1302759 * 2 ^ 59
def prefixEnd_1302759 : Nat := 4983230072969 + 3 ^ 40 * 1302759 * 2
def baseEnd_1302759 : Nat := 297307352875899414720545

theorem tailTrace_1302759 : CollatzResearch.WordTrace tailWord_1302759 prefixEnd_1302759 297307352875899414720545 := by
  unfold tailWord_1302759
  simp only [CollatzResearch.WordTrace]
  refine ⟨47515524287334111368695331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31677016191556074245796887 47515524287334111368695331)
  ·
    refine ⟨71273286431001167053042997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47515524287334111368695331 71273286431001167053042997)
    ·
      refine ⟨6681870602906359411222781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71273286431001167053042997 6681870602906359411222781)
      ·
        refine ⟨2505701476089884779208543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6681870602906359411222781 2505701476089884779208543)
        ·
          refine ⟨3758552214134827168812815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505701476089884779208543 3758552214134827168812815)
          ·
            refine ⟨5637828321202240753219223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758552214134827168812815 5637828321202240753219223)
            ·
              refine ⟨8456742481803361129828835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5637828321202240753219223 8456742481803361129828835)
              ·
                refine ⟨12685113722705041694743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8456742481803361129828835 12685113722705041694743253)
                ·
                  refine ⟨297307352875899414720545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12685113722705041694743253 297307352875899414720545)
                  ·
                    rfl

theorem cell21_1302759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_1302759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302759 prefixEnd_1302759 := by exact prefixLift 1302759
  have htrace : WordTrace (prefixWord ++ tailWord_1302759) baseStart_1302759 baseEnd_1302759 := by
    simpa [prefixWord, tailWord_1302759, baseEnd_1302759] using wordTrace_append hprefix tailTrace_1302759
  have hstable : (prefixWord ++ tailWord_1302759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302759).length < 2 ^ (prefixWord ++ tailWord_1302759).sum := by decide
  have hdescent : baseEnd_1302759 < baseStart_1302759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302787 : List Nat := [1, 1, 1, 3, 2, 3, 10]
def baseStart_1302787 : Nat := 118140960795 + 1302787 * 2 ^ 59
def prefixEnd_1302787 : Nat := 4983230072969 + 3 ^ 40 * 1302787 * 2
def baseEnd_1302787 : Nat := 33034860317486398694869

theorem tailTrace_1302787 : CollatzResearch.WordTrace tailWord_1302787 prefixEnd_1302787 33034860317486398694869 := by
  unfold tailWord_1302787
  simp only [CollatzResearch.WordTrace]
  refine ⟨47516545531232672150714615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31677697020821781433809743 47516545531232672150714615)
  ·
    refine ⟨71274818296849008226071923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47516545531232672150714615 71274818296849008226071923)
    ·
      refine ⟨106912227445273512339107885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71274818296849008226071923 106912227445273512339107885)
      ·
        refine ⟨40092085291977567127165457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106912227445273512339107885 40092085291977567127165457)
        ·
          refine ⟨30069063968983175345374093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40092085291977567127165457 30069063968983175345374093)
          ·
            refine ⟨11275898988368690754515285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30069063968983175345374093 11275898988368690754515285)
            ·
              refine ⟨33034860317486398694869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11275898988368690754515285 33034860317486398694869)
              ·
                rfl

theorem cell21_1302787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 10].length) (baseStart_1302787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302787 prefixEnd_1302787 := by exact prefixLift 1302787
  have htrace : WordTrace (prefixWord ++ tailWord_1302787) baseStart_1302787 baseEnd_1302787 := by
    simpa [prefixWord, tailWord_1302787, baseEnd_1302787] using wordTrace_append hprefix tailTrace_1302787
  have hstable : (prefixWord ++ tailWord_1302787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302787).length < 2 ^ (prefixWord ++ tailWord_1302787).sum := by decide
  have hdescent : baseEnd_1302787 < baseStart_1302787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302807 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 4]
def baseStart_1302807 : Nat := 118140960795 + 1302807 * 2 ^ 59
def prefixEnd_1302807 : Nat := 4983230072969 + 3 ^ 40 * 1302807 * 2
def baseEnd_1302807 : Nat := 297318307129861997920447

theorem tailTrace_1302807 : CollatzResearch.WordTrace tailWord_1302807 prefixEnd_1302807 297318307129861997920447 := by
  unfold tailWord_1302807
  simp only [CollatzResearch.WordTrace]
  refine ⟨47517274991160215566442675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31678183327440143710961783 47517274991160215566442675)
  ·
    refine ⟨71275912486740323349664013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47517274991160215566442675 71275912486740323349664013)
    ·
      refine ⟨26728467182527621256124005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71275912486740323349664013 26728467182527621256124005)
      ·
        refine ⟨5011587596723928985523251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26728467182527621256124005 5011587596723928985523251)
        ·
          refine ⟨7517381395085893478284877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011587596723928985523251 7517381395085893478284877)
          ·
            refine ⟨2819018023157210054356829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7517381395085893478284877 2819018023157210054356829)
            ·
              refine ⟨1057131758683953770383811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2819018023157210054356829 1057131758683953770383811)
              ·
                refine ⟨1585697638025930655575717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057131758683953770383811 1585697638025930655575717)
                ·
                  refine ⟨297318307129861997920447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585697638025930655575717 297318307129861997920447)
                  ·
                    rfl

theorem cell21_1302807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4].length) (baseStart_1302807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302807 prefixEnd_1302807 := by exact prefixLift 1302807
  have htrace : WordTrace (prefixWord ++ tailWord_1302807) baseStart_1302807 baseEnd_1302807 := by
    simpa [prefixWord, tailWord_1302807, baseEnd_1302807] using wordTrace_append hprefix tailTrace_1302807
  have hstable : (prefixWord ++ tailWord_1302807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302807).length < 2 ^ (prefixWord ++ tailWord_1302807).sum := by decide
  have hdescent : baseEnd_1302807 < baseStart_1302807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302911 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 3]
def baseStart_1302911 : Nat := 118140960795 + 1302911 * 2 ^ 59
def prefixEnd_1302911 : Nat := 4983230072969 + 3 ^ 40 * 1302911 * 2
def baseEnd_1302911 : Nat := 297342041346780928186901

theorem tailTrace_1302911 : CollatzResearch.WordTrace tailWord_1302911 prefixEnd_1302911 297342041346780928186901 := by
  unfold tailWord_1302911
  simp only [CollatzResearch.WordTrace]
  refine ⟨47521068182783441328228587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31680712121855627552152391 47521068182783441328228587)
  ·
    refine ⟨71281602274175161992342881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47521068182783441328228587 71281602274175161992342881)
    ·
      refine ⟨53461201705631371494257161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71281602274175161992342881 53461201705631371494257161)
      ·
        refine ⟨40095901279223528620692871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53461201705631371494257161 40095901279223528620692871)
        ·
          refine ⟨60143851918835292931039307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40095901279223528620692871 60143851918835292931039307)
          ·
            refine ⟨90215777878252939396558961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60143851918835292931039307 90215777878252939396558961)
            ·
              refine ⟨67661833408689704547419221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90215777878252939396558961 67661833408689704547419221)
              ·
                refine ⟨792912110258082475165069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 67661833408689704547419221 792912110258082475165069)
                ·
                  refine ⟨297342041346780928186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792912110258082475165069 297342041346780928186901)
                  ·
                    rfl

theorem cell21_1302911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 3].length) (baseStart_1302911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1302911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1302911 prefixEnd_1302911 := by exact prefixLift 1302911
  have htrace : WordTrace (prefixWord ++ tailWord_1302911) baseStart_1302911 baseEnd_1302911 := by
    simpa [prefixWord, tailWord_1302911, baseEnd_1302911] using wordTrace_append hprefix tailTrace_1302911
  have hstable : (prefixWord ++ tailWord_1302911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302911).length < 2 ^ (prefixWord ++ tailWord_1302911).sum := by decide
  have hdescent : baseEnd_1302911 < baseStart_1302911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303077 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1303077 : Nat := 118140960795 + 1303077 * 2 ^ 59
def prefixEnd_1303077 : Nat := 4983230072969 + 3 ^ 40 * 1303077 * 2
def baseEnd_1303077 : Nat := 297379924808401528419895

theorem tailTrace_1303077 : CollatzResearch.WordTrace tailWord_1303077 prefixEnd_1303077 297379924808401528419895 := by
  unfold tailWord_1303077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47527122700182051678771485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31684748466788034452514323 47527122700182051678771485)
  ·
    refine ⟨17822671012568269379539307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47527122700182051678771485 17822671012568269379539307)
    ·
      refine ⟨26734006518852404069308961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17822671012568269379539307 26734006518852404069308961)
      ·
        refine ⟨20050504889139303051981721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26734006518852404069308961 20050504889139303051981721)
        ·
          refine ⟨15037878666854477288986291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20050504889139303051981721 15037878666854477288986291)
          ·
            refine ⟨22556818000281715933479437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15037878666854477288986291 22556818000281715933479437)
            ·
              refine ⟨8458806750105643475054789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22556818000281715933479437 8458806750105643475054789)
              ·
                refine ⟨1586026265644808151572773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8458806750105643475054789 1586026265644808151572773)
                ·
                  refine ⟨297379924808401528419895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586026265644808151572773 297379924808401528419895)
                  ·
                    rfl

theorem cell21_1303077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1303077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303077 prefixEnd_1303077 := by exact prefixLift 1303077
  have htrace : WordTrace (prefixWord ++ tailWord_1303077) baseStart_1303077 baseEnd_1303077 := by
    simpa [prefixWord, tailWord_1303077, baseEnd_1303077] using wordTrace_append hprefix tailTrace_1303077
  have hstable : (prefixWord ++ tailWord_1303077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303077).length < 2 ^ (prefixWord ++ tailWord_1303077).sum := by decide
  have hdescent : baseEnd_1303077 < baseStart_1303077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303122 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1303122 : Nat := 118140960795 + 1303122 * 2 ^ 59
def prefixEnd_1303122 : Nat := 4983230072969 + 3 ^ 40 * 1303122 * 2
def baseEnd_1303122 : Nat := 297390194421491450169803

theorem tailTrace_1303122 : CollatzResearch.WordTrace tailWord_1303122 prefixEnd_1303122 297390194421491450169803 := by
  unfold tailWord_1303122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11882190996254756091039905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31685842656679349576106413 11882190996254756091039905)
  ·
    refine ⟨8911643247191067068279929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11882190996254756091039905 8911643247191067068279929)
    ·
      refine ⟨6683732435393300301209947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8911643247191067068279929 6683732435393300301209947)
      ·
        refine ⟨10025598653089950451814921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6683732435393300301209947 10025598653089950451814921)
        ·
          refine ⟨7519198989817462838861191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10025598653089950451814921 7519198989817462838861191)
          ·
            refine ⟨11278798484726194258291787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519198989817462838861191 11278798484726194258291787)
            ·
              refine ⟨16918197727089291387437681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11278798484726194258291787 16918197727089291387437681)
              ·
                refine ⟨12688648295316968540578261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16918197727089291387437681 12688648295316968540578261)
                ·
                  refine ⟨297390194421491450169803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12688648295316968540578261 297390194421491450169803)
                  ·
                    rfl

theorem cell21_1303122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1303122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303122 prefixEnd_1303122 := by exact prefixLift 1303122
  have htrace : WordTrace (prefixWord ++ tailWord_1303122) baseStart_1303122 baseEnd_1303122 := by
    simpa [prefixWord, tailWord_1303122, baseEnd_1303122] using wordTrace_append hprefix tailTrace_1303122
  have hstable : (prefixWord ++ tailWord_1303122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303122).length < 2 ^ (prefixWord ++ tailWord_1303122).sum := by decide
  have hdescent : baseEnd_1303122 < baseStart_1303122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303139 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 3]
def baseStart_1303139 : Nat := 118140960795 + 1303139 * 2 ^ 59
def prefixEnd_1303139 : Nat := 4983230072969 + 3 ^ 40 * 1303139 * 2
def baseEnd_1303139 : Nat := 297394074053103198386435

theorem tailTrace_1303139 : CollatzResearch.WordTrace tailWord_1303139 prefixEnd_1303139 297394074053103198386435 := by
  unfold tailWord_1303139
  simp only [CollatzResearch.WordTrace]
  refine ⟨47529384025957436267528471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31686256017304957511685647 47529384025957436267528471)
  ·
    refine ⟨71294076038936154401292707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47529384025957436267528471 71294076038936154401292707)
    ·
      refine ⟨106941114058404231601939061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71294076038936154401292707 106941114058404231601939061)
      ·
        refine ⟨10025729442975396712681787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106941114058404231601939061 10025729442975396712681787)
        ·
          refine ⟨15038594164463095069022681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10025729442975396712681787 15038594164463095069022681)
          ·
            refine ⟨11278945623347321301767011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15038594164463095069022681 11278945623347321301767011)
            ·
              refine ⟨16918418435020981952650517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11278945623347321301767011 16918418435020981952650517)
              ·
                refine ⟨793050864141608529030493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16918418435020981952650517 793050864141608529030493)
                ·
                  refine ⟨297394074053103198386435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793050864141608529030493 297394074053103198386435)
                  ·
                    rfl

theorem cell21_1303139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3].length) (baseStart_1303139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303139 prefixEnd_1303139 := by exact prefixLift 1303139
  have htrace : WordTrace (prefixWord ++ tailWord_1303139) baseStart_1303139 baseEnd_1303139 := by
    simpa [prefixWord, tailWord_1303139, baseEnd_1303139] using wordTrace_append hprefix tailTrace_1303139
  have hstable : (prefixWord ++ tailWord_1303139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303139).length < 2 ^ (prefixWord ++ tailWord_1303139).sum := by decide
  have hdescent : baseEnd_1303139 < baseStart_1303139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303246 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1303246 : Nat := 118140960795 + 1303246 * 2 ^ 59
def prefixEnd_1303246 : Nat := 4983230072969 + 3 ^ 40 * 1303246 * 2
def baseEnd_1303246 : Nat := 297418492910894790102883

theorem tailTrace_1303246 : CollatzResearch.WordTrace tailWord_1303246 prefixEnd_1303246 297418492910894790102883 := by
  unfold tailWord_1303246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941660829571224192709199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31688857757713195694449061 5941660829571224192709199)
  ·
    refine ⟨8912491244356836289063799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5941660829571224192709199 8912491244356836289063799)
    ·
      refine ⟨13368736866535254433595699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8912491244356836289063799 13368736866535254433595699)
      ·
        refine ⟨20053105299802881650393549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368736866535254433595699 20053105299802881650393549)
        ·
          refine ⟨7519914487426080618897581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20053105299802881650393549 7519914487426080618897581)
          ·
            refine ⟨2819967932784780232086593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7519914487426080618897581 2819967932784780232086593)
            ·
              refine ⟨2114975949588585174064945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819967932784780232086593 2114975949588585174064945)
              ·
                refine ⟨1586231962191438880548709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114975949588585174064945 1586231962191438880548709)
                ·
                  refine ⟨297418492910894790102883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586231962191438880548709 297418492910894790102883)
                  ·
                    rfl

theorem cell21_1303246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1303246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303246 prefixEnd_1303246 := by exact prefixLift 1303246
  have htrace : WordTrace (prefixWord ++ tailWord_1303246) baseStart_1303246 baseEnd_1303246 := by
    simpa [prefixWord, tailWord_1303246, baseEnd_1303246] using wordTrace_append hprefix tailTrace_1303246
  have hstable : (prefixWord ++ tailWord_1303246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303246).length < 2 ^ (prefixWord ++ tailWord_1303246).sum := by decide
  have hdescent : baseEnd_1303246 < baseStart_1303246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303288 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_1303288 : Nat := 118140960795 + 1303288 * 2 ^ 59
def prefixEnd_1303288 : Nat := 4983230072969 + 3 ^ 40 * 1303288 * 2
def baseEnd_1303288 : Nat := 297428077883112050402797

theorem tailTrace_1303288 : CollatzResearch.WordTrace tailWord_1303288 prefixEnd_1303288 297428077883112050402797 := by
  unfold tailWord_1303288
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767409251208817357351259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31689879001611756476468345 23767409251208817357351259)
  ·
    refine ⟨35651113876813226036026889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23767409251208817357351259 35651113876813226036026889)
    ·
      refine ⟨26738335407609919527020167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35651113876813226036026889 26738335407609919527020167)
      ·
        refine ⟨40107503111414879290530251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26738335407609919527020167 40107503111414879290530251)
        ·
          refine ⟨60161254667122318935795377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40107503111414879290530251 60161254667122318935795377)
          ·
            refine ⟨45120941000341739201846533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60161254667122318935795377 45120941000341739201846533)
            ·
              refine ⟨8460176437564076100346225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45120941000341739201846533 8460176437564076100346225)
              ·
                refine ⟨6345132328173057075259669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8460176437564076100346225 6345132328173057075259669)
                ·
                  refine ⟨297428077883112050402797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6345132328173057075259669 297428077883112050402797)
                  ·
                    rfl

theorem cell21_1303288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_1303288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303288 prefixEnd_1303288 := by exact prefixLift 1303288
  have htrace : WordTrace (prefixWord ++ tailWord_1303288) baseStart_1303288 baseEnd_1303288 := by
    simpa [prefixWord, tailWord_1303288, baseEnd_1303288] using wordTrace_append hprefix tailTrace_1303288
  have hstable : (prefixWord ++ tailWord_1303288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303288).length < 2 ^ (prefixWord ++ tailWord_1303288).sum := by decide
  have hdescent : baseEnd_1303288 < baseStart_1303288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303305 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_1303305 : Nat := 118140960795 + 1303305 * 2 ^ 59
def prefixEnd_1303305 : Nat := 4983230072969 + 3 ^ 40 * 1303305 * 2
def baseEnd_1303305 : Nat := 297431957514723798619429

theorem tailTrace_1303305 : CollatzResearch.WordTrace tailWord_1303305 prefixEnd_1303305 297431957514723798619429 := by
  unfold tailWord_1303305
  simp only [CollatzResearch.WordTrace]
  refine ⟨47535438543356046618071369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31690292362237364412047579 47535438543356046618071369)
  ·
    refine ⟨35651578907517034963553527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47535438543356046618071369 35651578907517034963553527)
    ·
      refine ⟨53477368361275552445330291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35651578907517034963553527 53477368361275552445330291)
      ·
        refine ⟨80216052541913328667995437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53477368361275552445330291 80216052541913328667995437)
        ·
          refine ⟨30081019703217498250498289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80216052541913328667995437 30081019703217498250498289)
          ·
            refine ⟨22560764777413123687873717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30081019703217498250498289 22560764777413123687873717)
            ·
              refine ⟨2115071697882480345738161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22560764777413123687873717 2115071697882480345738161)
              ·
                refine ⟨1586303773411860259303621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2115071697882480345738161 1586303773411860259303621)
                ·
                  refine ⟨297431957514723798619429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586303773411860259303621 297431957514723798619429)
                  ·
                    rfl

theorem cell21_1303305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_1303305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303305 prefixEnd_1303305 := by exact prefixLift 1303305
  have htrace : WordTrace (prefixWord ++ tailWord_1303305) baseStart_1303305 baseEnd_1303305 := by
    simpa [prefixWord, tailWord_1303305, baseEnd_1303305] using wordTrace_append hprefix tailTrace_1303305
  have hstable : (prefixWord ++ tailWord_1303305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303305).length < 2 ^ (prefixWord ++ tailWord_1303305).sum := by decide
  have hdescent : baseEnd_1303305 < baseStart_1303305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303322 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_1303322 : Nat := 118140960795 + 1303322 * 2 ^ 59
def prefixEnd_1303322 : Nat := 4983230072969 + 3 ^ 40 * 1303322 * 2
def baseEnd_1303322 : Nat := 297435837146335546836061

theorem tailTrace_1303322 : CollatzResearch.WordTrace tailWord_1303322 prefixEnd_1303322 297435837146335546836061 := by
  unfold tailWord_1303322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11884014646073614630360055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31690705722862972347626813 11884014646073614630360055)
  ·
    refine ⟨17826021969110421945540083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11884014646073614630360055 17826021969110421945540083)
    ·
      refine ⟨26739032953665632918310125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17826021969110421945540083 26739032953665632918310125)
      ·
        refine ⟨10027137357624612344366297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26739032953665632918310125 10027137357624612344366297)
        ·
          refine ⟨7520353018218459258274723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10027137357624612344366297 7520353018218459258274723)
          ·
            refine ⟨11280529527327688887412085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7520353018218459258274723 11280529527327688887412085)
            ·
              refine ⟨1057549643186970833194883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11280529527327688887412085 1057549643186970833194883)
              ·
                refine ⟨1586324464780456249792325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057549643186970833194883 1586324464780456249792325)
                ·
                  refine ⟨297435837146335546836061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586324464780456249792325 297435837146335546836061)
                  ·
                    rfl

theorem cell21_1303322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_1303322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303322 prefixEnd_1303322 := by exact prefixLift 1303322
  have htrace : WordTrace (prefixWord ++ tailWord_1303322) baseStart_1303322 baseEnd_1303322 := by
    simpa [prefixWord, tailWord_1303322, baseEnd_1303322] using wordTrace_append hprefix tailTrace_1303322
  have hstable : (prefixWord ++ tailWord_1303322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303322).length < 2 ^ (prefixWord ++ tailWord_1303322).sum := by decide
  have hdescent : baseEnd_1303322 < baseStart_1303322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303373 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1303373 : Nat := 118140960795 + 1303373 * 2 ^ 59
def prefixEnd_1303373 : Nat := 4983230072969 + 3 ^ 40 * 1303373 * 2
def baseEnd_1303373 : Nat := 297447476041170791485957

theorem tailTrace_1303373 : CollatzResearch.WordTrace tailWord_1303373 prefixEnd_1303373 297447476041170791485957 := by
  unfold tailWord_1303373
  simp only [CollatzResearch.WordTrace]
  refine ⟨47537918707109694231546773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31691945804739796154364515 47537918707109694231546773)
  ·
    refine ⟨2228339939395766917103755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47537918707109694231546773 2228339939395766917103755)
    ·
      refine ⟨3342509909093650375655633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228339939395766917103755 3342509909093650375655633)
      ·
        refine ⟨2506882431820237781741725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3342509909093650375655633 2506882431820237781741725)
        ·
          refine ⟨940080911932589168153147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2506882431820237781741725 940080911932589168153147)
          ·
            refine ⟨1410121367898883752229721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940080911932589168153147 1410121367898883752229721)
            ·
              refine ⟨1057591025924162814172291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410121367898883752229721 1057591025924162814172291)
              ·
                refine ⟨1586386538886244221258437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057591025924162814172291 1586386538886244221258437)
                ·
                  refine ⟨297447476041170791485957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586386538886244221258437 297447476041170791485957)
                  ·
                    rfl

theorem cell21_1303373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1303373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303373 prefixEnd_1303373 := by exact prefixLift 1303373
  have htrace : WordTrace (prefixWord ++ tailWord_1303373) baseStart_1303373 baseEnd_1303373 := by
    simpa [prefixWord, tailWord_1303373, baseEnd_1303373] using wordTrace_append hprefix tailTrace_1303373
  have hstable : (prefixWord ++ tailWord_1303373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303373).length < 2 ^ (prefixWord ++ tailWord_1303373).sum := by decide
  have hdescent : baseEnd_1303373 < baseStart_1303373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303381 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1303381 : Nat := 118140960795 + 1303381 * 2 ^ 59
def prefixEnd_1303381 : Nat := 4983230072969 + 3 ^ 40 * 1303381 * 2
def baseEnd_1303381 : Nat := 297449301750164555352607

theorem tailTrace_1303381 : CollatzResearch.WordTrace tailWord_1303381 prefixEnd_1303381 297449301750164555352607 := by
  unfold tailWord_1303381
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538210491080711597837997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31692140327387141065225331 47538210491080711597837997)
  ·
    refine ⟨17826828934155266849189249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47538210491080711597837997 17826828934155266849189249)
    ·
      refine ⟨13370121700616450136891937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17826828934155266849189249 13370121700616450136891937)
      ·
        refine ⟨10027591275462337602668953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13370121700616450136891937 10027591275462337602668953)
        ·
          refine ⟨7520693456596753202001715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10027591275462337602668953 7520693456596753202001715)
          ·
            refine ⟨11281040184895129803002573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7520693456596753202001715 11281040184895129803002573)
            ·
              refine ⟨4230390069335673676125965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11281040184895129803002573 4230390069335673676125965)
              ·
                refine ⟨1586396276000877628547237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4230390069335673676125965 1586396276000877628547237)
                ·
                  refine ⟨297449301750164555352607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586396276000877628547237 297449301750164555352607)
                  ·
                    rfl

theorem cell21_1303381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1303381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303381 prefixEnd_1303381 := by exact prefixLift 1303381
  have htrace : WordTrace (prefixWord ++ tailWord_1303381) baseStart_1303381 baseEnd_1303381 := by
    simpa [prefixWord, tailWord_1303381, baseEnd_1303381] using wordTrace_append hprefix tailTrace_1303381
  have hstable : (prefixWord ++ tailWord_1303381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303381).length < 2 ^ (prefixWord ++ tailWord_1303381).sum := by decide
  have hdescent : baseEnd_1303381 < baseStart_1303381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303395 : List Nat := [1, 1, 1, 5, 3, 1, 2, 7]
def baseStart_1303395 : Nat := 118140960795 + 1303395 * 2 ^ 59
def prefixEnd_1303395 : Nat := 4983230072969 + 3 ^ 40 * 1303395 * 2
def baseEnd_1303395 : Nat := 99150832246967880706415

theorem tailTrace_1303395 : CollatzResearch.WordTrace tailWord_1303395 prefixEnd_1303395 99150832246967880706415 := by
  unfold tailWord_1303395
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538721113029991988847639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31692480742019994659231759 47538721113029991988847639)
  ·
    refine ⟨71308081669544987983271459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47538721113029991988847639 71308081669544987983271459)
    ·
      refine ⟨106962122504317481974907189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71308081669544987983271459 106962122504317481974907189)
      ·
        refine ⟨10027698984779763935147549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106962122504317481974907189 10027698984779763935147549)
        ·
          refine ⟨3760387119292411475680331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10027698984779763935147549 3760387119292411475680331)
          ·
            refine ⟨5640580678938617213520497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760387119292411475680331 5640580678938617213520497)
            ·
              refine ⟨4230435509203962910140373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5640580678938617213520497 4230435509203962910140373)
              ·
                refine ⟨99150832246967880706415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4230435509203962910140373 99150832246967880706415)
                ·
                  rfl

theorem cell21_1303395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_1303395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303395 prefixEnd_1303395 := by exact prefixLift 1303395
  have htrace : WordTrace (prefixWord ++ tailWord_1303395) baseStart_1303395 baseEnd_1303395 := by
    simpa [prefixWord, tailWord_1303395, baseEnd_1303395] using wordTrace_append hprefix tailTrace_1303395
  have hstable : (prefixWord ++ tailWord_1303395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303395).length < 2 ^ (prefixWord ++ tailWord_1303395).sum := by decide
  have hdescent : baseEnd_1303395 < baseStart_1303395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303502 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1303502 : Nat := 118140960795 + 1303502 * 2 ^ 59
def prefixEnd_1303502 : Nat := 4983230072969 + 3 ^ 40 * 1303502 * 2
def baseEnd_1303502 : Nat := 297476915598695233835693

theorem tailTrace_1303502 : CollatzResearch.WordTrace tailWord_1303502 prefixEnd_1303502 297476915598695233835693 := by
  unfold tailWord_1303502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942827965455293657874095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31695082482428232841995173 5942827965455293657874095)
  ·
    refine ⟨8914241948182940486811143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5942827965455293657874095 8914241948182940486811143)
    ·
      refine ⟨13371362922274410730216715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8914241948182940486811143 13371362922274410730216715)
      ·
        refine ⟨20057044383411616095325073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13371362922274410730216715 20057044383411616095325073)
        ·
          refine ⟨15042783287558712071493805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20057044383411616095325073 15042783287558712071493805)
          ·
            refine ⟨5641043732834517026810177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15042783287558712071493805 5641043732834517026810177)
            ·
              refine ⟨4230782799625887770107633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641043732834517026810177 4230782799625887770107633)
              ·
                refine ⟨3173087099719415827580725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230782799625887770107633 3173087099719415827580725)
                ·
                  refine ⟨297476915598695233835693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3173087099719415827580725 297476915598695233835693)
                  ·
                    rfl

theorem cell21_1303502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1303502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303502 prefixEnd_1303502 := by exact prefixLift 1303502
  have htrace : WordTrace (prefixWord ++ tailWord_1303502) baseStart_1303502 baseEnd_1303502 := by
    simpa [prefixWord, tailWord_1303502, baseEnd_1303502] using wordTrace_append hprefix tailTrace_1303502
  have hstable : (prefixWord ++ tailWord_1303502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303502).length < 2 ^ (prefixWord ++ tailWord_1303502).sum := by decide
  have hdescent : baseEnd_1303502 < baseStart_1303502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303561 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_1303561 : Nat := 118140960795 + 1303561 * 2 ^ 59
def prefixEnd_1303561 : Nat := 4983230072969 + 3 ^ 40 * 1303561 * 2
def baseEnd_1303561 : Nat := 297490380202524242352239

theorem tailTrace_1303561 : CollatzResearch.WordTrace tailWord_1303561 prefixEnd_1303561 297490380202524242352239 := by
  unfold tailWord_1303561
  simp only [CollatzResearch.WordTrace]
  refine ⟨47544775630428602339390537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31696517086952401559593691 47544775630428602339390537)
  ·
    refine ⟨35658581722821451754542903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47544775630428602339390537 35658581722821451754542903)
    ·
      refine ⟨53487872584232177631814355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35658581722821451754542903 53487872584232177631814355)
      ·
        refine ⟨80231808876348266447721533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53487872584232177631814355 80231808876348266447721533)
        ·
          refine ⟨30086928328630599917895575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80231808876348266447721533 30086928328630599917895575)
          ·
            refine ⟨45130392492945899876843363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30086928328630599917895575 45130392492945899876843363)
            ·
              refine ⟨67695588739418849815265045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45130392492945899876843363 67695588739418849815265045)
              ·
                refine ⟨3173230722160258585090549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67695588739418849815265045 3173230722160258585090549)
                ·
                  refine ⟨297490380202524242352239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3173230722160258585090549 297490380202524242352239)
                  ·
                    rfl

theorem cell21_1303561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_1303561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303561 prefixEnd_1303561 := by exact prefixLift 1303561
  have htrace : WordTrace (prefixWord ++ tailWord_1303561) baseStart_1303561 baseEnd_1303561 := by
    simpa [prefixWord, tailWord_1303561, baseEnd_1303561] using wordTrace_append hprefix tailTrace_1303561
  have hstable : (prefixWord ++ tailWord_1303561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303561).length < 2 ^ (prefixWord ++ tailWord_1303561).sum := by decide
  have hdescent : baseEnd_1303561 < baseStart_1303561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303609 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_1303609 : Nat := 118140960795 + 1303609 * 2 ^ 59
def prefixEnd_1303609 : Nat := 4983230072969 + 3 ^ 40 * 1303609 * 2
def baseEnd_1303609 : Nat := 297501334456486825552141

theorem tailTrace_1303609 : CollatzResearch.WordTrace tailWord_1303609 prefixEnd_1303609 297501334456486825552141 := by
  unfold tailWord_1303609
  simp only [CollatzResearch.WordTrace]
  refine ⟨47546526334254706537137881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31697684222836471024758587 47546526334254706537137881)
  ·
    refine ⟨35659894750691029902853411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47546526334254706537137881 35659894750691029902853411)
    ·
      refine ⟨53489842126036544854280117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35659894750691029902853411 53489842126036544854280117)
      ·
        refine ⟨5014672699315926080088761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53489842126036544854280117 5014672699315926080088761)
        ·
          refine ⟨3761004524486944560066571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5014672699315926080088761 3761004524486944560066571)
          ·
            refine ⟨5641506786730416840099857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761004524486944560066571 5641506786730416840099857)
            ·
              refine ⟨4231130090047812630074893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641506786730416840099857 4231130090047812630074893)
              ·
                refine ⟨1586673783767929736278085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4231130090047812630074893 1586673783767929736278085)
                ·
                  refine ⟨297501334456486825552141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586673783767929736278085 297501334456486825552141)
                  ·
                    rfl

theorem cell21_1303609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_1303609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303609 prefixEnd_1303609 := by exact prefixLift 1303609
  have htrace : WordTrace (prefixWord ++ tailWord_1303609) baseStart_1303609 baseEnd_1303609 := by
    simpa [prefixWord, tailWord_1303609, baseEnd_1303609] using wordTrace_append hprefix tailTrace_1303609
  have hstable : (prefixWord ++ tailWord_1303609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303609).length < 2 ^ (prefixWord ++ tailWord_1303609).sum := by decide
  have hdescent : baseEnd_1303609 < baseStart_1303609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303637 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1303637 : Nat := 118140960795 + 1303637 * 2 ^ 59
def prefixEnd_1303637 : Nat := 4983230072969 + 3 ^ 40 * 1303637 * 2
def baseEnd_1303637 : Nat := 297507724437964999085417

theorem tailTrace_1303637 : CollatzResearch.WordTrace tailWord_1303637 prefixEnd_1303637 297507724437964999085417 := by
  unfold tailWord_1303637
  simp only [CollatzResearch.WordTrace]
  refine ⟨47547547578153267319157165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31698365052102178212771443 47547547578153267319157165)
  ·
    refine ⟨17830330341807475244683937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47547547578153267319157165 17830330341807475244683937)
    ·
      refine ⟨13372747756355606433512953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17830330341807475244683937 13372747756355606433512953)
      ·
        refine ⟨10029560817266704825134715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13372747756355606433512953 10029560817266704825134715)
        ·
          refine ⟨15044341225900057237702073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10029560817266704825134715 15044341225900057237702073)
          ·
            refine ⟨11283255919425042928276555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15044341225900057237702073 11283255919425042928276555)
            ·
              refine ⟨16924883879137564392414833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283255919425042928276555 16924883879137564392414833)
              ·
                refine ⟨12693662909353173294311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16924883879137564392414833 12693662909353173294311125)
                ·
                  refine ⟨297507724437964999085417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12693662909353173294311125 297507724437964999085417)
                  ·
                    rfl

theorem cell21_1303637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1303637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303637 prefixEnd_1303637 := by exact prefixLift 1303637
  have htrace : WordTrace (prefixWord ++ tailWord_1303637) baseStart_1303637 baseEnd_1303637 := by
    simpa [prefixWord, tailWord_1303637, baseEnd_1303637] using wordTrace_append hprefix tailTrace_1303637
  have hstable : (prefixWord ++ tailWord_1303637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303637).length < 2 ^ (prefixWord ++ tailWord_1303637).sum := by decide
  have hdescent : baseEnd_1303637 < baseStart_1303637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303719 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 4]
def baseStart_1303719 : Nat := 118140960795 + 1303719 * 2 ^ 59
def prefixEnd_1303719 : Nat := 4983230072969 + 3 ^ 40 * 1303719 * 2
def baseEnd_1303719 : Nat := 297526437955151078718583

theorem tailTrace_1303719 : CollatzResearch.WordTrace tailWord_1303719 prefixEnd_1303719 297526437955151078718583 := by
  unfold tailWord_1303719
  simp only [CollatzResearch.WordTrace]
  refine ⟨47550538363856195323642211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31700358909237463549094807 47550538363856195323642211)
  ·
    refine ⟨71325807545784292985463317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47550538363856195323642211 71325807545784292985463317)
    ·
      refine ⟨3343397228708638733693593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71325807545784292985463317 3343397228708638733693593)
      ·
        refine ⟨2507547921531479050270195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3343397228708638733693593 2507547921531479050270195)
        ·
          refine ⟨3761321882297218575405293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507547921531479050270195 3761321882297218575405293)
          ·
            refine ⟨1410495705861456965776985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3761321882297218575405293 1410495705861456965776985)
            ·
              refine ⟨1057871779396092724332739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410495705861456965776985 1057871779396092724332739)
              ·
                refine ⟨1586807669094139086499109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057871779396092724332739 1586807669094139086499109)
                ·
                  refine ⟨297526437955151078718583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586807669094139086499109 297526437955151078718583)
                  ·
                    rfl

theorem cell21_1303719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4].length) (baseStart_1303719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303719 prefixEnd_1303719 := by exact prefixLift 1303719
  have htrace : WordTrace (prefixWord ++ tailWord_1303719) baseStart_1303719 baseEnd_1303719 := by
    simpa [prefixWord, tailWord_1303719, baseEnd_1303719] using wordTrace_append hprefix tailTrace_1303719
  have hstable : (prefixWord ++ tailWord_1303719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303719).length < 2 ^ (prefixWord ++ tailWord_1303719).sum := by decide
  have hdescent : baseEnd_1303719 < baseStart_1303719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303750 : List Nat := [6, 1, 2, 2, 2, 8]
def baseStart_1303750 : Nat := 118140960795 + 1303750 * 2 ^ 59
def prefixEnd_1303750 : Nat := 4983230072969 + 3 ^ 40 * 1303750 * 2
def baseEnd_1303750 : Nat := 11019759725092663470439

theorem tailTrace_1303750 : CollatzResearch.WordTrace tailWord_1303750 prefixEnd_1303750 11019759725092663470439 := by
  unfold tailWord_1303750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485989657085746488063147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31701112684495925078680469 1485989657085746488063147)
  ·
    refine ⟨2228984485628619732094721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1485989657085746488063147 2228984485628619732094721)
    ·
      refine ⟨1671738364221464799071041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2228984485628619732094721 1671738364221464799071041)
      ·
        refine ⟨1253803773166098599303281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1671738364221464799071041 1253803773166098599303281)
        ·
          refine ⟨940352829874573949477461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253803773166098599303281 940352829874573949477461)
          ·
            refine ⟨11019759725092663470439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 940352829874573949477461 11019759725092663470439)
            ·
              rfl

theorem cell21_1303750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 8].length) (baseStart_1303750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303750 prefixEnd_1303750 := by exact prefixLift 1303750
  have htrace : WordTrace (prefixWord ++ tailWord_1303750) baseStart_1303750 baseEnd_1303750 := by
    simpa [prefixWord, tailWord_1303750, baseEnd_1303750] using wordTrace_append hprefix tailTrace_1303750
  have hstable : (prefixWord ++ tailWord_1303750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303750).length < 2 ^ (prefixWord ++ tailWord_1303750).sum := by decide
  have hdescent : baseEnd_1303750 < baseStart_1303750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303758 : List Nat := [4, 1, 1, 1, 14]
def baseStart_1303758 : Nat := 118140960795 + 1303758 * 2 ^ 59
def prefixEnd_1303758 : Nat := 4983230072969 + 3 ^ 40 * 1303758 * 2
def baseEnd_1303758 : Nat := 3673275781314761451463

theorem tailTrace_1303758 : CollatzResearch.WordTrace tailWord_1303758 prefixEnd_1303758 3673275781314761451463 := by
  unfold tailWord_1303758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943995101339363123038991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31701307207143269989541285 5943995101339363123038991)
  ·
    refine ⟨8915992652009044684558487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943995101339363123038991 8915992652009044684558487)
    ·
      refine ⟨13373988978013567026837731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8915992652009044684558487 13373988978013567026837731)
      ·
        refine ⟨20060983467020350540256597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13373988978013567026837731 20060983467020350540256597)
        ·
          refine ⟨3673275781314761451463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20060983467020350540256597 3673275781314761451463)
          ·
            rfl

theorem cell21_1303758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 14].length) (baseStart_1303758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303758 prefixEnd_1303758 := by exact prefixLift 1303758
  have htrace : WordTrace (prefixWord ++ tailWord_1303758) baseStart_1303758 baseEnd_1303758 := by
    simpa [prefixWord, tailWord_1303758, baseEnd_1303758] using wordTrace_append hprefix tailTrace_1303758
  have hstable : (prefixWord ++ tailWord_1303758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303758).length < 2 ^ (prefixWord ++ tailWord_1303758).sum := by decide
  have hdescent : baseEnd_1303758 < baseStart_1303758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303820 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1303820 : Nat := 118140960795 + 1303820 * 2 ^ 59
def prefixEnd_1303820 : Nat := 4983230072969 + 3 ^ 40 * 1303820 * 2
def baseEnd_1303820 : Nat := 297549487531197347535043

theorem tailTrace_1303820 : CollatzResearch.WordTrace tailWord_1303820 prefixEnd_1303820 297549487531197347535043 := by
  unfold tailWord_1303820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23777111068245144786534457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31702814757660193048712609 23777111068245144786534457)
  ·
    refine ⟨17832833301183858589900843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23777111068245144786534457 17832833301183858589900843)
    ·
      refine ⟨26749249951775787884851265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17832833301183858589900843 26749249951775787884851265)
      ·
        refine ⟨20061937463831840913638449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26749249951775787884851265 20061937463831840913638449)
        ·
          refine ⟨15046453097873880685228837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20061937463831840913638449 15046453097873880685228837)
          ·
            refine ⟨2821209955851352628480407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15046453097873880685228837 2821209955851352628480407)
            ·
              refine ⟨4231814933777028942720611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821209955851352628480407 4231814933777028942720611)
              ·
                refine ⟨6347722400665543414080917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4231814933777028942720611 6347722400665543414080917)
                ·
                  refine ⟨297549487531197347535043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6347722400665543414080917 297549487531197347535043)
                  ·
                    rfl

theorem cell21_1303820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1303820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303820 prefixEnd_1303820 := by exact prefixLift 1303820
  have htrace : WordTrace (prefixWord ++ tailWord_1303820) baseStart_1303820 baseEnd_1303820 := by
    simpa [prefixWord, tailWord_1303820, baseEnd_1303820] using wordTrace_append hprefix tailTrace_1303820
  have hstable : (prefixWord ++ tailWord_1303820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303820).length < 2 ^ (prefixWord ++ tailWord_1303820).sum := by decide
  have hdescent : baseEnd_1303820 < baseStart_1303820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303882 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_1303882 : Nat := 118140960795 + 1303882 * 2 ^ 59
def prefixEnd_1303882 : Nat := 4983230072969 + 3 ^ 40 * 1303882 * 2
def baseEnd_1303882 : Nat := 297563636775899017501583

theorem tailTrace_1303882 : CollatzResearch.WordTrace tailWord_1303882 prefixEnd_1303882 297563636775899017501583 := by
  unfold tailWord_1303882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11889120865566418540456475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31704322308177116107883933 11889120865566418540456475)
  ·
    refine ⟨17833681298349627810684713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11889120865566418540456475 17833681298349627810684713)
    ·
      refine ⟨13375260973762220858013535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17833681298349627810684713 13375260973762220858013535)
      ·
        refine ⟨20062891460643331287020303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13375260973762220858013535 20062891460643331287020303)
        ·
          refine ⟨30094337190964996930530455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20062891460643331287020303 30094337190964996930530455)
          ·
            refine ⟨45141505786447495395795683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30094337190964996930530455 45141505786447495395795683)
            ·
              refine ⟨67712258679671243093693525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45141505786447495395795683 67712258679671243093693525)
              ·
                refine ⟨793503031402397380004221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 67712258679671243093693525 793503031402397380004221)
                ·
                  refine ⟨297563636775899017501583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793503031402397380004221 297563636775899017501583)
                  ·
                    rfl

theorem cell21_1303882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_1303882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303882 prefixEnd_1303882 := by exact prefixLift 1303882
  have htrace : WordTrace (prefixWord ++ tailWord_1303882) baseStart_1303882 baseEnd_1303882 := by
    simpa [prefixWord, tailWord_1303882, baseEnd_1303882] using wordTrace_append hprefix tailTrace_1303882
  have hstable : (prefixWord ++ tailWord_1303882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303882).length < 2 ^ (prefixWord ++ tailWord_1303882).sum := by decide
  have hdescent : baseEnd_1303882 < baseStart_1303882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303885 : List Nat := [1, 6, 1, 3, 1, 1, 2, 6]
def baseStart_1303885 : Nat := 118140960795 + 1303885 * 2 ^ 59
def prefixEnd_1303885 : Nat := 4983230072969 + 3 ^ 40 * 1303885 * 2
def baseEnd_1303885 : Nat := 99188107138923892983859

theorem tailTrace_1303885 : CollatzResearch.WordTrace tailWord_1303885 prefixEnd_1303885 99188107138923892983859 := by
  unfold tailWord_1303885
  simp only [CollatzResearch.WordTrace]
  refine ⟨47556592881254805674185109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31704395254169870449456739 47556592881254805674185109)
  ·
    refine ⟨2229215291308819015977427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47556592881254805674185109 2229215291308819015977427)
    ·
      refine ⟨3343822936963228523966141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229215291308819015977427 3343822936963228523966141)
      ·
        refine ⟨1253933601361210696487303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3343822936963228523966141 1253933601361210696487303)
        ·
          refine ⟨1880900402041816044730955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253933601361210696487303 1880900402041816044730955)
          ·
            refine ⟨2821350603062724067096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880900402041816044730955 2821350603062724067096433)
            ·
              refine ⟨2116012952297043050322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821350603062724067096433 2116012952297043050322325)
              ·
                refine ⟨99188107138923892983859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2116012952297043050322325 99188107138923892983859)
                ·
                  rfl

theorem cell21_1303885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 6].length) (baseStart_1303885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303885 prefixEnd_1303885 := by exact prefixLift 1303885
  have htrace : WordTrace (prefixWord ++ tailWord_1303885) baseStart_1303885 baseEnd_1303885 := by
    simpa [prefixWord, tailWord_1303885, baseEnd_1303885] using wordTrace_append hprefix tailTrace_1303885
  have hstable : (prefixWord ++ tailWord_1303885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303885).length < 2 ^ (prefixWord ++ tailWord_1303885).sum := by decide
  have hdescent : baseEnd_1303885 < baseStart_1303885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303896 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_1303896 : Nat := 118140960795 + 1303896 * 2 ^ 59
def prefixEnd_1303896 : Nat := 4983230072969 + 3 ^ 40 * 1303896 * 2
def baseEnd_1303896 : Nat := 297566831766638104268221

theorem tailTrace_1303896 : CollatzResearch.WordTrace tailWord_1303896 prefixEnd_1303896 297566831766638104268221 := by
  unfold tailWord_1303896
  simp only [CollatzResearch.WordTrace]
  refine ⟨23778497042107477276417771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31704662722809969701890361 23778497042107477276417771)
  ·
    refine ⟨35667745563161215914626657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23778497042107477276417771 35667745563161215914626657)
    ·
      refine ⟨26750809172370911935969993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35667745563161215914626657 26750809172370911935969993)
      ·
        refine ⟨20063106879278183951977495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26750809172370911935969993 20063106879278183951977495)
        ·
          refine ⟨30094660318917275927966243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20063106879278183951977495 30094660318917275927966243)
          ·
            refine ⟨45141990478375913891949365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30094660318917275927966243 45141990478375913891949365)
            ·
              refine ⟨4232061607347741927370253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45141990478375913891949365 4232061607347741927370253)
              ·
                refine ⟨1587023102755403222763845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232061607347741927370253 1587023102755403222763845)
                ·
                  refine ⟨297566831766638104268221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587023102755403222763845 297566831766638104268221)
                  ·
                    rfl

theorem cell21_1303896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_1303896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303896 prefixEnd_1303896 := by exact prefixLift 1303896
  have htrace : WordTrace (prefixWord ++ tailWord_1303896) baseStart_1303896 baseEnd_1303896 := by
    simpa [prefixWord, tailWord_1303896, baseEnd_1303896] using wordTrace_append hprefix tailTrace_1303896
  have hstable : (prefixWord ++ tailWord_1303896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303896).length < 2 ^ (prefixWord ++ tailWord_1303896).sum := by decide
  have hdescent : baseEnd_1303896 < baseStart_1303896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303975 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 3]
def baseStart_1303975 : Nat := 118140960795 + 1303975 * 2 ^ 59
def prefixEnd_1303975 : Nat := 4983230072969 + 3 ^ 40 * 1303975 * 2
def baseEnd_1303975 : Nat := 297584860642951522451393

theorem tailTrace_1303975 : CollatzResearch.WordTrace tailWord_1303975 prefixEnd_1303975 297584860642951522451393 := by
  unfold tailWord_1303975
  simp only [CollatzResearch.WordTrace]
  refine ⟨47559875450928751044961379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31706583633952500696640919 47559875450928751044961379)
  ·
    refine ⟨71339813176393126567442069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47559875450928751044961379 71339813176393126567442069)
    ·
      refine ⟨3344053742643427807848847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71339813176393126567442069 3344053742643427807848847)
      ·
        refine ⟨5016080613965141711773271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344053742643427807848847 5016080613965141711773271)
        ·
          refine ⟨7524120920947712567659907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016080613965141711773271 7524120920947712567659907)
          ·
            refine ⟨11286181381421568851489861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524120920947712567659907 11286181381421568851489861)
            ·
              refine ⟨2116159009016544159654349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11286181381421568851489861 2116159009016544159654349)
              ·
                refine ⟨793559628381204059870381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2116159009016544159654349 793559628381204059870381)
                ·
                  refine ⟨297584860642951522451393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793559628381204059870381 297584860642951522451393)
                  ·
                    rfl

theorem cell21_1303975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 3].length) (baseStart_1303975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303975 prefixEnd_1303975 := by exact prefixLift 1303975
  have htrace : WordTrace (prefixWord ++ tailWord_1303975) baseStart_1303975 baseEnd_1303975 := by
    simpa [prefixWord, tailWord_1303975, baseEnd_1303975] using wordTrace_append hprefix tailTrace_1303975
  have hstable : (prefixWord ++ tailWord_1303975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303975).length < 2 ^ (prefixWord ++ tailWord_1303975).sum := by decide
  have hdescent : baseEnd_1303975 < baseStart_1303975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303989 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1303989 : Nat := 118140960795 + 1303989 * 2 ^ 59
def prefixEnd_1303989 : Nat := 4983230072969 + 3 ^ 40 * 1303989 * 2
def baseEnd_1303989 : Nat := 297588055633690609218031

theorem tailTrace_1303989 : CollatzResearch.WordTrace tailWord_1303989 prefixEnd_1303989 297588055633690609218031 := by
  unfold tailWord_1303989
  simp only [CollatzResearch.WordTrace]
  refine ⟨47560386072878031435971021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31706924048585354290647347 47560386072878031435971021)
  ·
    refine ⟨17835144777329261788489133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47560386072878031435971021 17835144777329261788489133)
    ·
      refine ⟨6688179291498473170683425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17835144777329261788489133 6688179291498473170683425)
      ·
        refine ⟨5016134468623854878012569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6688179291498473170683425 5016134468623854878012569)
        ·
          refine ⟨3762100851467891158509427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5016134468623854878012569 3762100851467891158509427)
          ·
            refine ⟨5643151277201836737764141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762100851467891158509427 5643151277201836737764141)
            ·
              refine ⟨2116181728950688776661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5643151277201836737764141 2116181728950688776661553)
              ·
                refine ⟨1587136296713016582496165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116181728950688776661553 1587136296713016582496165)
                ·
                  refine ⟨297588055633690609218031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587136296713016582496165 297588055633690609218031)
                  ·
                    rfl

theorem cell21_1303989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1303989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1303989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1303989 prefixEnd_1303989 := by exact prefixLift 1303989
  have htrace : WordTrace (prefixWord ++ tailWord_1303989) baseStart_1303989 baseEnd_1303989 := by
    simpa [prefixWord, tailWord_1303989, baseEnd_1303989] using wordTrace_append hprefix tailTrace_1303989
  have hstable : (prefixWord ++ tailWord_1303989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303989).length < 2 ^ (prefixWord ++ tailWord_1303989).sum := by decide
  have hdescent : baseEnd_1303989 < baseStart_1303989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304031 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_1304031 : Nat := 118140960795 + 1304031 * 2 ^ 59
def prefixEnd_1304031 : Nat := 4983230072969 + 3 ^ 40 * 1304031 * 2
def baseEnd_1304031 : Nat := 297597640605907869517945

theorem tailTrace_1304031 : CollatzResearch.WordTrace tailWord_1304031 prefixEnd_1304031 297597640605907869517945 := by
  unfold tailWord_1304031
  simp only [CollatzResearch.WordTrace]
  refine ⟨47561917938725872608999947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31707945292483915072666631 47561917938725872608999947)
  ·
    refine ⟨71342876908088808913499921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47561917938725872608999947 71342876908088808913499921)
    ·
      refine ⟨53507157681066606685124941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71342876908088808913499921 53507157681066606685124941)
      ·
        refine ⟨20065184130399977506921853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53507157681066606685124941 20065184130399977506921853)
        ·
          refine ⟨7524444048899991565095695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20065184130399977506921853 7524444048899991565095695)
          ·
            refine ⟨11286666073349987347643543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524444048899991565095695 11286666073349987347643543)
            ·
              refine ⟨16929999110024981021465315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286666073349987347643543 16929999110024981021465315)
              ·
                refine ⟨25394998665037471532197973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16929999110024981021465315 25394998665037471532197973)
                ·
                  refine ⟨297597640605907869517945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25394998665037471532197973 297597640605907869517945)
                  ·
                    rfl

theorem cell21_1304031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_1304031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304031 prefixEnd_1304031 := by exact prefixLift 1304031
  have htrace : WordTrace (prefixWord ++ tailWord_1304031) baseStart_1304031 baseEnd_1304031 := by
    simpa [prefixWord, tailWord_1304031, baseEnd_1304031] using wordTrace_append hprefix tailTrace_1304031
  have hstable : (prefixWord ++ tailWord_1304031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304031).length < 2 ^ (prefixWord ++ tailWord_1304031).sum := by decide
  have hdescent : baseEnd_1304031 < baseStart_1304031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304065 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_1304065 : Nat := 118140960795 + 1304065 * 2 ^ 59
def prefixEnd_1304065 : Nat := 4983230072969 + 3 ^ 40 * 1304065 * 2
def baseEnd_1304065 : Nat := 297605399869131365951209

theorem tailTrace_1304065 : CollatzResearch.WordTrace tailWord_1304065 prefixEnd_1304065 297605399869131365951209 := by
  unfold tailWord_1304065
  simp only [CollatzResearch.WordTrace]
  refine ⟨47563158020602696415737649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31708772013735130943825099 47563158020602696415737649)
  ·
    refine ⟨35672368515452022311803237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47563158020602696415737649 35672368515452022311803237)
    ·
      refine ⟨6688569096647254183463107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35672368515452022311803237 6688569096647254183463107)
      ·
        refine ⟨10032853644970881275194661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6688569096647254183463107 10032853644970881275194661)
        ·
          refine ⟨1881160058432040239098999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10032853644970881275194661 1881160058432040239098999)
          ·
            refine ⟨2821740087648060358648499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881160058432040239098999 2821740087648060358648499)
            ·
              refine ⟨4232610131472090537972749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821740087648060358648499 4232610131472090537972749)
              ·
                refine ⟨1587228799302033951739781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232610131472090537972749 1587228799302033951739781)
                ·
                  refine ⟨297605399869131365951209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587228799302033951739781 297605399869131365951209)
                  ·
                    rfl

theorem cell21_1304065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_1304065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304065 prefixEnd_1304065 := by exact prefixLift 1304065
  have htrace : WordTrace (prefixWord ++ tailWord_1304065) baseStart_1304065 baseEnd_1304065 := by
    simpa [prefixWord, tailWord_1304065, baseEnd_1304065] using wordTrace_append hprefix tailTrace_1304065
  have hstable : (prefixWord ++ tailWord_1304065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304065).length < 2 ^ (prefixWord ++ tailWord_1304065).sum := by decide
  have hdescent : baseEnd_1304065 < baseStart_1304065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304152 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_1304152 : Nat := 118140960795 + 1304152 * 2 ^ 59
def prefixEnd_1304152 : Nat := 4983230072969 + 3 ^ 40 * 1304152 * 2
def baseEnd_1304152 : Nat := 297625254454438548001031

theorem tailTrace_1304152 : CollatzResearch.WordTrace tailWord_1304152 prefixEnd_1304152 297625254454438548001031 := by
  unfold tailWord_1304152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23783165585643755137077355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31710887447525006849436473 23783165585643755137077355)
  ·
    refine ⟨35674748378465632705616033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23783165585643755137077355 35674748378465632705616033)
    ·
      refine ⟨26756061283849224529212025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35674748378465632705616033 26756061283849224529212025)
      ·
        refine ⟨20067045962886918396909019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26756061283849224529212025 20067045962886918396909019)
        ·
          refine ⟨30100568944330377595363529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20067045962886918396909019 30100568944330377595363529)
          ·
            refine ⟨22575426708247783196522647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30100568944330377595363529 22575426708247783196522647)
            ·
              refine ⟨33863140062371674794783971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22575426708247783196522647 33863140062371674794783971)
              ·
                refine ⟨50794710093557512192175957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33863140062371674794783971 50794710093557512192175957)
                ·
                  refine ⟨297625254454438548001031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50794710093557512192175957 297625254454438548001031)
                  ·
                    rfl

theorem cell21_1304152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_1304152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304152 prefixEnd_1304152 := by exact prefixLift 1304152
  have htrace : WordTrace (prefixWord ++ tailWord_1304152) baseStart_1304152 baseEnd_1304152 := by
    simpa [prefixWord, tailWord_1304152, baseEnd_1304152] using wordTrace_append hprefix tailTrace_1304152
  have hstable : (prefixWord ++ tailWord_1304152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304152).length < 2 ^ (prefixWord ++ tailWord_1304152).sum := by decide
  have hdescent : baseEnd_1304152 < baseStart_1304152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304220 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1304220 : Nat := 118140960795 + 1304220 * 2 ^ 59
def prefixEnd_1304220 : Nat := 4983230072969 + 3 ^ 40 * 1304220 * 2
def baseEnd_1304220 : Nat := 297640772980885540867559

theorem tailTrace_1304220 : CollatzResearch.WordTrace tailWord_1304220 prefixEnd_1304220 297640772980885540867559 := by
  unfold tailWord_1304220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23784405667520578943815057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31712540890027438591753409 23784405667520578943815057)
  ·
    refine ⟨17838304250640434207861293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23784405667520578943815057 17838304250640434207861293)
    ·
      refine ⟨6689364093990162827947985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17838304250640434207861293 6689364093990162827947985)
      ·
        refine ⟨5017023070492622120960989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6689364093990162827947985 5017023070492622120960989)
        ·
          refine ⟨1881383651434733295360371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5017023070492622120960989 1881383651434733295360371)
          ·
            refine ⟨2822075477152099943040557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881383651434733295360371 2822075477152099943040557)
            ·
              refine ⟨1058278303932037478640209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2822075477152099943040557 1058278303932037478640209)
              ·
                refine ⟨793708727949028108980157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058278303932037478640209 793708727949028108980157)
                ·
                  refine ⟨297640772980885540867559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793708727949028108980157 297640772980885540867559)
                  ·
                    rfl

theorem cell21_1304220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1304220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304220 prefixEnd_1304220 := by exact prefixLift 1304220
  have htrace : WordTrace (prefixWord ++ tailWord_1304220) baseStart_1304220 baseEnd_1304220 := by
    simpa [prefixWord, tailWord_1304220, baseEnd_1304220] using wordTrace_append hprefix tailTrace_1304220
  have hstable : (prefixWord ++ tailWord_1304220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304220).length < 2 ^ (prefixWord ++ tailWord_1304220).sum := by decide
  have hdescent : baseEnd_1304220 < baseStart_1304220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304273 : List Nat := [1, 2, 2, 1, 2, 13]
def baseStart_1304273 : Nat := 118140960795 + 1304273 * 2 ^ 59
def prefixEnd_1304273 : Nat := 4983230072969 + 3 ^ 40 * 1304273 * 2
def baseEnd_1304273 : Nat := 11024180307517378758671

theorem tailTrace_1304273 : CollatzResearch.WordTrace tailWord_1304273 prefixEnd_1304273 11024180307517378758671 := by
  unfold tailWord_1304273
  simp only [CollatzResearch.WordTrace]
  refine ⟨47570744403849147939309473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31713829602566098626206315 47570744403849147939309473)
  ·
    refine ⟨35678058302886860954482105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47570744403849147939309473 35678058302886860954482105)
    ·
      refine ⟨26758543727165145715861579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35678058302886860954482105 26758543727165145715861579)
      ·
        refine ⟨40137815590747718573792369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26758543727165145715861579 40137815590747718573792369)
        ·
          refine ⟨30103361693060788930344277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40137815590747718573792369 30103361693060788930344277)
          ·
            refine ⟨11024180307517378758671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 30103361693060788930344277 11024180307517378758671)
            ·
              rfl

theorem cell21_1304273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 13].length) (baseStart_1304273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304273 prefixEnd_1304273 := by exact prefixLift 1304273
  have htrace : WordTrace (prefixWord ++ tailWord_1304273) baseStart_1304273 baseEnd_1304273 := by
    simpa [prefixWord, tailWord_1304273, baseEnd_1304273] using wordTrace_append hprefix tailTrace_1304273
  have hstable : (prefixWord ++ tailWord_1304273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304273).length < 2 ^ (prefixWord ++ tailWord_1304273).sum := by decide
  have hdescent : baseEnd_1304273 < baseStart_1304273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304335 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_1304335 : Nat := 118140960795 + 1304335 * 2 ^ 59
def prefixEnd_1304335 : Nat := 4983230072969 + 3 ^ 40 * 1304335 * 2
def baseEnd_1304335 : Nat := 297667017547670896450657

theorem tailTrace_1304335 : CollatzResearch.WordTrace tailWord_1304335 prefixEnd_1304335 297667017547670896450657 := by
  unfold tailWord_1304335
  simp only [CollatzResearch.WordTrace]
  refine ⟨47573005729624532528066459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31715337153083021685377639 47573005729624532528066459)
  ·
    refine ⟨71359508594436798792099689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47573005729624532528066459 71359508594436798792099689)
    ·
      refine ⟨53519631445827599094074767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71359508594436798792099689 53519631445827599094074767)
      ·
        refine ⟨80279447168741398641112151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53519631445827599094074767 80279447168741398641112151)
        ·
          refine ⟨120419170753112097961668227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80279447168741398641112151 120419170753112097961668227)
          ·
            refine ⟨180628756129668146942502341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120419170753112097961668227 180628756129668146942502341)
            ·
              refine ⟨33867891774312777551719189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180628756129668146942502341 33867891774312777551719189)
              ·
                refine ⟨1587557426920911447736837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33867891774312777551719189 1587557426920911447736837)
                ·
                  refine ⟨297667017547670896450657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587557426920911447736837 297667017547670896450657)
                  ·
                    rfl

theorem cell21_1304335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_1304335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304335 prefixEnd_1304335 := by exact prefixLift 1304335
  have htrace : WordTrace (prefixWord ++ tailWord_1304335) baseStart_1304335 baseEnd_1304335 := by
    simpa [prefixWord, tailWord_1304335, baseEnd_1304335] using wordTrace_append hprefix tailTrace_1304335
  have hstable : (prefixWord ++ tailWord_1304335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304335).length < 2 ^ (prefixWord ++ tailWord_1304335).sum := by decide
  have hdescent : baseEnd_1304335 < baseStart_1304335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304338 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1304338 : Nat := 118140960795 + 1304338 * 2 ^ 59
def prefixEnd_1304338 : Nat := 4983230072969 + 3 ^ 40 * 1304338 * 2
def baseEnd_1304338 : Nat := 297667702188543557900651

theorem tailTrace_1304338 : CollatzResearch.WordTrace tailWord_1304338 prefixEnd_1304338 297667702188543557900651 := by
  unfold tailWord_1304338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11893278787153416010106417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31715410099075776026950445 11893278787153416010106417)
  ·
    refine ⟨8919959090365062007579813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11893278787153416010106417 8919959090365062007579813)
    ·
      refine ⟨1672492329443449126421215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8919959090365062007579813 1672492329443449126421215)
      ·
        refine ⟨2508738494165173689631823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672492329443449126421215 2508738494165173689631823)
        ·
          refine ⟨3763107741247760534447735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508738494165173689631823 3763107741247760534447735)
          ·
            refine ⟨5644661611871640801671603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763107741247760534447735 5644661611871640801671603)
            ·
              refine ⟨8466992417807461202507405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644661611871640801671603 8466992417807461202507405)
              ·
                refine ⟨3175122156677797950940277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8466992417807461202507405 3175122156677797950940277)
                ·
                  refine ⟨297667702188543557900651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3175122156677797950940277 297667702188543557900651)
                  ·
                    rfl

theorem cell21_1304338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1304338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304338 prefixEnd_1304338 := by exact prefixLift 1304338
  have htrace : WordTrace (prefixWord ++ tailWord_1304338) baseStart_1304338 baseEnd_1304338 := by
    simpa [prefixWord, tailWord_1304338, baseEnd_1304338] using wordTrace_append hprefix tailTrace_1304338
  have hstable : (prefixWord ++ tailWord_1304338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304338).length < 2 ^ (prefixWord ++ tailWord_1304338).sum := by decide
  have hdescent : baseEnd_1304338 < baseStart_1304338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304372 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1304372 : Nat := 118140960795 + 1304372 * 2 ^ 59
def prefixEnd_1304372 : Nat := 4983230072969 + 3 ^ 40 * 1304372 * 2
def baseEnd_1304372 : Nat := 297675461451767054333915

theorem tailTrace_1304372 : CollatzResearch.WordTrace tailWord_1304372 prefixEnd_1304372 297675461451767054333915 := by
  unfold tailWord_1304372
  simp only [CollatzResearch.WordTrace]
  refine ⟨23787177615245243923581685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31716236820326991898108913 23787177615245243923581685)
  ·
    refine ⟨2230047901429241617835783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23787177615245243923581685 2230047901429241617835783)
    ·
      refine ⟨3345071852143862426753675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230047901429241617835783 3345071852143862426753675)
      ·
        refine ⟨5017607778215793640130513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345071852143862426753675 5017607778215793640130513)
        ·
          refine ⟨3763205833661845230097885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5017607778215793640130513 3763205833661845230097885)
          ·
            refine ⟨1411202187623191961286707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3763205833661845230097885 1411202187623191961286707)
            ·
              refine ⟨2116803281434787941930061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411202187623191961286707 2116803281434787941930061)
              ·
                refine ⟨793801230538045478223773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2116803281434787941930061 793801230538045478223773)
                ·
                  refine ⟨297675461451767054333915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 793801230538045478223773 297675461451767054333915)
                  ·
                    rfl

theorem cell21_1304372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1304372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304372 prefixEnd_1304372 := by exact prefixLift 1304372
  have htrace : WordTrace (prefixWord ++ tailWord_1304372) baseStart_1304372 baseEnd_1304372 := by
    simpa [prefixWord, tailWord_1304372, baseEnd_1304372] using wordTrace_append hprefix tailTrace_1304372
  have hstable : (prefixWord ++ tailWord_1304372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304372).length < 2 ^ (prefixWord ++ tailWord_1304372).sum := by decide
  have hdescent : baseEnd_1304372 < baseStart_1304372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304380 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1304380 : Nat := 118140960795 + 1304380 * 2 ^ 59
def prefixEnd_1304380 : Nat := 4983230072969 + 3 ^ 40 * 1304380 * 2
def baseEnd_1304380 : Nat := 297677287160760818200565

theorem tailTrace_1304380 : CollatzResearch.WordTrace tailWord_1304380 prefixEnd_1304380 297677287160760818200565 := by
  unfold tailWord_1304380
  simp only [CollatzResearch.WordTrace]
  refine ⟨23787323507230752606727297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31716431342974336808969729 23787323507230752606727297)
  ·
    refine ⟨17840492630423064455045473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23787323507230752606727297 17840492630423064455045473)
    ·
      refine ⟨13380369472817298341284105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17840492630423064455045473 13380369472817298341284105)
      ·
        refine ⟨10035277104612973755963079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13380369472817298341284105 10035277104612973755963079)
        ·
          refine ⟨15052915656919460633944619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10035277104612973755963079 15052915656919460633944619)
          ·
            refine ⟨22579373485379190950916929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15052915656919460633944619 22579373485379190950916929)
            ·
              refine ⟨16934530114034393213187697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22579373485379190950916929 16934530114034393213187697)
              ·
                refine ⟨12700897585525794909890773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16934530114034393213187697 12700897585525794909890773)
                ·
                  refine ⟨297677287160760818200565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12700897585525794909890773 297677287160760818200565)
                  ·
                    rfl

theorem cell21_1304380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1304380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304380 prefixEnd_1304380 := by exact prefixLift 1304380
  have htrace : WordTrace (prefixWord ++ tailWord_1304380) baseStart_1304380 baseEnd_1304380 := by
    simpa [prefixWord, tailWord_1304380, baseEnd_1304380] using wordTrace_append hprefix tailTrace_1304380
  have hstable : (prefixWord ++ tailWord_1304380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304380).length < 2 ^ (prefixWord ++ tailWord_1304380).sum := by decide
  have hdescent : baseEnd_1304380 < baseStart_1304380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304383 : List Nat := [1, 1, 2, 2, 7, 1, 7]
def baseStart_1304383 : Nat := 118140960795 + 1304383 * 2 ^ 59
def prefixEnd_1304383 : Nat := 4983230072969 + 3 ^ 40 * 1304383 * 2
def baseEnd_1304383 : Nat := 33075330200181497738951

theorem tailTrace_1304383 : CollatzResearch.WordTrace tailWord_1304383 prefixEnd_1304383 33075330200181497738951 := by
  unfold tailWord_1304383
  simp only [CollatzResearch.WordTrace]
  refine ⟨47574756433450636725813803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31716504288967091150542535 47574756433450636725813803)
  ·
    refine ⟨71362134650175955088720705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47574756433450636725813803 71362134650175955088720705)
    ·
      refine ⟨53521600987631966316540529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71362134650175955088720705 53521600987631966316540529)
      ·
        refine ⟨40141200740723974737405397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53521600987631966316540529 40141200740723974737405397)
        ·
          refine ⟨940809392360718157907939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 40141200740723974737405397 940809392360718157907939)
          ·
            refine ⟨1411214088541077236861909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940809392360718157907939 1411214088541077236861909)
            ·
              refine ⟨33075330200181497738951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1411214088541077236861909 33075330200181497738951)
              ·
                rfl

theorem cell21_1304383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 7].length) (baseStart_1304383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304383 prefixEnd_1304383 := by exact prefixLift 1304383
  have htrace : WordTrace (prefixWord ++ tailWord_1304383) baseStart_1304383 baseEnd_1304383 := by
    simpa [prefixWord, tailWord_1304383, baseEnd_1304383] using wordTrace_append hprefix tailTrace_1304383
  have hstable : (prefixWord ++ tailWord_1304383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304383).length < 2 ^ (prefixWord ++ tailWord_1304383).sum := by decide
  have hdescent : baseEnd_1304383 < baseStart_1304383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304628 : List Nat := [2, 5, 1, 2, 2, 2, 1, 6]
def baseStart_1304628 : Nat := 118140960795 + 1304628 * 2 ^ 59
def prefixEnd_1304628 : Nat := 4983230072969 + 3 ^ 40 * 1304628 * 2
def baseEnd_1304628 : Nat := 99244628046522499355575

theorem tailTrace_1304628 : CollatzResearch.WordTrace tailWord_1304628 prefixEnd_1304628 99244628046522499355575 := by
  unfold tailWord_1304628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23791846158781521784241269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31722461545042029045655025 23791846158781521784241269)
  ·
    refine ⟨2230485577385767667272619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23791846158781521784241269 2230485577385767667272619)
    ·
      refine ⟨3345728366078651500908929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230485577385767667272619 3345728366078651500908929)
      ·
        refine ⟨2509296274558988625681697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3345728366078651500908929 2509296274558988625681697)
        ·
          refine ⟨1881972205919241469261273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509296274558988625681697 1881972205919241469261273)
          ·
            refine ⟨1411479154439431101945955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1881972205919241469261273 1411479154439431101945955)
            ·
              refine ⟨2117218731659146652918933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411479154439431101945955 2117218731659146652918933)
              ·
                refine ⟨99244628046522499355575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2117218731659146652918933 99244628046522499355575)
                ·
                  rfl

theorem cell21_1304628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_1304628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304628 prefixEnd_1304628 := by exact prefixLift 1304628
  have htrace : WordTrace (prefixWord ++ tailWord_1304628) baseStart_1304628 baseEnd_1304628 := by
    simpa [prefixWord, tailWord_1304628, baseEnd_1304628] using wordTrace_append hprefix tailTrace_1304628
  have hstable : (prefixWord ++ tailWord_1304628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304628).length < 2 ^ (prefixWord ++ tailWord_1304628).sum := by decide
  have hdescent : baseEnd_1304628 < baseStart_1304628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304639 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_1304639 : Nat := 118140960795 + 1304639 * 2 ^ 59
def prefixEnd_1304639 : Nat := 4983230072969 + 3 ^ 40 * 1304639 * 2
def baseEnd_1304639 : Nat := 297736394489433923383369

theorem tailTrace_1304639 : CollatzResearch.WordTrace tailWord_1304639 prefixEnd_1304639 297736394489433923383369 := by
  unfold tailWord_1304639
  simp only [CollatzResearch.WordTrace]
  refine ⟨47584093520523192447132971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31722729013682128298088647 47584093520523192447132971)
  ·
    refine ⟨71376140280784788670699457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47584093520523192447132971 71376140280784788670699457)
    ·
      refine ⟨53532105210588591503024593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71376140280784788670699457 53532105210588591503024593)
      ·
        refine ⟨40149078907941443627268445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53532105210588591503024593 40149078907941443627268445)
        ·
          refine ⟨15055904590478041360225667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40149078907941443627268445 15055904590478041360225667)
          ·
            refine ⟨22583856885717062040338501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15055904590478041360225667 22583856885717062040338501)
            ·
              refine ⟨4234473166071949132563469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22583856885717062040338501 4234473166071949132563469)
              ·
                refine ⟨1587927437276980924711301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4234473166071949132563469 1587927437276980924711301)
                ·
                  refine ⟨297736394489433923383369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587927437276980924711301 297736394489433923383369)
                  ·
                    rfl

theorem cell21_1304639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_1304639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304639 prefixEnd_1304639 := by exact prefixLift 1304639
  have htrace : WordTrace (prefixWord ++ tailWord_1304639) baseStart_1304639 baseEnd_1304639 := by
    simpa [prefixWord, tailWord_1304639, baseEnd_1304639] using wordTrace_append hprefix tailTrace_1304639
  have hstable : (prefixWord ++ tailWord_1304639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304639).length < 2 ^ (prefixWord ++ tailWord_1304639).sum := by decide
  have hdescent : baseEnd_1304639 < baseStart_1304639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304684 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1304684 : Nat := 118140960795 + 1304684 * 2 ^ 59
def prefixEnd_1304684 : Nat := 4983230072969 + 3 ^ 40 * 1304684 * 2
def baseEnd_1304684 : Nat := 297746664102523845133277

theorem tailTrace_1304684 : CollatzResearch.WordTrace tailWord_1304684 prefixEnd_1304684 297746664102523845133277 := by
  unfold tailWord_1304684
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792867402680082566260553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31723823203573443421680737 23792867402680082566260553)
  ·
    refine ⟨17844650552010061924695415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23792867402680082566260553 17844650552010061924695415)
    ·
      refine ⟨26766975828015092887043123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17844650552010061924695415 26766975828015092887043123)
      ·
        refine ⟨40150463742022639330564685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26766975828015092887043123 40150463742022639330564685)
        ·
          refine ⟨15056423903258489748961757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40150463742022639330564685 15056423903258489748961757)
          ·
            refine ⟨5646158963721933655860659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15056423903258489748961757 5646158963721933655860659)
            ·
              refine ⟨8469238445582900483790989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646158963721933655860659 8469238445582900483790989)
              ·
                refine ⟨3175964417093587681421621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8469238445582900483790989 3175964417093587681421621)
                ·
                  refine ⟨297746664102523845133277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3175964417093587681421621 297746664102523845133277)
                  ·
                    rfl

theorem cell21_1304684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1304684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304684 prefixEnd_1304684 := by exact prefixLift 1304684
  have htrace : WordTrace (prefixWord ++ tailWord_1304684) baseStart_1304684 baseEnd_1304684 := by
    simpa [prefixWord, tailWord_1304684, baseEnd_1304684] using wordTrace_append hprefix tailTrace_1304684
  have hstable : (prefixWord ++ tailWord_1304684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304684).length < 2 ^ (prefixWord ++ tailWord_1304684).sum := by decide
  have hdescent : baseEnd_1304684 < baseStart_1304684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304735 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 3]
def baseStart_1304735 : Nat := 118140960795 + 1304735 * 2 ^ 59
def prefixEnd_1304735 : Nat := 4983230072969 + 3 ^ 40 * 1304735 * 2
def baseEnd_1304735 : Nat := 297758302997359089783173

theorem tailTrace_1304735 : CollatzResearch.WordTrace tailWord_1304735 prefixEnd_1304735 297758302997359089783173 := by
  unfold tailWord_1304735
  simp only [CollatzResearch.WordTrace]
  refine ⟨47587594928175400842627659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31725063285450267228418439 47587594928175400842627659)
  ·
    refine ⟨71381392392263101263941489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47587594928175400842627659 71381392392263101263941489)
    ·
      refine ⟨53536044294197325947956117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71381392392263101263941489 53536044294197325947956117)
      ·
        refine ⟨2509502076290499653810443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53536044294197325947956117 2509502076290499653810443)
        ·
          refine ⟨3764253114435749480715665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509502076290499653810443 3764253114435749480715665)
          ·
            refine ⟨2823189835826812110536749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764253114435749480715665 2823189835826812110536749)
            ·
              refine ⟨1058696188435054541451281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2823189835826812110536749 1058696188435054541451281)
              ·
                refine ⟨794022141326290906088461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058696188435054541451281 794022141326290906088461)
                ·
                  refine ⟨297758302997359089783173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794022141326290906088461 297758302997359089783173)
                  ·
                    rfl

theorem cell21_1304735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 3].length) (baseStart_1304735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304735 prefixEnd_1304735 := by exact prefixLift 1304735
  have htrace : WordTrace (prefixWord ++ tailWord_1304735) baseStart_1304735 baseEnd_1304735 := by
    simpa [prefixWord, tailWord_1304735, baseEnd_1304735] using wordTrace_append hprefix tailTrace_1304735
  have hstable : (prefixWord ++ tailWord_1304735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304735).length < 2 ^ (prefixWord ++ tailWord_1304735).sum := by decide
  have hdescent : baseEnd_1304735 < baseStart_1304735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304749 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1304749 : Nat := 118140960795 + 1304749 * 2 ^ 59
def prefixEnd_1304749 : Nat := 4983230072969 + 3 ^ 40 * 1304749 * 2
def baseEnd_1304749 : Nat := 297761497988098176549811

theorem tailTrace_1304749 : CollatzResearch.WordTrace tailWord_1304749 prefixEnd_1304749 297761497988098176549811 := by
  unfold tailWord_1304749
  simp only [CollatzResearch.WordTrace]
  refine ⟨47588105550124681233637301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31725403700083120822424867 47588105550124681233637301)
  ·
    refine ⟨4461384895324188865653497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47588105550124681233637301 4461384895324188865653497)
    ·
      refine ⟨3346038671493141649240123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4461384895324188865653497 3346038671493141649240123)
      ·
        refine ⟨5019058007239712473860185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346038671493141649240123 5019058007239712473860185)
        ·
          refine ⟨3764293505429784355395139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019058007239712473860185 3764293505429784355395139)
          ·
            refine ⟨5646440258144676533092709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764293505429784355395139 5646440258144676533092709)
            ·
              refine ⟨1058707548402126849954883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5646440258144676533092709 1058707548402126849954883)
              ·
                refine ⟨1588061322603190274932325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058707548402126849954883 1588061322603190274932325)
                ·
                  refine ⟨297761497988098176549811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1588061322603190274932325 297761497988098176549811)
                  ·
                    rfl

theorem cell21_1304749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1304749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304749 prefixEnd_1304749 := by exact prefixLift 1304749
  have htrace : WordTrace (prefixWord ++ tailWord_1304749) baseStart_1304749 baseEnd_1304749 := by
    simpa [prefixWord, tailWord_1304749, baseEnd_1304749] using wordTrace_append hprefix tailTrace_1304749
  have hstable : (prefixWord ++ tailWord_1304749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304749).length < 2 ^ (prefixWord ++ tailWord_1304749).sum := by decide
  have hdescent : baseEnd_1304749 < baseStart_1304749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304794 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_1304794 : Nat := 118140960795 + 1304794 * 2 ^ 59
def prefixEnd_1304794 : Nat := 4983230072969 + 3 ^ 40 * 1304794 * 2
def baseEnd_1304794 : Nat := 297771767601188098299719

theorem tailTrace_1304794 : CollatzResearch.WordTrace tailWord_1304794 prefixEnd_1304794 297771767601188098299719 := by
  unfold tailWord_1304794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897436708740413479756359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31726497889974435946016957 11897436708740413479756359)
  ·
    refine ⟨17846155063110620219634539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11897436708740413479756359 17846155063110620219634539)
    ·
      refine ⟨26769232594665930329451809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17846155063110620219634539 26769232594665930329451809)
      ·
        refine ⟨20076924445999447747088857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26769232594665930329451809 20076924445999447747088857)
        ·
          refine ⟨15057693334499585810316643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20076924445999447747088857 15057693334499585810316643)
          ·
            refine ⟨22586540001749378715474965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15057693334499585810316643 22586540001749378715474965)
            ·
              refine ⟨1058744062582002127287889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22586540001749378715474965 1058744062582002127287889)
              ·
                refine ⟨794058046936501595465917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058744062582002127287889 794058046936501595465917)
                ·
                  refine ⟨297771767601188098299719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794058046936501595465917 297771767601188098299719)
                  ·
                    rfl

theorem cell21_1304794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_1304794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304794 prefixEnd_1304794 := by exact prefixLift 1304794
  have htrace : WordTrace (prefixWord ++ tailWord_1304794) baseStart_1304794 baseEnd_1304794 := by
    simpa [prefixWord, tailWord_1304794, baseEnd_1304794] using wordTrace_append hprefix tailTrace_1304794
  have hstable : (prefixWord ++ tailWord_1304794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304794).length < 2 ^ (prefixWord ++ tailWord_1304794).sum := by decide
  have hdescent : baseEnd_1304794 < baseStart_1304794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304853 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 3]
def baseStart_1304853 : Nat := 118140960795 + 1304853 * 2 ^ 59
def prefixEnd_1304853 : Nat := 4983230072969 + 3 ^ 40 * 1304853 * 2
def baseEnd_1304853 : Nat := 297785232205017106816265

theorem tailTrace_1304853 : CollatzResearch.WordTrace tailWord_1304853 prefixEnd_1304853 297785232205017106816265 := by
  unfold tailWord_1304853
  simp only [CollatzResearch.WordTrace]
  refine ⟨47591898741747906995423213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31727932494498604663615475 47591898741747906995423213)
  ·
    refine ⟨17846962028155465123283705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47591898741747906995423213 17846962028155465123283705)
    ·
      refine ⟨13385221521116598842462779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17846962028155465123283705 13385221521116598842462779)
      ·
        refine ⟨20077832281674898263694169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13385221521116598842462779 20077832281674898263694169)
        ·
          refine ⟨15058374211256173697770627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20077832281674898263694169 15058374211256173697770627)
          ·
            refine ⟨22587561316884260546655941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058374211256173697770627 22587561316884260546655941)
            ·
              refine ⟨4235167746915798852497989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22587561316884260546655941 4235167746915798852497989)
              ·
                refine ⟨794093952546712284843373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4235167746915798852497989 794093952546712284843373)
                ·
                  refine ⟨297785232205017106816265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794093952546712284843373 297785232205017106816265)
                  ·
                    rfl

theorem cell21_1304853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_1304853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304853 prefixEnd_1304853 := by exact prefixLift 1304853
  have htrace : WordTrace (prefixWord ++ tailWord_1304853) baseStart_1304853 baseEnd_1304853 := by
    simpa [prefixWord, tailWord_1304853, baseEnd_1304853] using wordTrace_append hprefix tailTrace_1304853
  have hstable : (prefixWord ++ tailWord_1304853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304853).length < 2 ^ (prefixWord ++ tailWord_1304853).sum := by decide
  have hdescent : baseEnd_1304853 < baseStart_1304853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304912 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_1304912 : Nat := 118140960795 + 1304912 * 2 ^ 59
def prefixEnd_1304912 : Nat := 4983230072969 + 3 ^ 40 * 1304912 * 2
def baseEnd_1304912 : Nat := 297798696808846115332811

theorem tailTrace_1304912 : CollatzResearch.WordTrace tailWord_1304912 prefixEnd_1304912 297798696808846115332811 := by
  unfold tailWord_1304912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23797025324267080035910495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31729367099022773381213993 23797025324267080035910495)
  ·
    refine ⟨35695537986400620053865743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23797025324267080035910495 35695537986400620053865743)
    ·
      refine ⟨53543306979600930080798615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35695537986400620053865743 53543306979600930080798615)
      ·
        refine ⟨80314960469401395121197923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53543306979600930080798615 80314960469401395121197923)
        ·
          refine ⟨120472440704102092681796885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80314960469401395121197923 120472440704102092681796885)
          ·
            refine ⟨5647145658004785594459229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120472440704102092681796885 5647145658004785594459229)
            ·
              refine ⟨2117679621751794597922211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5647145658004785594459229 2117679621751794597922211)
              ·
                refine ⟨3176519432627691896883317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117679621751794597922211 3176519432627691896883317)
                ·
                  refine ⟨297798696808846115332811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3176519432627691896883317 297798696808846115332811)
                  ·
                    rfl

theorem cell21_1304912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_1304912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304912 prefixEnd_1304912 := by exact prefixLift 1304912
  have htrace : WordTrace (prefixWord ++ tailWord_1304912) baseStart_1304912 baseEnd_1304912 := by
    simpa [prefixWord, tailWord_1304912, baseEnd_1304912] using wordTrace_append hprefix tailTrace_1304912
  have hstable : (prefixWord ++ tailWord_1304912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304912).length < 2 ^ (prefixWord ++ tailWord_1304912).sum := by decide
  have hdescent : baseEnd_1304912 < baseStart_1304912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304963 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 3]
def baseStart_1304963 : Nat := 118140960795 + 1304963 * 2 ^ 59
def prefixEnd_1304963 : Nat := 4983230072969 + 3 ^ 40 * 1304963 * 2
def baseEnd_1304963 : Nat := 297810335703681359982707

theorem tailTrace_1304963 : CollatzResearch.WordTrace tailWord_1304963 prefixEnd_1304963 297810335703681359982707 := by
  unfold tailWord_1304963
  simp only [CollatzResearch.WordTrace]
  refine ⟨47595910771349395781927543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31730607180899597187951695 47595910771349395781927543)
  ·
    refine ⟨71393866157024093672891315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47595910771349395781927543 71393866157024093672891315)
    ·
      refine ⟨107090799235536140509336973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71393866157024093672891315 107090799235536140509336973)
      ·
        refine ⟨40159049713326052691001365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107090799235536140509336973 40159049713326052691001365)
        ·
          refine ⟨1882455455312158719890689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40159049713326052691001365 1882455455312158719890689)
          ·
            refine ⟨1411841591484119039918017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1882455455312158719890689 1411841591484119039918017)
            ·
              refine ⟨1058881193613089279938513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411841591484119039918017 1058881193613089279938513)
              ·
                refine ⟨794160895209816959953885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058881193613089279938513 794160895209816959953885)
                ·
                  refine ⟨297810335703681359982707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794160895209816959953885 297810335703681359982707)
                  ·
                    rfl

theorem cell21_1304963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 3].length) (baseStart_1304963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304963 prefixEnd_1304963 := by exact prefixLift 1304963
  have htrace : WordTrace (prefixWord ++ tailWord_1304963) baseStart_1304963 baseEnd_1304963 := by
    simpa [prefixWord, tailWord_1304963, baseEnd_1304963] using wordTrace_append hprefix tailTrace_1304963
  have hstable : (prefixWord ++ tailWord_1304963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304963).length < 2 ^ (prefixWord ++ tailWord_1304963).sum := by decide
  have hdescent : baseEnd_1304963 < baseStart_1304963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304974 : List Nat := [4, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1304974 : Nat := 118140960795 + 1304974 * 2 ^ 59
def prefixEnd_1304974 : Nat := 4983230072969 + 3 ^ 40 * 1304974 * 2
def baseEnd_1304974 : Nat := 99270948684515928433117

theorem tailTrace_1304974 : CollatzResearch.WordTrace tailWord_1304974 prefixEnd_1304974 99270948684515928433117 := by
  unfold tailWord_1304974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949538996788693082572247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31730874649539696440385317 5949538996788693082572247)
  ·
    refine ⟨8924308495183039623858371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949538996788693082572247 8924308495183039623858371)
    ·
      refine ⟨13386462742774559435787557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8924308495183039623858371 13386462742774559435787557)
      ·
        refine ⟨2509961764270229894210167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13386462742774559435787557 2509961764270229894210167)
        ·
          refine ⟨3764942646405344841315251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509961764270229894210167 3764942646405344841315251)
          ·
            refine ⟨5647413969608017261972877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764942646405344841315251 5647413969608017261972877)
            ·
              refine ⟨2117780238603006473239829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5647413969608017261972877 2117780238603006473239829)
              ·
                refine ⟨99270948684515928433117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2117780238603006473239829 99270948684515928433117)
                ·
                  rfl

theorem cell21_1304974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1304974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1304974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1304974 prefixEnd_1304974 := by exact prefixLift 1304974
  have htrace : WordTrace (prefixWord ++ tailWord_1304974) baseStart_1304974 baseEnd_1304974 := by
    simpa [prefixWord, tailWord_1304974, baseEnd_1304974] using wordTrace_append hprefix tailTrace_1304974
  have hstable : (prefixWord ++ tailWord_1304974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304974).length < 2 ^ (prefixWord ++ tailWord_1304974).sum := by decide
  have hdescent : baseEnd_1304974 < baseStart_1304974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305199 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_1305199 : Nat := 118140960795 + 1305199 * 2 ^ 59
def prefixEnd_1305199 : Nat := 4983230072969 + 3 ^ 40 * 1305199 * 2
def baseEnd_1305199 : Nat := 297864194118997394048891

theorem tailTrace_1305199 : CollatzResearch.WordTrace tailWord_1305199 prefixEnd_1305199 297864194118997394048891 := by
  unfold tailWord_1305199
  simp only [CollatzResearch.WordTrace]
  refine ⟨47604518398494408087518651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31736345598996272058345767 47604518398494408087518651)
  ·
    refine ⟨71406777597741612131277977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47604518398494408087518651 71406777597741612131277977)
    ·
      refine ⟨53555083198306209098458483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71406777597741612131277977 53555083198306209098458483)
      ·
        refine ⟨80332624797459313647687725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53555083198306209098458483 80332624797459313647687725)
        ·
          refine ⟨30124734299047242617882897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80332624797459313647687725 30124734299047242617882897)
          ·
            refine ⟨22593550724285431963412173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30124734299047242617882897 22593550724285431963412173)
            ·
              refine ⟨8472581521607036986279565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22593550724285431963412173 8472581521607036986279565)
              ·
                refine ⟨3177218070602638869854837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8472581521607036986279565 3177218070602638869854837)
                ·
                  refine ⟨297864194118997394048891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3177218070602638869854837 297864194118997394048891)
                  ·
                    rfl

theorem cell21_1305199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_1305199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305199 prefixEnd_1305199 := by exact prefixLift 1305199
  have htrace : WordTrace (prefixWord ++ tailWord_1305199) baseStart_1305199 baseEnd_1305199 := by
    simpa [prefixWord, tailWord_1305199, baseEnd_1305199] using wordTrace_append hprefix tailTrace_1305199
  have hstable : (prefixWord ++ tailWord_1305199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305199).length < 2 ^ (prefixWord ++ tailWord_1305199).sum := by decide
  have hdescent : baseEnd_1305199 < baseStart_1305199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305205 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 4]
def baseStart_1305205 : Nat := 118140960795 + 1305205 * 2 ^ 59
def prefixEnd_1305205 : Nat := 4983230072969 + 3 ^ 40 * 1305205 * 2
def baseEnd_1305205 : Nat := 297865563400742716948879

theorem tailTrace_1305205 : CollatzResearch.WordTrace tailWord_1305205 prefixEnd_1305205 297865563400742716948879 := by
  unfold tailWord_1305205
  simp only [CollatzResearch.WordTrace]
  refine ⟨47604737236472671112237069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31736491490981780741491379 47604737236472671112237069)
  ·
    refine ⟨17851776463677251667088901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47604737236472671112237069 17851776463677251667088901)
    ·
      refine ⟨3347208086939484687579169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17851776463677251667088901 3347208086939484687579169)
      ·
        refine ⟨2510406065204613515684377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3347208086939484687579169 2510406065204613515684377)
        ·
          refine ⟨1882804548903460136763283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2510406065204613515684377 1882804548903460136763283)
          ·
            refine ⟨2824206823355190205144925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882804548903460136763283 2824206823355190205144925)
            ·
              refine ⟨1059077558758196326929347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2824206823355190205144925 1059077558758196326929347)
              ·
                refine ⟨1588616338137294490394021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059077558758196326929347 1588616338137294490394021)
                ·
                  refine ⟨297865563400742716948879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1588616338137294490394021 297865563400742716948879)
                  ·
                    rfl

theorem cell21_1305205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_1305205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305205 prefixEnd_1305205 := by exact prefixLift 1305205
  have htrace : WordTrace (prefixWord ++ tailWord_1305205) baseStart_1305205 baseEnd_1305205 := by
    simpa [prefixWord, tailWord_1305205, baseEnd_1305205] using wordTrace_append hprefix tailTrace_1305205
  have hstable : (prefixWord ++ tailWord_1305205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305205).length < 2 ^ (prefixWord ++ tailWord_1305205).sum := by decide
  have hdescent : baseEnd_1305205 < baseStart_1305205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305230 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1305230 : Nat := 118140960795 + 1305230 * 2 ^ 59
def prefixEnd_1305230 : Nat := 4983230072969 + 3 ^ 40 * 1305230 * 2
def baseEnd_1305230 : Nat := 297871268741348229032161

theorem tailTrace_1305230 : CollatzResearch.WordTrace tailWord_1305230 prefixEnd_1305230 297871268741348229032161 := by
  unfold tailWord_1305230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5950706132672762547737143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31737099374254733587931429 5950706132672762547737143)
  ·
    refine ⟨8926059199009143821605715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5950706132672762547737143 8926059199009143821605715)
    ·
      refine ⟨13389088798513715732408573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8926059199009143821605715 13389088798513715732408573)
      ·
        refine ⟨5020908299442643399653215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13389088798513715732408573 5020908299442643399653215)
        ·
          refine ⟨7531362449163965099479823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020908299442643399653215 7531362449163965099479823)
          ·
            refine ⟨11297043673745947649219735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531362449163965099479823 11297043673745947649219735)
            ·
              refine ⟨16945565510618921473829603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11297043673745947649219735 16945565510618921473829603)
              ·
                refine ⟨25418348265928382210744405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16945565510618921473829603 25418348265928382210744405)
                ·
                  refine ⟨297871268741348229032161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25418348265928382210744405 297871268741348229032161)
                  ·
                    rfl

theorem cell21_1305230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1305230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305230 prefixEnd_1305230 := by exact prefixLift 1305230
  have htrace : WordTrace (prefixWord ++ tailWord_1305230) baseStart_1305230 baseEnd_1305230 := by
    simpa [prefixWord, tailWord_1305230, baseEnd_1305230] using wordTrace_append hprefix tailTrace_1305230
  have hstable : (prefixWord ++ tailWord_1305230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305230).length < 2 ^ (prefixWord ++ tailWord_1305230).sum := by decide
  have hdescent : baseEnd_1305230 < baseStart_1305230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305261 : List Nat := [1, 5, 2, 1, 1, 2, 1, 8]
def baseStart_1305261 : Nat := 118140960795 + 1305261 * 2 ^ 59
def prefixEnd_1305261 : Nat := 4983230072969 + 3 ^ 40 * 1305261 * 2
def baseEnd_1305261 : Nat := 99292781121233021338477

theorem tailTrace_1305261 : CollatzResearch.WordTrace tailWord_1305261 prefixEnd_1305261 99292781121233021338477 := by
  unfold tailWord_1305261
  simp only [CollatzResearch.WordTrace]
  refine ⟨47606779724269792676275637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31737853149513195117517091 47606779724269792676275637)
  ·
    refine ⟨4463135599150293063400841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47606779724269792676275637 4463135599150293063400841)
    ·
      refine ⟨3347351699362719797550631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4463135599150293063400841 3347351699362719797550631)
      ·
        refine ⟨5021027549044079696325947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347351699362719797550631 5021027549044079696325947)
        ·
          refine ⟨7531541323566119544488921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5021027549044079696325947 7531541323566119544488921)
          ·
            refine ⟨5648655992674589658366691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7531541323566119544488921 5648655992674589658366691)
            ·
              refine ⟨8472983989011884487550037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648655992674589658366691 8472983989011884487550037)
              ·
                refine ⟨99292781121233021338477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8472983989011884487550037 99292781121233021338477)
                ·
                  rfl

theorem cell21_1305261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_1305261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305261 prefixEnd_1305261 := by exact prefixLift 1305261
  have htrace : WordTrace (prefixWord ++ tailWord_1305261) baseStart_1305261 baseEnd_1305261 := by
    simpa [prefixWord, tailWord_1305261, baseEnd_1305261] using wordTrace_append hprefix tailTrace_1305261
  have hstable : (prefixWord ++ tailWord_1305261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305261).length < 2 ^ (prefixWord ++ tailWord_1305261).sum := by decide
  have hdescent : baseEnd_1305261 < baseStart_1305261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305402 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_1305402 : Nat := 118140960795 + 1305402 * 2 ^ 59
def prefixEnd_1305402 : Nat := 4983230072969 + 3 ^ 40 * 1305402 * 2
def baseEnd_1305402 : Nat := 297910521484714152165143

theorem tailTrace_1305402 : CollatzResearch.WordTrace tailWord_1305402 prefixEnd_1305402 297910521484714152165143 := by
  unfold tailWord_1305402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902980604189743439289615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31741281611172649171438973 11902980604189743439289615)
  ·
    refine ⟨17854470906284615158934423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11902980604189743439289615 17854470906284615158934423)
    ·
      refine ⟨26781706359426922738401635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854470906284615158934423 26781706359426922738401635)
      ·
        refine ⟨40172559539140384107602453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26781706359426922738401635 40172559539140384107602453)
        ·
          refine ⟨1883088728397205505043865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40172559539140384107602453 1883088728397205505043865)
          ·
            refine ⟨1412316546297904128782899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883088728397205505043865 1412316546297904128782899)
            ·
              refine ⟨2118474819446856193174349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412316546297904128782899 2118474819446856193174349)
              ·
                refine ⟨794428057292571072440381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2118474819446856193174349 794428057292571072440381)
                ·
                  refine ⟨297910521484714152165143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794428057292571072440381 297910521484714152165143)
                  ·
                    rfl

theorem cell21_1305402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_1305402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305402 prefixEnd_1305402 := by exact prefixLift 1305402
  have htrace : WordTrace (prefixWord ++ tailWord_1305402) baseStart_1305402 baseEnd_1305402 := by
    simpa [prefixWord, tailWord_1305402, baseEnd_1305402] using wordTrace_append hprefix tailTrace_1305402
  have hstable : (prefixWord ++ tailWord_1305402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305402).length < 2 ^ (prefixWord ++ tailWord_1305402).sum := by decide
  have hdescent : baseEnd_1305402 < baseStart_1305402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305441 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1305441 : Nat := 118140960795 + 1305441 * 2 ^ 59
def prefixEnd_1305441 : Nat := 4983230072969 + 3 ^ 40 * 1305441 * 2
def baseEnd_1305441 : Nat := 297919421816058751015063

theorem tailTrace_1305441 : CollatzResearch.WordTrace tailWord_1305441 prefixEnd_1305441 297919421816058751015063 := by
  unfold tailWord_1305441
  simp only [CollatzResearch.WordTrace]
  refine ⟨47613344863617683417828177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31742229909078455611885451 47613344863617683417828177)
  ·
    refine ⟨35710008647713262563371133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47613344863617683417828177 35710008647713262563371133)
    ·
      refine ⟨13391253242892473461264175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35710008647713262563371133 13391253242892473461264175)
      ·
        refine ⟨20086879864338710191896263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391253242892473461264175 20086879864338710191896263)
        ·
          refine ⟨30130319796508065287844395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20086879864338710191896263 30130319796508065287844395)
          ·
            refine ⟨45195479694762097931766593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130319796508065287844395 45195479694762097931766593)
            ·
              refine ⟨33896609771071573448824945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45195479694762097931766593 33896609771071573448824945)
              ·
                refine ⟨25422457328303680086618709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33896609771071573448824945 25422457328303680086618709)
                ·
                  refine ⟨297919421816058751015063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25422457328303680086618709 297919421816058751015063)
                  ·
                    rfl

theorem cell21_1305441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1305441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305441 prefixEnd_1305441 := by exact prefixLift 1305441
  have htrace : WordTrace (prefixWord ++ tailWord_1305441) baseStart_1305441 baseEnd_1305441 := by
    simpa [prefixWord, tailWord_1305441, baseEnd_1305441] using wordTrace_append hprefix tailTrace_1305441
  have hstable : (prefixWord ++ tailWord_1305441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305441).length < 2 ^ (prefixWord ++ tailWord_1305441).sum := by decide
  have hdescent : baseEnd_1305441 < baseStart_1305441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305503 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_1305503 : Nat := 118140960795 + 1305503 * 2 ^ 59
def prefixEnd_1305503 : Nat := 4983230072969 + 3 ^ 40 * 1305503 * 2
def baseEnd_1305503 : Nat := 297933571060760420981603

theorem tailTrace_1305503 : CollatzResearch.WordTrace tailWord_1305503 prefixEnd_1305503 297933571060760420981603 := by
  unfold tailWord_1305503
  simp only [CollatzResearch.WordTrace]
  refine ⟨47615606189393068006585163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31743737459595378671056775 47615606189393068006585163)
  ·
    refine ⟨71423409284089602009877745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47615606189393068006585163 71423409284089602009877745)
    ·
      refine ⟨53567556963067201507408309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71423409284089602009877745 53567556963067201507408309)
      ·
        refine ⟨5021958465287550141319529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53567556963067201507408309 5021958465287550141319529)
        ·
          refine ⟨3766468848965662605989647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5021958465287550141319529 3766468848965662605989647)
          ·
            refine ⟨5649703273448493908984471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766468848965662605989647 5649703273448493908984471)
            ·
              refine ⟨8474554910172740863476707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649703273448493908984471 8474554910172740863476707)
              ·
                refine ⟨12711832365259111295215061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474554910172740863476707 12711832365259111295215061)
                ·
                  refine ⟨297933571060760420981603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12711832365259111295215061 297933571060760420981603)
                  ·
                    rfl

theorem cell21_1305503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_1305503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305503 prefixEnd_1305503 := by exact prefixLift 1305503
  have htrace : WordTrace (prefixWord ++ tailWord_1305503) baseStart_1305503 baseEnd_1305503 := by
    simpa [prefixWord, tailWord_1305503, baseEnd_1305503] using wordTrace_append hprefix tailTrace_1305503
  have hstable : (prefixWord ++ tailWord_1305503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305503).length < 2 ^ (prefixWord ++ tailWord_1305503).sum := by decide
  have hdescent : baseEnd_1305503 < baseStart_1305503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305506 : List Nat := [3, 3, 1, 2, 2, 2, 3, 5]
def baseStart_1305506 : Nat := 118140960795 + 1305506 * 2 ^ 59
def prefixEnd_1305506 : Nat := 4983230072969 + 3 ^ 40 * 1305506 * 2
def baseEnd_1305506 : Nat := 99311418567211027477199

theorem tailTrace_1305506 : CollatzResearch.WordTrace tailWord_1305506 prefixEnd_1305506 99311418567211027477199 := by
  unfold tailWord_1305506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903928902095549879736093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31743810405588133012629581 11903928902095549879736093)
  ·
    refine ⟨4463973338285831204901035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11903928902095549879736093 4463973338285831204901035)
    ·
      refine ⟨6695960007428746807351553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463973338285831204901035 6695960007428746807351553)
      ·
        refine ⟨5021970005571560105513665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6695960007428746807351553 5021970005571560105513665)
        ·
          refine ⟨3766477504178670079135249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5021970005571560105513665 3766477504178670079135249)
          ·
            refine ⟨2824858128134002559351437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3766477504178670079135249 2824858128134002559351437)
            ·
              refine ⟨1059321798050250959756789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2824858128134002559351437 1059321798050250959756789)
              ·
                refine ⟨99311418567211027477199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1059321798050250959756789 99311418567211027477199)
                ·
                  rfl

theorem cell21_1305506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_1305506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305506 prefixEnd_1305506 := by exact prefixLift 1305506
  have htrace : WordTrace (prefixWord ++ tailWord_1305506) baseStart_1305506 baseEnd_1305506 := by
    simpa [prefixWord, tailWord_1305506, baseEnd_1305506] using wordTrace_append hprefix tailTrace_1305506
  have hstable : (prefixWord ++ tailWord_1305506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305506).length < 2 ^ (prefixWord ++ tailWord_1305506).sum := by decide
  have hdescent : baseEnd_1305506 < baseStart_1305506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305534 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1305534 : Nat := 118140960795 + 1305534 * 2 ^ 59
def prefixEnd_1305534 : Nat := 4983230072969 + 3 ^ 40 * 1305534 * 2
def baseEnd_1305534 : Nat := 297940645683111255964873

theorem tailTrace_1305534 : CollatzResearch.WordTrace tailWord_1305534 prefixEnd_1305534 297940645683111255964873 := by
  unfold tailWord_1305534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952092106535095037620457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31744491234853840200642437 5952092106535095037620457)
  ·
    refine ⟨4464069079901321278215343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5952092106535095037620457 4464069079901321278215343)
    ·
      refine ⟨6696103619851981917323015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4464069079901321278215343 6696103619851981917323015)
      ·
        refine ⟨10044155429777972875984523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696103619851981917323015 10044155429777972875984523)
        ·
          refine ⟨15066233144666959313976785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10044155429777972875984523 15066233144666959313976785)
          ·
            refine ⟨11299674858500219485482589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15066233144666959313976785 11299674858500219485482589)
            ·
              refine ⟨4237378071937582307055971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11299674858500219485482589 4237378071937582307055971)
              ·
                refine ⟨6356067107906373460583957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237378071937582307055971 6356067107906373460583957)
                ·
                  refine ⟨297940645683111255964873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6356067107906373460583957 297940645683111255964873)
                  ·
                    rfl

theorem cell21_1305534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1305534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305534 prefixEnd_1305534 := by exact prefixLift 1305534
  have htrace : WordTrace (prefixWord ++ tailWord_1305534) baseStart_1305534 baseEnd_1305534 := by
    simpa [prefixWord, tailWord_1305534, baseEnd_1305534] using wordTrace_append hprefix tailTrace_1305534
  have hstable : (prefixWord ++ tailWord_1305534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305534).length < 2 ^ (prefixWord ++ tailWord_1305534).sum := by decide
  have hdescent : baseEnd_1305534 < baseStart_1305534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305548 : List Nat := [2, 2, 1, 4, 1, 1, 2, 8]
def baseStart_1305548 : Nat := 118140960795 + 1305548 * 2 ^ 59
def prefixEnd_1305548 : Nat := 4983230072969 + 3 ^ 40 * 1305548 * 2
def baseEnd_1305548 : Nat := 99314613557950114243837

theorem tailTrace_1305548 : CollatzResearch.WordTrace tailWord_1305548 prefixEnd_1305548 99314613557950114243837 := by
  unfold tailWord_1305548
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808623737115020345986649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31744831649486693794648865 23808623737115020345986649)
  ·
    refine ⟨17856467802836265259489987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23808623737115020345986649 17856467802836265259489987)
    ·
      refine ⟨26784701704254397889234981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17856467802836265259489987 26784701704254397889234981)
      ·
        refine ⟨5022131569547699604231559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26784701704254397889234981 5022131569547699604231559)
        ·
          refine ⟨7533197354321549406347339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022131569547699604231559 7533197354321549406347339)
          ·
            refine ⟨11299796031482324109521009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7533197354321549406347339 11299796031482324109521009)
            ·
              refine ⟨8474847023611743082140757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11299796031482324109521009 8474847023611743082140757)
              ·
                refine ⟨99314613557950114243837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8474847023611743082140757 99314613557950114243837)
                ·
                  rfl

theorem cell21_1305548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_1305548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305548 prefixEnd_1305548 := by exact prefixLift 1305548
  have htrace : WordTrace (prefixWord ++ tailWord_1305548) baseStart_1305548 baseEnd_1305548 := by
    simpa [prefixWord, tailWord_1305548, baseEnd_1305548] using wordTrace_append hprefix tailTrace_1305548
  have hstable : (prefixWord ++ tailWord_1305548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305548).length < 2 ^ (prefixWord ++ tailWord_1305548).sum := by decide
  have hdescent : baseEnd_1305548 < baseStart_1305548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305551 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 4]
def baseStart_1305551 : Nat := 118140960795 + 1305551 * 2 ^ 59
def prefixEnd_1305551 : Nat := 4983230072969 + 3 ^ 40 * 1305551 * 2
def baseEnd_1305551 : Nat := 297944525314723004181505

theorem tailTrace_1305551 : CollatzResearch.WordTrace tailWord_1305551 prefixEnd_1305551 297944525314723004181505 := by
  unfold tailWord_1305551
  simp only [CollatzResearch.WordTrace]
  refine ⟨47617356893219172204332507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31744904595479448136221671 47617356893219172204332507)
  ·
    refine ⟨71426035339828758306498761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47617356893219172204332507 71426035339828758306498761)
    ·
      refine ⟨53569526504871568729874071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71426035339828758306498761 53569526504871568729874071)
      ·
        refine ⟨80354289757307353094811107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53569526504871568729874071 80354289757307353094811107)
        ·
          refine ⟨120531434635961029642216661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80354289757307353094811107 120531434635961029642216661)
          ·
            refine ⟨2824955499280336632239453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 120531434635961029642216661 2824955499280336632239453)
            ·
              refine ⟨1059358312230126237089795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2824955499280336632239453 1059358312230126237089795)
              ·
                refine ⟨1589037468345189355634693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059358312230126237089795 1589037468345189355634693)
                ·
                  refine ⟨297944525314723004181505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589037468345189355634693 297944525314723004181505)
                  ·
                    rfl

theorem cell21_1305551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4].length) (baseStart_1305551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305551 prefixEnd_1305551 := by exact prefixLift 1305551
  have htrace : WordTrace (prefixWord ++ tailWord_1305551) baseStart_1305551 baseEnd_1305551 := by
    simpa [prefixWord, tailWord_1305551, baseEnd_1305551] using wordTrace_append hprefix tailTrace_1305551
  have hstable : (prefixWord ++ tailWord_1305551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305551).length < 2 ^ (prefixWord ++ tailWord_1305551).sum := by decide
  have hdescent : baseEnd_1305551 < baseStart_1305551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305565 : List Nat := [1, 4, 3, 1, 2, 2, 1, 7]
def baseStart_1305565 : Nat := 118140960795 + 1305565 * 2 ^ 59
def prefixEnd_1305565 : Nat := 4983230072969 + 3 ^ 40 * 1305565 * 2
def baseEnd_1305565 : Nat := 99315906768487363649381

theorem tailTrace_1305565 : CollatzResearch.WordTrace tailWord_1305565 prefixEnd_1305565 99315906768487363649381 := by
  unfold tailWord_1305565
  simp only [CollatzResearch.WordTrace]
  refine ⟨47617867515168452595342149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31745245010112301730228099 47617867515168452595342149)
  ·
    refine ⟨8928350159094084861626653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47617867515168452595342149 8928350159094084861626653)
    ·
      refine ⟨3348131309660281823109995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8928350159094084861626653 3348131309660281823109995)
      ·
        refine ⟨5022196964490422734664993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348131309660281823109995 5022196964490422734664993)
        ·
          refine ⟨3766647723367817050998745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5022196964490422734664993 3766647723367817050998745)
          ·
            refine ⟨2824985792525862788249059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3766647723367817050998745 2824985792525862788249059)
            ·
              refine ⟨4237478688788794182373589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824985792525862788249059 4237478688788794182373589)
              ·
                refine ⟨99315906768487363649381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4237478688788794182373589 99315906768487363649381)
                ·
                  rfl

theorem cell21_1305565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_1305565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305565 prefixEnd_1305565 := by exact prefixLift 1305565
  have htrace : WordTrace (prefixWord ++ tailWord_1305565) baseStart_1305565 baseEnd_1305565 := by
    simpa [prefixWord, tailWord_1305565, baseEnd_1305565] using wordTrace_append hprefix tailTrace_1305565
  have hstable : (prefixWord ++ tailWord_1305565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305565).length < 2 ^ (prefixWord ++ tailWord_1305565).sum := by decide
  have hdescent : baseEnd_1305565 < baseStart_1305565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305582 : List Nat := [4, 1, 2, 1, 5, 1, 7]
def baseStart_1305582 : Nat := 118140960795 + 1305582 * 2 ^ 59
def prefixEnd_1305582 : Nat := 4983230072969 + 3 ^ 40 * 1305582 * 2
def baseEnd_1305582 : Nat := 33105733326341537684975

theorem tailTrace_1305582 : CollatzResearch.WordTrace tailWord_1305582 prefixEnd_1305582 33105733326341537684975 := by
  unfold tailWord_1305582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952310944513358062338875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31745658370737909665807333 5952310944513358062338875)
  ·
    refine ⟨8928466416770037093508313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952310944513358062338875 8928466416770037093508313)
    ·
      refine ⟨6696349812577527820131235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8928466416770037093508313 6696349812577527820131235)
      ·
        refine ⟨10044524718866291730196853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696349812577527820131235 10044524718866291730196853)
        ·
          refine ⟨941674192393714849705955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10044524718866291730196853 941674192393714849705955)
          ·
            refine ⟨1412511288590572274558933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941674192393714849705955 1412511288590572274558933)
            ·
              refine ⟨33105733326341537684975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1412511288590572274558933 33105733326341537684975)
              ·
                rfl

theorem cell21_1305582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 7].length) (baseStart_1305582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305582 prefixEnd_1305582 := by exact prefixLift 1305582
  have htrace : WordTrace (prefixWord ++ tailWord_1305582) baseStart_1305582 baseEnd_1305582 := by
    simpa [prefixWord, tailWord_1305582, baseEnd_1305582] using wordTrace_append hprefix tailTrace_1305582
  have hstable : (prefixWord ++ tailWord_1305582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305582).length < 2 ^ (prefixWord ++ tailWord_1305582).sum := by decide
  have hdescent : baseEnd_1305582 < baseStart_1305582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305588 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1305588 : Nat := 118140960795 + 1305588 * 2 ^ 59
def prefixEnd_1305588 : Nat := 4983230072969 + 3 ^ 40 * 1305588 * 2
def baseEnd_1305588 : Nat := 297952969218819162064763

theorem tailTrace_1305588 : CollatzResearch.WordTrace tailWord_1305588 prefixEnd_1305588 297952969218819162064763 := by
  unfold tailWord_1305588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23809353197042563761714709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31745804262723418348952945 23809353197042563761714709)
  ·
    refine ⟨1116063431111370176330377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23809353197042563761714709 1116063431111370176330377)
    ·
      refine ⟨837047573333527632247783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116063431111370176330377 837047573333527632247783)
      ·
        refine ⟨1255571360000291448371675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837047573333527632247783 1255571360000291448371675)
        ·
          refine ⟨1883357040000437172557513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255571360000291448371675 1883357040000437172557513)
          ·
            refine ⟨1412517780000327879418135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883357040000437172557513 1412517780000327879418135)
            ·
              refine ⟨2118776670000491819127203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412517780000327879418135 2118776670000491819127203)
              ·
                refine ⟨3178165005000737728690805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118776670000491819127203 3178165005000737728690805)
                ·
                  refine ⟨297952969218819162064763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178165005000737728690805 297952969218819162064763)
                  ·
                    rfl

theorem cell21_1305588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1305588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305588 prefixEnd_1305588 := by exact prefixLift 1305588
  have htrace : WordTrace (prefixWord ++ tailWord_1305588) baseStart_1305588 baseEnd_1305588 := by
    simpa [prefixWord, tailWord_1305588, baseEnd_1305588] using wordTrace_append hprefix tailTrace_1305588
  have hstable : (prefixWord ++ tailWord_1305588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305588).length < 2 ^ (prefixWord ++ tailWord_1305588).sum := by decide
  have hdescent : baseEnd_1305588 < baseStart_1305588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305593 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_1305593 : Nat := 118140960795 + 1305593 * 2 ^ 59
def prefixEnd_1305593 : Nat := 4983230072969 + 3 ^ 40 * 1305593 * 2
def baseEnd_1305593 : Nat := 297954110286940264481419

theorem tailTrace_1305593 : CollatzResearch.WordTrace tailWord_1305593 prefixEnd_1305593 297954110286940264481419 := by
  unfold tailWord_1305593
  simp only [CollatzResearch.WordTrace]
  refine ⟨47618888759067013377361433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31745925839378008918240955 47618888759067013377361433)
  ·
    refine ⟨35714166569300260033021075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47618888759067013377361433 35714166569300260033021075)
    ·
      refine ⟨53571249853950390049531613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35714166569300260033021075 53571249853950390049531613)
      ·
        refine ⟨20089218695231396268574355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53571249853950390049531613 20089218695231396268574355)
        ·
          refine ⟨30133828042847094402861533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089218695231396268574355 30133828042847094402861533)
          ·
            refine ⟨11300185516067660401073075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30133828042847094402861533 11300185516067660401073075)
            ·
              refine ⟨16950278274101490601609613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11300185516067660401073075 16950278274101490601609613)
              ·
                refine ⟨6356354352788058975603605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16950278274101490601609613 6356354352788058975603605)
                ·
                  refine ⟨297954110286940264481419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6356354352788058975603605 297954110286940264481419)
                  ·
                    rfl

theorem cell21_1305593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_1305593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305593 prefixEnd_1305593 := by exact prefixLift 1305593
  have htrace : WordTrace (prefixWord ++ tailWord_1305593) baseStart_1305593 baseEnd_1305593 := by
    simpa [prefixWord, tailWord_1305593, baseEnd_1305593] using wordTrace_append hprefix tailTrace_1305593
  have hstable : (prefixWord ++ tailWord_1305593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305593).length < 2 ^ (prefixWord ++ tailWord_1305593).sum := by decide
  have hdescent : baseEnd_1305593 < baseStart_1305593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305596 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_1305596 : Nat := 118140960795 + 1305596 * 2 ^ 59
def prefixEnd_1305596 : Nat := 4983230072969 + 3 ^ 40 * 1305596 * 2
def baseEnd_1305596 : Nat := 297954794927812925931413

theorem tailTrace_1305596 : CollatzResearch.WordTrace tailWord_1305596 prefixEnd_1305596 297954794927812925931413 := by
  unfold tailWord_1305596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23809499089028072444860321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31745998785370763259813761 23809499089028072444860321)
  ·
    refine ⟨17857124316771054333645241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23809499089028072444860321 17857124316771054333645241)
    ·
      refine ⟨13392843237578290750233931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17857124316771054333645241 13392843237578290750233931)
      ·
        refine ⟨20089264856367436125350897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13392843237578290750233931 20089264856367436125350897)
        ·
          refine ⟨15066948642275577094013173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20089264856367436125350897 15066948642275577094013173)
          ·
            refine ⟨1412526435213335352563735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15066948642275577094013173 1412526435213335352563735)
            ·
              refine ⟨2118789652820003028845603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412526435213335352563735 2118789652820003028845603)
              ·
                refine ⟨3178184479230004543268405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118789652820003028845603 3178184479230004543268405)
                ·
                  refine ⟨297954794927812925931413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178184479230004543268405 297954794927812925931413)
                  ·
                    rfl

theorem cell21_1305596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_1305596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305596 prefixEnd_1305596 := by exact prefixLift 1305596
  have htrace : WordTrace (prefixWord ++ tailWord_1305596) baseStart_1305596 baseEnd_1305596 := by
    simpa [prefixWord, tailWord_1305596, baseEnd_1305596] using wordTrace_append hprefix tailTrace_1305596
  have hstable : (prefixWord ++ tailWord_1305596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305596).length < 2 ^ (prefixWord ++ tailWord_1305596).sum := by decide
  have hdescent : baseEnd_1305596 < baseStart_1305596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305602 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1305602 : Nat := 118140960795 + 1305602 * 2 ^ 59
def prefixEnd_1305602 : Nat := 4983230072969 + 3 ^ 40 * 1305602 * 2
def baseEnd_1305602 : Nat := 297956164209558248831401

theorem tailTrace_1305602 : CollatzResearch.WordTrace tailWord_1305602 prefixEnd_1305602 297956164209558248831401 := by
  unfold tailWord_1305602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11904804254008601978609765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31746144677356271942959373 11904804254008601978609765)
  ·
    refine ⟨2232150797626612870989331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11904804254008601978609765 2232150797626612870989331)
    ·
      refine ⟨3348226196439919306483997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232150797626612870989331 3348226196439919306483997)
      ·
        refine ⟨1255584823664969739931499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3348226196439919306483997 1255584823664969739931499)
        ·
          refine ⟨1883377235497454609897249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255584823664969739931499 1883377235497454609897249)
          ·
            refine ⟨1412532926623090957422937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883377235497454609897249 1412532926623090957422937)
            ·
              refine ⟨1059399694967318218067203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412532926623090957422937 1059399694967318218067203)
              ·
                refine ⟨1589099542450977327100805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059399694967318218067203 1589099542450977327100805)
                ·
                  refine ⟨297956164209558248831401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589099542450977327100805 297956164209558248831401)
                  ·
                    rfl

theorem cell21_1305602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1305602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305602 prefixEnd_1305602 := by exact prefixLift 1305602
  have htrace : WordTrace (prefixWord ++ tailWord_1305602) baseStart_1305602 baseEnd_1305602 := by
    simpa [prefixWord, tailWord_1305602, baseEnd_1305602] using wordTrace_append hprefix tailTrace_1305602
  have hstable : (prefixWord ++ tailWord_1305602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305602).length < 2 ^ (prefixWord ++ tailWord_1305602).sum := by decide
  have hdescent : baseEnd_1305602 < baseStart_1305602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305624 : List Nat := [2, 1, 2, 3, 2, 2, 2, 7]
def baseStart_1305624 : Nat := 118140960795 + 1305624 * 2 ^ 59
def prefixEnd_1305624 : Nat := 4983230072969 + 3 ^ 40 * 1305624 * 2
def baseEnd_1305624 : Nat := 99320394969763699821563

theorem tailTrace_1305624 : CollatzResearch.WordTrace tailWord_1305624 prefixEnd_1305624 99320394969763699821563 := by
  unfold tailWord_1305624
  simp only [CollatzResearch.WordTrace]
  refine ⟨23810009710977352835869963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31746679614636470447826617 23810009710977352835869963)
  ·
    refine ⟨35715014566466029253804945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23810009710977352835869963 35715014566466029253804945)
    ·
      refine ⟨26786260924849521940353709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35715014566466029253804945 26786260924849521940353709)
      ·
        refine ⟨10044847846818570727632641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26786260924849521940353709 10044847846818570727632641)
        ·
          refine ⟨7533635885113928045724481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10044847846818570727632641 7533635885113928045724481)
          ·
            refine ⟨5650226913835446034293361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7533635885113928045724481 5650226913835446034293361)
            ·
              refine ⟨4237670185376584525720021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5650226913835446034293361 4237670185376584525720021)
              ·
                refine ⟨99320394969763699821563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4237670185376584525720021 99320394969763699821563)
                ·
                  rfl

theorem cell21_1305624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_1305624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305624 prefixEnd_1305624 := by exact prefixLift 1305624
  have htrace : WordTrace (prefixWord ++ tailWord_1305624) baseStart_1305624 baseEnd_1305624 := by
    simpa [prefixWord, tailWord_1305624, baseEnd_1305624] using wordTrace_append hprefix tailTrace_1305624
  have hstable : (prefixWord ++ tailWord_1305624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305624).length < 2 ^ (prefixWord ++ tailWord_1305624).sum := by decide
  have hdescent : baseEnd_1305624 < baseStart_1305624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305703 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 4]
def baseStart_1305703 : Nat := 118140960795 + 1305703 * 2 ^ 59
def prefixEnd_1305703 : Nat := 4983230072969 + 3 ^ 40 * 1305703 * 2
def baseEnd_1305703 : Nat := 297979213785604517647861

theorem tailTrace_1305703 : CollatzResearch.WordTrace tailWord_1305703 prefixEnd_1305703 297979213785604517647861 := by
  unfold tailWord_1305703
  simp only [CollatzResearch.WordTrace]
  refine ⟨47622900788668502163865763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31748600525779001442577175 47622900788668502163865763)
  ·
    refine ⟨71434351183002753245798645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47622900788668502163865763 71434351183002753245798645)
    ·
      refine ⟨6696970423406508116793623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71434351183002753245798645 6696970423406508116793623)
      ·
        refine ⟨10045455635109762175190435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696970423406508116793623 10045455635109762175190435)
        ·
          refine ⟨15068183452664643262785653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10045455635109762175190435 15068183452664643262785653)
          ·
            refine ⟨1412642198687310305886155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15068183452664643262785653 1412642198687310305886155)
            ·
              refine ⟨2118963298030965458829233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412642198687310305886155 2118963298030965458829233)
              ·
                refine ⟨1589222473523224094121925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118963298030965458829233 1589222473523224094121925)
                ·
                  refine ⟨297979213785604517647861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589222473523224094121925 297979213785604517647861)
                  ·
                    rfl

theorem cell21_1305703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_1305703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305703 prefixEnd_1305703 := by exact prefixLift 1305703
  have htrace : WordTrace (prefixWord ++ tailWord_1305703) baseStart_1305703 baseEnd_1305703 := by
    simpa [prefixWord, tailWord_1305703, baseEnd_1305703] using wordTrace_append hprefix tailTrace_1305703
  have hstable : (prefixWord ++ tailWord_1305703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305703).length < 2 ^ (prefixWord ++ tailWord_1305703).sum := by decide
  have hdescent : baseEnd_1305703 < baseStart_1305703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305765 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 3]
def baseStart_1305765 : Nat := 118140960795 + 1305765 * 2 ^ 59
def prefixEnd_1305765 : Nat := 4983230072969 + 3 ^ 40 * 1305765 * 2
def baseEnd_1305765 : Nat := 297993363030306187614401

theorem tailTrace_1305765 : CollatzResearch.WordTrace tailWord_1305765 prefixEnd_1305765 297993363030306187614401 := by
  unfold tailWord_1305765
  simp only [CollatzResearch.WordTrace]
  refine ⟨47625162114443886752622749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31750108076295924501748499 47625162114443886752622749)
  ·
    refine ⟨17859435792916457532233531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47625162114443886752622749 17859435792916457532233531)
    ·
      refine ⟨26789153689374686298350297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17859435792916457532233531 26789153689374686298350297)
      ·
        refine ⟨20091865267031014723762723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26789153689374686298350297 20091865267031014723762723)
        ·
          refine ⟨30137797900546522085644085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20091865267031014723762723 30137797900546522085644085)
          ·
            refine ⟨2825418553176236445529133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30137797900546522085644085 2825418553176236445529133)
            ·
              refine ⟨1059531957441088667073425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825418553176236445529133 1059531957441088667073425)
              ·
                refine ⟨794648968080816500305069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059531957441088667073425 794648968080816500305069)
                ·
                  refine ⟨297993363030306187614401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794648968080816500305069 297993363030306187614401)
                  ·
                    rfl

theorem cell21_1305765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_1305765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305765 prefixEnd_1305765 := by exact prefixLift 1305765
  have htrace : WordTrace (prefixWord ++ tailWord_1305765) baseStart_1305765 baseEnd_1305765 := by
    simpa [prefixWord, tailWord_1305765, baseEnd_1305765] using wordTrace_append hprefix tailTrace_1305765
  have hstable : (prefixWord ++ tailWord_1305765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305765).length < 2 ^ (prefixWord ++ tailWord_1305765).sum := by decide
  have hdescent : baseEnd_1305765 < baseStart_1305765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305793 : List Nat := [1, 2, 6, 1, 1, 1, 2, 7]
def baseStart_1305793 : Nat := 118140960795 + 1305793 * 2 ^ 59
def prefixEnd_1305793 : Nat := 4983230072969 + 3 ^ 40 * 1305793 * 2
def baseEnd_1305793 : Nat := 99333251003928120382559

theorem tailTrace_1305793 : CollatzResearch.WordTrace tailWord_1305793 prefixEnd_1305793 99333251003928120382559 := by
  unfold tailWord_1305793
  simp only [CollatzResearch.WordTrace]
  refine ⟨47626183358342447534642033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31750788905561631689761355 47626183358342447534642033)
  ·
    refine ⟨35719637518756835650981525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47626183358342447534642033 35719637518756835650981525)
    ·
      refine ⟨1674358008691726671139759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35719637518756835650981525 1674358008691726671139759)
      ·
        refine ⟨2511537013037590006709639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674358008691726671139759 2511537013037590006709639)
        ·
          refine ⟨3767305519556385010064459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511537013037590006709639 3767305519556385010064459)
          ·
            refine ⟨5650958279334577515096689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767305519556385010064459 5650958279334577515096689)
            ·
              refine ⟨4238218709500933136322517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5650958279334577515096689 4238218709500933136322517)
              ·
                refine ⟨99333251003928120382559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4238218709500933136322517 99333251003928120382559)
                ·
                  rfl

theorem cell21_1305793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_1305793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305793 prefixEnd_1305793 := by exact prefixLift 1305793
  have htrace : WordTrace (prefixWord ++ tailWord_1305793) baseStart_1305793 baseEnd_1305793 := by
    simpa [prefixWord, tailWord_1305793, baseEnd_1305793] using wordTrace_append hprefix tailTrace_1305793
  have hstable : (prefixWord ++ tailWord_1305793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305793).length < 2 ^ (prefixWord ++ tailWord_1305793).sum := by decide
  have hdescent : baseEnd_1305793 < baseStart_1305793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305824 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_1305824 : Nat := 118140960795 + 1305824 * 2 ^ 59
def prefixEnd_1305824 : Nat := 4983230072969 + 3 ^ 40 * 1305824 * 2
def baseEnd_1305824 : Nat := 298006827634135196130947

theorem tailTrace_1305824 : CollatzResearch.WordTrace tailWord_1305824 prefixEnd_1305824 298006827634135196130947 := by
  unfold tailWord_1305824
  simp only [CollatzResearch.WordTrace]
  refine ⟨23813657010615069914510263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31751542680820093219347017 23813657010615069914510263)
  ·
    refine ⟨35720485515922604871765395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23813657010615069914510263 35720485515922604871765395)
    ·
      refine ⟨53580728273883907307648093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35720485515922604871765395 53580728273883907307648093)
      ·
        refine ⟨20092773102706465240368035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53580728273883907307648093 20092773102706465240368035)
        ·
          refine ⟨30139159654059697860552053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20092773102706465240368035 30139159654059697860552053)
          ·
            refine ⟨2825546217568096674426755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30139159654059697860552053 2825546217568096674426755)
            ·
              refine ⟨4238319326352145011640133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825546217568096674426755 4238319326352145011640133)
              ·
                refine ⟨794684873691027189682525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4238319326352145011640133 794684873691027189682525)
                ·
                  refine ⟨298006827634135196130947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794684873691027189682525 298006827634135196130947)
                  ·
                    rfl

theorem cell21_1305824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_1305824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305824 prefixEnd_1305824 := by exact prefixLift 1305824
  have htrace : WordTrace (prefixWord ++ tailWord_1305824) baseStart_1305824 baseEnd_1305824 := by
    simpa [prefixWord, tailWord_1305824, baseEnd_1305824] using wordTrace_append hprefix tailTrace_1305824
  have hstable : (prefixWord ++ tailWord_1305824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305824).length < 2 ^ (prefixWord ++ tailWord_1305824).sum := by decide
  have hdescent : baseEnd_1305824 < baseStart_1305824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305838 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1305838 : Nat := 118140960795 + 1305838 * 2 ^ 59
def prefixEnd_1305838 : Nat := 4983230072969 + 3 ^ 40 * 1305838 * 2
def baseEnd_1305838 : Nat := 298010022624874282897585

theorem tailTrace_1305838 : CollatzResearch.WordTrace tailWord_1305838 prefixEnd_1305838 298010022624874282897585 := by
  unfold tailWord_1305838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5953478080397427527503771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31751883095452946813353445 5953478080397427527503771)
  ·
    refine ⟨8930217120596141291255657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5953478080397427527503771 8930217120596141291255657)
    ·
      refine ⟨6697662840447105968441743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8930217120596141291255657 6697662840447105968441743)
      ·
        refine ⟨10046494260670658952662615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697662840447105968441743 10046494260670658952662615)
        ·
          refine ⟨15069741391005988428993923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046494260670658952662615 15069741391005988428993923)
          ·
            refine ⟨22604612086508982643490885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15069741391005988428993923 22604612086508982643490885)
            ·
              refine ⟨4238364766220434245654541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22604612086508982643490885 4238364766220434245654541)
              ·
                refine ⟨1589386787332662842120453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4238364766220434245654541 1589386787332662842120453)
                ·
                  refine ⟨298010022624874282897585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589386787332662842120453 298010022624874282897585)
                  ·
                    rfl

theorem cell21_1305838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1305838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305838 prefixEnd_1305838 := by exact prefixLift 1305838
  have htrace : WordTrace (prefixWord ++ tailWord_1305838) baseStart_1305838 baseEnd_1305838 := by
    simpa [prefixWord, tailWord_1305838, baseEnd_1305838] using wordTrace_append hprefix tailTrace_1305838
  have hstable : (prefixWord ++ tailWord_1305838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305838).length < 2 ^ (prefixWord ++ tailWord_1305838).sum := by decide
  have hdescent : baseEnd_1305838 < baseStart_1305838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305844 : List Nat := [2, 6, 1, 2, 1, 1, 3, 5]
def baseStart_1305844 : Nat := 118140960795 + 1305844 * 2 ^ 59
def prefixEnd_1305844 : Nat := 4983230072969 + 3 ^ 40 * 1305844 * 2
def baseEnd_1305844 : Nat := 99337130635539868599191

theorem tailTrace_1305844 : CollatzResearch.WordTrace tailWord_1305844 prefixEnd_1305844 99337130635539868599191 := by
  unfold tailWord_1305844
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814021740578841622374293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31752028987438455496499057 23814021740578841622374293)
  ·
    refine ⟨1116282269089633201048795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23814021740578841622374293 1116282269089633201048795)
    ·
      refine ⟨1674423403634449801573193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116282269089633201048795 1674423403634449801573193)
      ·
        refine ⟨1255817552725837351179895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674423403634449801573193 1255817552725837351179895)
        ·
          refine ⟨1883726329088756026769843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255817552725837351179895 1883726329088756026769843)
          ·
            refine ⟨2825589493633134040154765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883726329088756026769843 2825589493633134040154765)
            ·
              refine ⟨1059596060112425265058037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825589493633134040154765 1059596060112425265058037)
              ·
                refine ⟨99337130635539868599191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1059596060112425265058037 99337130635539868599191)
                ·
                  rfl

theorem cell21_1305844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_1305844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305844 prefixEnd_1305844 := by exact prefixLift 1305844
  have htrace : WordTrace (prefixWord ++ tailWord_1305844) baseStart_1305844 baseEnd_1305844 := by
    simpa [prefixWord, tailWord_1305844, baseEnd_1305844] using wordTrace_append hprefix tailTrace_1305844
  have hstable : (prefixWord ++ tailWord_1305844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305844).length < 2 ^ (prefixWord ++ tailWord_1305844).sum := by decide
  have hdescent : baseEnd_1305844 < baseStart_1305844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305858 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1305858 : Nat := 118140960795 + 1305858 * 2 ^ 59
def prefixEnd_1305858 : Nat := 4983230072969 + 3 ^ 40 * 1305858 * 2
def baseEnd_1305858 : Nat := 298014586897358692564211

theorem tailTrace_1305858 : CollatzResearch.WordTrace tailWord_1305858 prefixEnd_1305858 298014586897358692564211 := by
  unfold tailWord_1305858
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907138525776740908939557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31752369402071309090505485 11907138525776740908939557)
  ·
    refine ⟨2232588473583138920426167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11907138525776740908939557 2232588473583138920426167)
    ·
      refine ⟨3348882710374708380639251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232588473583138920426167 3348882710374708380639251)
      ·
        refine ⟨5023324065562062570958877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348882710374708380639251 5023324065562062570958877)
        ·
          refine ⟨1883746524585773464109579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5023324065562062570958877 1883746524585773464109579)
          ·
            refine ⟨2825619786878660196164369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883746524585773464109579 2825619786878660196164369)
            ·
              refine ⟨2119214840158995147123277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825619786878660196164369 2119214840158995147123277)
              ·
                refine ⟨794705565059623180171229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2119214840158995147123277 794705565059623180171229)
                ·
                  refine ⟨298014586897358692564211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794705565059623180171229 298014586897358692564211)
                  ·
                    rfl

theorem cell21_1305858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1305858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305858 prefixEnd_1305858 := by exact prefixLift 1305858
  have htrace : WordTrace (prefixWord ++ tailWord_1305858) baseStart_1305858 baseEnd_1305858 := by
    simpa [prefixWord, tailWord_1305858, baseEnd_1305858] using wordTrace_append hprefix tailTrace_1305858
  have hstable : (prefixWord ++ tailWord_1305858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305858).length < 2 ^ (prefixWord ++ tailWord_1305858).sum := by decide
  have hdescent : baseEnd_1305858 < baseStart_1305858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305866 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_1305866 : Nat := 118140960795 + 1305866 * 2 ^ 59
def prefixEnd_1305866 : Nat := 4983230072969 + 3 ^ 40 * 1305866 * 2
def baseEnd_1305866 : Nat := 298016412606352456430861

theorem tailTrace_1305866 : CollatzResearch.WordTrace tailWord_1305866 prefixEnd_1305866 298016412606352456430861 := by
  unfold tailWord_1305866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907211471769495250512363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31752563924718654001366301 11907211471769495250512363)
  ·
    refine ⟨17860817207654242875768545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11907211471769495250512363 17860817207654242875768545)
    ·
      refine ⟨13395612905740682156826409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17860817207654242875768545 13395612905740682156826409)
      ·
        refine ⟨10046709679305511617619807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13395612905740682156826409 10046709679305511617619807)
        ·
          refine ⟨15070064518958267426429711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046709679305511617619807 15070064518958267426429711)
          ·
            refine ⟨22605096778437401139644567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15070064518958267426429711 22605096778437401139644567)
            ·
              refine ⟨33907645167656101709466851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22605096778437401139644567 33907645167656101709466851)
              ·
                refine ⟨50861467751484152564200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33907645167656101709466851 50861467751484152564200277)
                ·
                  refine ⟨298016412606352456430861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50861467751484152564200277 298016412606352456430861)
                  ·
                    rfl

theorem cell21_1305866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_1305866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305866 prefixEnd_1305866 := by exact prefixLift 1305866
  have htrace : WordTrace (prefixWord ++ tailWord_1305866) baseStart_1305866 baseEnd_1305866 := by
    simpa [prefixWord, tailWord_1305866, baseEnd_1305866] using wordTrace_append hprefix tailTrace_1305866
  have hstable : (prefixWord ++ tailWord_1305866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305866).length < 2 ^ (prefixWord ++ tailWord_1305866).sum := by decide
  have hdescent : baseEnd_1305866 < baseStart_1305866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305987 : List Nat := [1, 1, 1, 3, 5, 10]
def baseStart_1305987 : Nat := 118140960795 + 1305987 * 2 ^ 59
def prefixEnd_1305987 : Nat := 4983230072969 + 3 ^ 40 * 1305987 * 2
def baseEnd_1305987 : Nat := 11038667646477153144961

theorem tailTrace_1305987 : CollatzResearch.WordTrace tailWord_1305987 prefixEnd_1305987 11038667646477153144961 := by
  unfold tailWord_1305987
  simp only [CollatzResearch.WordTrace]
  refine ⟨47633259119639618667204215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31755506079759745778136143 47633259119639618667204215)
  ·
    refine ⟨71449888679459428000806323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47633259119639618667204215 71449888679459428000806323)
    ·
      refine ⟨107174833019189142001209485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71449888679459428000806323 107174833019189142001209485)
      ·
        refine ⟨40190562382195928250453557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107174833019189142001209485 40190562382195928250453557)
        ·
          refine ⟨3767865223330868273480021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40190562382195928250453557 3767865223330868273480021)
          ·
            refine ⟨11038667646477153144961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3767865223330868273480021 11038667646477153144961)
            ·
              rfl

theorem cell21_1305987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 10].length) (baseStart_1305987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1305987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1305987 prefixEnd_1305987 := by exact prefixLift 1305987
  have htrace : WordTrace (prefixWord ++ tailWord_1305987) baseStart_1305987 baseEnd_1305987 := by
    simpa [prefixWord, tailWord_1305987, baseEnd_1305987] using wordTrace_append hprefix tailTrace_1305987
  have hstable : (prefixWord ++ tailWord_1305987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305987).length < 2 ^ (prefixWord ++ tailWord_1305987).sum := by decide
  have hdescent : baseEnd_1305987 < baseStart_1305987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306052 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1306052 : Nat := 118140960795 + 1306052 * 2 ^ 59
def prefixEnd_1306052 : Nat := 4983230072969 + 3 ^ 40 * 1306052 * 2
def baseEnd_1306052 : Nat := 298058860340457466330481

theorem tailTrace_1306052 : CollatzResearch.WordTrace tailWord_1306052 prefixEnd_1306052 298058860340457466330481 := by
  unfold tailWord_1306052
  simp only [CollatzResearch.WordTrace]
  refine ⟨23817814932202067384160205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31757086576269423178880273 23817814932202067384160205)
  ·
    refine ⟨8931680599575775269060077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23817814932202067384160205 8931680599575775269060077)
    ·
      refine ⟨3349380224840915725897529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8931680599575775269060077 3349380224840915725897529)
      ·
        refine ⟨2512035168630686794423147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3349380224840915725897529 2512035168630686794423147)
        ·
          refine ⟨3768052752946030191634721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512035168630686794423147 3768052752946030191634721)
          ·
            refine ⟨2826039564709522643726041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3768052752946030191634721 2826039564709522643726041)
            ·
              refine ⟨2119529673532141982794531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2826039564709522643726041 2119529673532141982794531)
              ·
                refine ⟨3179294510298212974191797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119529673532141982794531 3179294510298212974191797)
                ·
                  refine ⟨298058860340457466330481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3179294510298212974191797 298058860340457466330481)
                  ·
                    rfl

theorem cell21_1306052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1306052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306052 prefixEnd_1306052 := by exact prefixLift 1306052
  have htrace : WordTrace (prefixWord ++ tailWord_1306052) baseStart_1306052 baseEnd_1306052 := by
    simpa [prefixWord, tailWord_1306052, baseEnd_1306052] using wordTrace_append hprefix tailTrace_1306052
  have hstable : (prefixWord ++ tailWord_1306052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306052).length < 2 ^ (prefixWord ++ tailWord_1306052).sum := by decide
  have hdescent : baseEnd_1306052 < baseStart_1306052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306170 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1306170 : Nat := 118140960795 + 1306170 * 2 ^ 59
def prefixEnd_1306170 : Nat := 4983230072969 + 3 ^ 40 * 1306170 * 2
def baseEnd_1306170 : Nat := 298085789548115483363573

theorem tailTrace_1306170 : CollatzResearch.WordTrace tailWord_1306170 prefixEnd_1306170 298085789548115483363573 := by
  unfold tailWord_1306170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909983419494160230278991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31759955785317760614077309 11909983419494160230278991)
  ·
    refine ⟨17864975129241240345418487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11909983419494160230278991 17864975129241240345418487)
    ·
      refine ⟨26797462693861860518127731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17864975129241240345418487 26797462693861860518127731)
      ·
        refine ⟨40196194040792790777191597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26797462693861860518127731 40196194040792790777191597)
        ·
          refine ⟨15073572765297296541446849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40196194040792790777191597 15073572765297296541446849)
          ·
            refine ⟨11305179573972972406085137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15073572765297296541446849 11305179573972972406085137)
            ·
              refine ⟨8478884680479729304563853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11305179573972972406085137 8478884680479729304563853)
              ·
                refine ⟨3179581755179898489211445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8478884680479729304563853 3179581755179898489211445)
                ·
                  refine ⟨298085789548115483363573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3179581755179898489211445 298085789548115483363573)
                  ·
                    rfl

theorem cell21_1306170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1306170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306170 prefixEnd_1306170 := by exact prefixLift 1306170
  have htrace : WordTrace (prefixWord ++ tailWord_1306170) baseStart_1306170 baseEnd_1306170 := by
    simpa [prefixWord, tailWord_1306170, baseEnd_1306170] using wordTrace_append hprefix tailTrace_1306170
  have hstable : (prefixWord ++ tailWord_1306170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306170).length < 2 ^ (prefixWord ++ tailWord_1306170).sum := by decide
  have hdescent : baseEnd_1306170 < baseStart_1306170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306173 : List Nat := [1, 4, 1, 3, 3, 2, 1, 6]
def baseStart_1306173 : Nat := 118140960795 + 1306173 * 2 ^ 59
def prefixEnd_1306173 : Nat := 4983230072969 + 3 ^ 40 * 1306173 * 2
def baseEnd_1306173 : Nat := 99362158062996048271189

theorem tailTrace_1306173 : CollatzResearch.WordTrace tailWord_1306173 prefixEnd_1306173 99362158062996048271189 := by
  unfold tailWord_1306173
  simp only [CollatzResearch.WordTrace]
  refine ⟨47640043096965772433475173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31760028731310514955650115 47640043096965772433475173)
  ·
    refine ⟨8932508080681082331276595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47640043096965772433475173 8932508080681082331276595)
    ·
      refine ⟨13398762121021623496914893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8932508080681082331276595 13398762121021623496914893)
      ·
        refine ⟨5024535795383108811343085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13398762121021623496914893 5024535795383108811343085)
        ·
          refine ⟨1884200923268665804253657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5024535795383108811343085 1884200923268665804253657)
          ·
            refine ⟨1413150692451499353190243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1884200923268665804253657 1413150692451499353190243)
            ·
              refine ⟨2119726038677249029785365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413150692451499353190243 2119726038677249029785365)
              ·
                refine ⟨99362158062996048271189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2119726038677249029785365 99362158062996048271189)
                ·
                  rfl

theorem cell21_1306173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 6].length) (baseStart_1306173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306173 prefixEnd_1306173 := by exact prefixLift 1306173
  have htrace : WordTrace (prefixWord ++ tailWord_1306173) baseStart_1306173 baseEnd_1306173 := by
    simpa [prefixWord, tailWord_1306173, baseEnd_1306173] using wordTrace_append hprefix tailTrace_1306173
  have hstable : (prefixWord ++ tailWord_1306173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306173).length < 2 ^ (prefixWord ++ tailWord_1306173).sum := by decide
  have hdescent : baseEnd_1306173 < baseStart_1306173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306184 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_1306184 : Nat := 118140960795 + 1306184 * 2 ^ 59
def prefixEnd_1306184 : Nat := 4983230072969 + 3 ^ 40 * 1306184 * 2
def baseEnd_1306184 : Nat := 298088984538854570130211

theorem tailTrace_1306184 : CollatzResearch.WordTrace tailWord_1306184 prefixEnd_1306184 298088984538854570130211 := by
  unfold tailWord_1306184
  simp only [CollatzResearch.WordTrace]
  refine ⟨23820222149962960656062803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31760296199950614208083737 23820222149962960656062803)
  ·
    refine ⟨35730333224944440984094205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23820222149962960656062803 35730333224944440984094205)
    ·
      refine ⟨13398874959354165369035327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35730333224944440984094205 13398874959354165369035327)
      ·
        refine ⟨20098312439031248053552991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13398874959354165369035327 20098312439031248053552991)
        ·
          refine ⟨30147468658546872080329487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20098312439031248053552991 30147468658546872080329487)
          ·
            refine ⟨45221202987820308120494231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30147468658546872080329487 45221202987820308120494231)
            ·
              refine ⟨67831804481730462180741347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45221202987820308120494231 67831804481730462180741347)
              ·
                refine ⟨101747706722595693271112021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67831804481730462180741347 101747706722595693271112021)
                ·
                  refine ⟨298088984538854570130211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 101747706722595693271112021 298088984538854570130211)
                  ·
                    rfl

theorem cell21_1306184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_1306184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306184 prefixEnd_1306184 := by exact prefixLift 1306184
  have htrace : WordTrace (prefixWord ++ tailWord_1306184) baseStart_1306184 baseEnd_1306184 := by
    simpa [prefixWord, tailWord_1306184, baseEnd_1306184] using wordTrace_append hprefix tailTrace_1306184
  have hstable : (prefixWord ++ tailWord_1306184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306184).length < 2 ^ (prefixWord ++ tailWord_1306184).sum := by decide
  have hdescent : baseEnd_1306184 < baseStart_1306184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306204 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1306204 : Nat := 118140960795 + 1306204 * 2 ^ 59
def prefixEnd_1306204 : Nat := 4983230072969 + 3 ^ 40 * 1306204 * 2
def baseEnd_1306204 : Nat := 298093548811338979796837

theorem tailTrace_1306204 : CollatzResearch.WordTrace tailWord_1306204 prefixEnd_1306204 298093548811338979796837 := by
  unfold tailWord_1306204
  simp only [CollatzResearch.WordTrace]
  refine ⟨23820586879926732363926833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31760782506568976485235777 23820586879926732363926833)
  ·
    refine ⟨17865440159945049272945125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23820586879926732363926833 17865440159945049272945125)
    ·
      refine ⟨3349770029989696738677211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17865440159945049272945125 3349770029989696738677211)
      ·
        refine ⟨5024655044984545108015817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349770029989696738677211 5024655044984545108015817)
        ·
          refine ⟨3768491283738408831011863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024655044984545108015817 3768491283738408831011863)
          ·
            refine ⟨5652736925607613246517795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768491283738408831011863 5652736925607613246517795)
            ·
              refine ⟨8479105388411419869776693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652736925607613246517795 8479105388411419869776693)
              ·
                refine ⟨794916130163570612791565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8479105388411419869776693 794916130163570612791565)
                ·
                  refine ⟨298093548811338979796837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794916130163570612791565 298093548811338979796837)
                  ·
                    rfl

theorem cell21_1306204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1306204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306204 prefixEnd_1306204 := by exact prefixLift 1306204
  have htrace : WordTrace (prefixWord ++ tailWord_1306204) baseStart_1306204 baseEnd_1306204 := by
    simpa [prefixWord, tailWord_1306204, baseEnd_1306204] using wordTrace_append hprefix tailTrace_1306204
  have hstable : (prefixWord ++ tailWord_1306204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306204).length < 2 ^ (prefixWord ++ tailWord_1306204).sum := by decide
  have hdescent : baseEnd_1306204 < baseStart_1306204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306218 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1306218 : Nat := 118140960795 + 1306218 * 2 ^ 59
def prefixEnd_1306218 : Nat := 4983230072969 + 3 ^ 40 * 1306218 * 2
def baseEnd_1306218 : Nat := 298096743802078066563475

theorem tailTrace_1306218 : CollatzResearch.WordTrace tailWord_1306218 prefixEnd_1306218 298096743802078066563475 := by
  unfold tailWord_1306218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11910421095450686279715827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31761122921201830079242205 11910421095450686279715827)
  ·
    refine ⟨17865631643176029419573741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11910421095450686279715827 17865631643176029419573741)
    ·
      refine ⟨6699611866191011032340153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17865631643176029419573741 6699611866191011032340153)
      ·
        refine ⟨5024708899643258274255115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6699611866191011032340153 5024708899643258274255115)
        ·
          refine ⟨7537063349464887411382673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024708899643258274255115 7537063349464887411382673)
          ·
            refine ⟨5652797512098665558537005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7537063349464887411382673 5652797512098665558537005)
            ·
              refine ⟨2119799067036999584451377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5652797512098665558537005 2119799067036999584451377)
              ·
                refine ⟨1589849300277749688338533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2119799067036999584451377 1589849300277749688338533)
                ·
                  refine ⟨298096743802078066563475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589849300277749688338533 298096743802078066563475)
                  ·
                    rfl

theorem cell21_1306218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1306218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306218 prefixEnd_1306218 := by exact prefixLift 1306218
  have htrace : WordTrace (prefixWord ++ tailWord_1306218) baseStart_1306218 baseEnd_1306218 := by
    simpa [prefixWord, tailWord_1306218, baseEnd_1306218] using wordTrace_append hprefix tailTrace_1306218
  have hstable : (prefixWord ++ tailWord_1306218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306218).length < 2 ^ (prefixWord ++ tailWord_1306218).sum := by decide
  have hdescent : baseEnd_1306218 < baseStart_1306218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306291 : List Nat := [1, 1, 1, 2, 3, 3, 4, 6]
def baseStart_1306291 : Nat := 118140960795 + 1306291 * 2 ^ 59
def prefixEnd_1306291 : Nat := 4983230072969 + 3 ^ 40 * 1306291 * 2
def baseEnd_1306291 : Nat := 99371134465548720615553

theorem tailTrace_1306291 : CollatzResearch.WordTrace tailWord_1306291 prefixEnd_1306291 99371134465548720615553 := by
  unfold tailWord_1306291
  simp only [CollatzResearch.WordTrace]
  refine ⟨47644346910538278586270727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31762897940358852390847151 47644346910538278586270727)
  ·
    refine ⟨71466520365807417879406091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47644346910538278586270727 71466520365807417879406091)
    ·
      refine ⟨107199780548711126819109137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71466520365807417879406091 107199780548711126819109137)
      ·
        refine ⟨80399835411533345114331853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107199780548711126819109137 80399835411533345114331853)
        ·
          refine ⟨30149938279325004417874445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80399835411533345114331853 30149938279325004417874445)
          ·
            refine ⟨11306226854746876656702917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30149938279325004417874445 11306226854746876656702917)
            ·
              refine ⟨2119917535265039373131797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11306226854746876656702917 2119917535265039373131797)
              ·
                refine ⟨99371134465548720615553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2119917535265039373131797 99371134465548720615553)
                ·
                  rfl

theorem cell21_1306291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_1306291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306291 prefixEnd_1306291 := by exact prefixLift 1306291
  have htrace : WordTrace (prefixWord ++ tailWord_1306291) baseStart_1306291 baseEnd_1306291 := by
    simpa [prefixWord, tailWord_1306291, baseEnd_1306291] using wordTrace_append hprefix tailTrace_1306291
  have hstable : (prefixWord ++ tailWord_1306291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306291).length < 2 ^ (prefixWord ++ tailWord_1306291).sum := by decide
  have hdescent : baseEnd_1306291 < baseStart_1306291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306336 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_1306336 : Nat := 118140960795 + 1306336 * 2 ^ 59
def prefixEnd_1306336 : Nat := 4983230072969 + 3 ^ 40 * 1306336 * 2
def baseEnd_1306336 : Nat := 298123673009736083596567

theorem tailTrace_1306336 : CollatzResearch.WordTrace tailWord_1306336 prefixEnd_1306336 298123673009736083596567 := by
  unfold tailWord_1306336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23822994097687625635829431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31763992130250167514439241 23822994097687625635829431)
  ·
    refine ⟨35734491146531438453744147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23822994097687625635829431 35734491146531438453744147)
    ·
      refine ⟨53601736719797157680616221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35734491146531438453744147 53601736719797157680616221)
      ·
        refine ⟨20100651269923934130231083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53601736719797157680616221 20100651269923934130231083)
        ·
          refine ⟨30150976904885901195346625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20100651269923934130231083 30150976904885901195346625)
          ·
            refine ⟨22613232678664425896509969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30150976904885901195346625 22613232678664425896509969)
            ·
              refine ⟨16959924508998319422382477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22613232678664425896509969 16959924508998319422382477)
              ·
                refine ⟨6359971690874369783393429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16959924508998319422382477 6359971690874369783393429)
                ·
                  refine ⟨298123673009736083596567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6359971690874369783393429 298123673009736083596567)
                  ·
                    rfl

theorem cell21_1306336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_1306336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306336 prefixEnd_1306336 := by exact prefixLift 1306336
  have htrace : WordTrace (prefixWord ++ tailWord_1306336) baseStart_1306336 baseEnd_1306336 := by
    simpa [prefixWord, tailWord_1306336, baseEnd_1306336] using wordTrace_append hprefix tailTrace_1306336
  have hstable : (prefixWord ++ tailWord_1306336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306336).length < 2 ^ (prefixWord ++ tailWord_1306336).sum := by decide
  have hdescent : baseEnd_1306336 < baseStart_1306336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306353 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1306353 : Nat := 118140960795 + 1306353 * 2 ^ 59
def prefixEnd_1306353 : Nat := 4983230072969 + 3 ^ 40 * 1306353 * 2
def baseEnd_1306353 : Nat := 298127552641347831813199

theorem tailTrace_1306353 : CollatzResearch.WordTrace tailWord_1306353 prefixEnd_1306353 298127552641347831813199 := by
  unfold tailWord_1306353
  simp only [CollatzResearch.WordTrace]
  refine ⟨47646608236313663175027713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31764405490875775450018475 47646608236313663175027713)
  ·
    refine ⟨35734956177235247381270785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47646608236313663175027713 35734956177235247381270785)
    ·
      refine ⟨26801217132926435535953089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35734956177235247381270785 26801217132926435535953089)
      ·
        refine ⟨20100912849694826651964817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26801217132926435535953089 20100912849694826651964817)
        ·
          refine ⟨15075684637271119988973613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20100912849694826651964817 15075684637271119988973613)
          ·
            refine ⟨5653381738976669995865105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15075684637271119988973613 5653381738976669995865105)
            ·
              refine ⟨4240036304232502496898829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5653381738976669995865105 4240036304232502496898829)
              ·
                refine ⟨1590013614087188436337061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4240036304232502496898829 1590013614087188436337061)
                ·
                  refine ⟨298127552641347831813199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590013614087188436337061 298127552641347831813199)
                  ·
                    rfl

theorem cell21_1306353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1306353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306353 prefixEnd_1306353 := by exact prefixLift 1306353
  have htrace : WordTrace (prefixWord ++ tailWord_1306353) baseStart_1306353 baseEnd_1306353 := by
    simpa [prefixWord, tailWord_1306353, baseEnd_1306353] using wordTrace_append hprefix tailTrace_1306353
  have hstable : (prefixWord ++ tailWord_1306353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306353).length < 2 ^ (prefixWord ++ tailWord_1306353).sum := by decide
  have hdescent : baseEnd_1306353 < baseStart_1306353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306356 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1306356 : Nat := 118140960795 + 1306356 * 2 ^ 59
def prefixEnd_1306356 : Nat := 4983230072969 + 3 ^ 40 * 1306356 * 2
def baseEnd_1306356 : Nat := 298128237282220493263193

theorem tailTrace_1306356 : CollatzResearch.WordTrace tailWord_1306356 prefixEnd_1306356 298128237282220493263193 := by
  unfold tailWord_1306356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23823358827651397343693461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31764478436868529791591281 23823358827651397343693461)
  ·
    refine ⟨1116719945046159250485631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23823358827651397343693461 1116719945046159250485631)
    ·
      refine ⟨1675079917569238875728447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116719945046159250485631 1675079917569238875728447)
      ·
        refine ⟨2512619876353858313592671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675079917569238875728447 2512619876353858313592671)
        ·
          refine ⟨3768929814530787470389007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512619876353858313592671 3768929814530787470389007)
          ·
            refine ⟨5653394721796181205583511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768929814530787470389007 5653394721796181205583511)
            ·
              refine ⟨8480092082694271808375267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653394721796181205583511 8480092082694271808375267)
              ·
                refine ⟨12720138124041407712562901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8480092082694271808375267 12720138124041407712562901)
                ·
                  refine ⟨298128237282220493263193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12720138124041407712562901 298128237282220493263193)
                  ·
                    rfl

theorem cell21_1306356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1306356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306356 prefixEnd_1306356 := by exact prefixLift 1306356
  have htrace : WordTrace (prefixWord ++ tailWord_1306356) baseStart_1306356 baseEnd_1306356 := by
    simpa [prefixWord, tailWord_1306356, baseEnd_1306356] using wordTrace_append hprefix tailTrace_1306356
  have hstable : (prefixWord ++ tailWord_1306356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306356).length < 2 ^ (prefixWord ++ tailWord_1306356).sum := by decide
  have hdescent : baseEnd_1306356 < baseStart_1306356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306429 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_1306429 : Nat := 118140960795 + 1306429 * 2 ^ 59
def prefixEnd_1306429 : Nat := 4983230072969 + 3 ^ 40 * 1306429 * 2
def baseEnd_1306429 : Nat := 298144896876788588546377

theorem tailTrace_1306429 : CollatzResearch.WordTrace tailWord_1306429 prefixEnd_1306429 298144896876788588546377 := by
  unfold tailWord_1306429
  simp only [CollatzResearch.WordTrace]
  refine ⟨47649380184038328154794341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31766253456025552103196227 47649380184038328154794341)
  ·
    refine ⟨8934258784507186529023939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47649380184038328154794341 8934258784507186529023939)
    ·
      refine ⟨13401388176760779793535909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8934258784507186529023939 13401388176760779793535909)
      ·
        refine ⟨2512760283142646211287983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13401388176760779793535909 2512760283142646211287983)
        ·
          refine ⟨3769140424713969316931975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512760283142646211287983 3769140424713969316931975)
          ·
            refine ⟨5653710637070953975397963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769140424713969316931975 5653710637070953975397963)
            ·
              refine ⟨8480565955606430963096945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653710637070953975397963 8480565955606430963096945)
              ·
                refine ⟨6360424466704823222322709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8480565955606430963096945 6360424466704823222322709)
                ·
                  refine ⟨298144896876788588546377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6360424466704823222322709 298144896876788588546377)
                  ·
                    rfl

theorem cell21_1306429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_1306429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306429 prefixEnd_1306429 := by exact prefixLift 1306429
  have htrace : WordTrace (prefixWord ++ tailWord_1306429) baseStart_1306429 baseEnd_1306429 := by
    simpa [prefixWord, tailWord_1306429, baseEnd_1306429] using wordTrace_append hprefix tailTrace_1306429
  have hstable : (prefixWord ++ tailWord_1306429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306429).length < 2 ^ (prefixWord ++ tailWord_1306429).sum := by decide
  have hdescent : baseEnd_1306429 < baseStart_1306429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306505 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_1306505 : Nat := 118140960795 + 1306505 * 2 ^ 59
def prefixEnd_1306505 : Nat := 4983230072969 + 3 ^ 40 * 1306505 * 2
def baseEnd_1306505 : Nat := 298162241112229345279555

theorem tailTrace_1306505 : CollatzResearch.WordTrace tailWord_1306505 prefixEnd_1306505 298162241112229345279555 := by
  unfold tailWord_1306505
  simp only [CollatzResearch.WordTrace]
  refine ⟨47652152131762993134560969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31768101421175328756373979 47652152131762993134560969)
  ·
    refine ⟨35739114098822244850920727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47652152131762993134560969 35739114098822244850920727)
    ·
      refine ⟨53608671148233367276381091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35739114098822244850920727 53608671148233367276381091)
      ·
        refine ⟨80413006722350050914571637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53608671148233367276381091 80413006722350050914571637)
        ·
          refine ⟨7538719380220317273241091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80413006722350050914571637 7538719380220317273241091)
          ·
            refine ⟨11308079070330475909861637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7538719380220317273241091 11308079070330475909861637)
            ·
              refine ⟨2120264825686964233099057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11308079070330475909861637 2120264825686964233099057)
              ·
                refine ⟨1590198619265223174824293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120264825686964233099057 1590198619265223174824293)
                ·
                  refine ⟨298162241112229345279555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590198619265223174824293 298162241112229345279555)
                  ·
                    rfl

theorem cell21_1306505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_1306505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306505 prefixEnd_1306505 := by exact prefixLift 1306505
  have htrace : WordTrace (prefixWord ++ tailWord_1306505) baseStart_1306505 baseEnd_1306505 := by
    simpa [prefixWord, tailWord_1306505, baseEnd_1306505] using wordTrace_append hprefix tailTrace_1306505
  have hstable : (prefixWord ++ tailWord_1306505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306505).length < 2 ^ (prefixWord ++ tailWord_1306505).sum := by decide
  have hdescent : baseEnd_1306505 < baseStart_1306505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306519 : List Nat := [1, 1, 3, 3, 1, 3, 3, 6]
def baseStart_1306519 : Nat := 118140960795 + 1306519 * 2 ^ 59
def prefixEnd_1306519 : Nat := 4983230072969 + 3 ^ 40 * 1306519 * 2
def baseEnd_1306519 : Nat := 99388478700989477348731

theorem tailTrace_1306519 : CollatzResearch.WordTrace tailWord_1306519 prefixEnd_1306519 99388478700989477348731 := by
  unfold tailWord_1306519
  simp only [CollatzResearch.WordTrace]
  refine ⟨47652662753712273525570611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31768441835808182350380407 47652662753712273525570611)
  ·
    refine ⟨71478994130568410288355917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47652662753712273525570611 71478994130568410288355917)
    ·
      refine ⟨26804622798963153858133469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71478994130568410288355917 26804622798963153858133469)
      ·
        refine ⟨10051733549611182696800051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26804622798963153858133469 10051733549611182696800051)
        ·
          refine ⟨15077600324416774045200077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051733549611182696800051 15077600324416774045200077)
          ·
            refine ⟨5654100121656290266950029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15077600324416774045200077 5654100121656290266950029)
            ·
              refine ⟨2120287545621108850106261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5654100121656290266950029 2120287545621108850106261)
              ·
                refine ⟨99388478700989477348731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2120287545621108850106261 99388478700989477348731)
                ·
                  rfl

theorem cell21_1306519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_1306519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306519 prefixEnd_1306519 := by exact prefixLift 1306519
  have htrace : WordTrace (prefixWord ++ tailWord_1306519) baseStart_1306519 baseEnd_1306519 := by
    simpa [prefixWord, tailWord_1306519, baseEnd_1306519] using wordTrace_append hprefix tailTrace_1306519
  have hstable : (prefixWord ++ tailWord_1306519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306519).length < 2 ^ (prefixWord ++ tailWord_1306519).sum := by decide
  have hdescent : baseEnd_1306519 < baseStart_1306519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306556 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1306556 : Nat := 118140960795 + 1306556 * 2 ^ 59
def prefixEnd_1306556 : Nat := 4983230072969 + 3 ^ 40 * 1306556 * 2
def baseEnd_1306556 : Nat := 298173880007064589929451

theorem tailTrace_1306556 : CollatzResearch.WordTrace tailWord_1306556 prefixEnd_1306556 298173880007064589929451 := by
  unfold tailWord_1306556
  simp only [CollatzResearch.WordTrace]
  refine ⟨23827006127289114422333761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31769341503052152563111681 23827006127289114422333761)
  ·
    refine ⟨17870254595466835816750321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23827006127289114422333761 17870254595466835816750321)
    ·
      refine ⟨13402690946600126862562741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17870254595466835816750321 13402690946600126862562741)
      ·
        refine ⟨1256502276243761893365257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13402690946600126862562741 1256502276243761893365257)
        ·
          refine ⟨942376707182821420023943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256502276243761893365257 942376707182821420023943)
          ·
            refine ⟨1413565060774232130035915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942376707182821420023943 1413565060774232130035915)
            ·
              refine ⟨2120347591161348195053873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413565060774232130035915 2120347591161348195053873)
              ·
                refine ⟨1590260693371011146290405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120347591161348195053873 1590260693371011146290405)
                ·
                  refine ⟨298173880007064589929451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590260693371011146290405 298173880007064589929451)
                  ·
                    rfl

theorem cell21_1306556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1306556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306556 prefixEnd_1306556 := by exact prefixLift 1306556
  have htrace : WordTrace (prefixWord ++ tailWord_1306556) baseStart_1306556 baseEnd_1306556 := by
    simpa [prefixWord, tailWord_1306556, baseEnd_1306556] using wordTrace_append hprefix tailTrace_1306556
  have hstable : (prefixWord ++ tailWord_1306556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306556).length < 2 ^ (prefixWord ++ tailWord_1306556).sum := by decide
  have hdescent : baseEnd_1306556 < baseStart_1306556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306595 : List Nat := [1, 1, 1, 6, 1, 3, 1, 7]
def baseStart_1306595 : Nat := 118140960795 + 1306595 * 2 ^ 59
def prefixEnd_1306595 : Nat := 4983230072969 + 3 ^ 40 * 1306595 * 2
def baseEnd_1306595 : Nat := 99394260112803062926457

theorem tailTrace_1306595 : CollatzResearch.WordTrace tailWord_1306595 prefixEnd_1306595 99394260112803062926457 := by
  unfold tailWord_1306595
  simp only [CollatzResearch.WordTrace]
  refine ⟨47655434701436938505337239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31770289800957959003558159 47655434701436938505337239)
  ·
    refine ⟨71483152052155407758005859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47655434701436938505337239 71483152052155407758005859)
    ·
      refine ⟨107224728078233111637008789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71483152052155407758005859 107224728078233111637008789)
      ·
        refine ⟨5026159128667177107984787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107224728078233111637008789 5026159128667177107984787)
        ·
          refine ⟨7539238693000765661977181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026159128667177107984787 7539238693000765661977181)
          ·
            refine ⟨2827214509875287123241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7539238693000765661977181 2827214509875287123241443)
            ·
              refine ⟨4240821764812930684862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827214509875287123241443 4240821764812930684862165)
              ·
                refine ⟨99394260112803062926457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4240821764812930684862165 99394260112803062926457)
                ·
                  rfl

theorem cell21_1306595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_1306595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306595 prefixEnd_1306595 := by exact prefixLift 1306595
  have htrace : WordTrace (prefixWord ++ tailWord_1306595) baseStart_1306595 baseEnd_1306595 := by
    simpa [prefixWord, tailWord_1306595, baseEnd_1306595] using wordTrace_append hprefix tailTrace_1306595
  have hstable : (prefixWord ++ tailWord_1306595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306595).length < 2 ^ (prefixWord ++ tailWord_1306595).sum := by decide
  have hdescent : baseEnd_1306595 < baseStart_1306595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306640 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_1306640 : Nat := 118140960795 + 1306640 * 2 ^ 59
def prefixEnd_1306640 : Nat := 4983230072969 + 3 ^ 40 * 1306640 * 2
def baseEnd_1306640 : Nat := 298193049951499110529279

theorem tailTrace_1306640 : CollatzResearch.WordTrace tailWord_1306640 prefixEnd_1306640 298193049951499110529279 := by
  unfold tailWord_1306640
  simp only [CollatzResearch.WordTrace]
  refine ⟨23828537993136955595362687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31771383990849274127150249 23828537993136955595362687)
  ·
    refine ⟨35742806989705433393044031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23828537993136955595362687 35742806989705433393044031)
    ·
      refine ⟨53614210484558150089566047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35742806989705433393044031 53614210484558150089566047)
      ·
        refine ⟨80421315726837225134349071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53614210484558150089566047 80421315726837225134349071)
        ·
          refine ⟨120631973590255837701523607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80421315726837225134349071 120631973590255837701523607)
          ·
            refine ⟨180947960385383756552285411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120631973590255837701523607 180947960385383756552285411)
            ·
              refine ⟨271421940578075634828428117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180947960385383756552285411 271421940578075634828428117)
              ·
                refine ⟨1590362933074661922822821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 271421940578075634828428117 1590362933074661922822821)
                ·
                  refine ⟨298193049951499110529279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590362933074661922822821 298193049951499110529279)
                  ·
                    rfl

theorem cell21_1306640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_1306640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306640 prefixEnd_1306640 := by exact prefixLift 1306640
  have htrace : WordTrace (prefixWord ++ tailWord_1306640) baseStart_1306640 baseEnd_1306640 := by
    simpa [prefixWord, tailWord_1306640, baseEnd_1306640] using wordTrace_append hprefix tailTrace_1306640
  have hstable : (prefixWord ++ tailWord_1306640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306640).length < 2 ^ (prefixWord ++ tailWord_1306640).sum := by decide
  have hdescent : baseEnd_1306640 < baseStart_1306640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306702 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1306702 : Nat := 118140960795 + 1306702 * 2 ^ 59
def prefixEnd_1306702 : Nat := 4983230072969 + 3 ^ 40 * 1306702 * 2
def baseEnd_1306702 : Nat := 298207199196200780495819

theorem tailTrace_1306702 : CollatzResearch.WordTrace tailWord_1306702 prefixEnd_1306702 298207199196200780495819 := by
  unfold tailWord_1306702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957417164006161972435295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31772891541366197186321573 5957417164006161972435295)
  ·
    refine ⟨8936125746009242958652943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5957417164006161972435295 8936125746009242958652943)
    ·
      refine ⟨13404188619013864437979415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936125746009242958652943 13404188619013864437979415)
      ·
        refine ⟨20106282928520796656969123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13404188619013864437979415 20106282928520796656969123)
        ·
          refine ⟨30159424392781194985453685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20106282928520796656969123 30159424392781194985453685)
          ·
            refine ⟨2827446036823237029886283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30159424392781194985453685 2827446036823237029886283)
            ·
              refine ⟨4241169055234855544829425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827446036823237029886283 4241169055234855544829425)
              ·
                refine ⟨3180876791426141658622069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241169055234855544829425 3180876791426141658622069)
                ·
                  refine ⟨298207199196200780495819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180876791426141658622069 298207199196200780495819)
                  ·
                    rfl

theorem cell21_1306702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1306702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306702 prefixEnd_1306702 := by exact prefixLift 1306702
  have htrace : WordTrace (prefixWord ++ tailWord_1306702) baseStart_1306702 baseEnd_1306702 := by
    simpa [prefixWord, tailWord_1306702, baseEnd_1306702] using wordTrace_append hprefix tailTrace_1306702
  have hstable : (prefixWord ++ tailWord_1306702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306702).length < 2 ^ (prefixWord ++ tailWord_1306702).sum := by decide
  have hdescent : baseEnd_1306702 < baseStart_1306702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306761 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_1306761 : Nat := 118140960795 + 1306761 * 2 ^ 59
def prefixEnd_1306761 : Nat := 4983230072969 + 3 ^ 40 * 1306761 * 2
def baseEnd_1306761 : Nat := 298220663800029789012365

theorem tailTrace_1306761 : CollatzResearch.WordTrace tailWord_1306761 prefixEnd_1306761 298220663800029789012365 := by
  unfold tailWord_1306761
  simp only [CollatzResearch.WordTrace]
  refine ⟨47661489218835548855880137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31774326145890365903920091 47661489218835548855880137)
  ·
    refine ⟨35746116914126661641910103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47661489218835548855880137 35746116914126661641910103)
    ·
      refine ⟨53619175371189992462865155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35746116914126661641910103 53619175371189992462865155)
      ·
        refine ⟨80428763056784988694297733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53619175371189992462865155 80428763056784988694297733)
        ·
          refine ⟨15080393073147185380180825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80428763056784988694297733 15080393073147185380180825)
          ·
            refine ⟨11310294804860389035135619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15080393073147185380180825 11310294804860389035135619)
            ·
              refine ⟨16965442207290583552703429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11310294804860389035135619 16965442207290583552703429)
              ·
                refine ⟨3181020413866984416131893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16965442207290583552703429 3181020413866984416131893)
                ·
                  refine ⟨298220663800029789012365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181020413866984416131893 298220663800029789012365)
                  ·
                    rfl

theorem cell21_1306761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_1306761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306761 prefixEnd_1306761 := by exact prefixLift 1306761
  have htrace : WordTrace (prefixWord ++ tailWord_1306761) baseStart_1306761 baseEnd_1306761 := by
    simpa [prefixWord, tailWord_1306761, baseEnd_1306761] using wordTrace_append hprefix tailTrace_1306761
  have hstable : (prefixWord ++ tailWord_1306761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306761).length < 2 ^ (prefixWord ++ tailWord_1306761).sum := by decide
  have hdescent : baseEnd_1306761 < baseStart_1306761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306913 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_1306913 : Nat := 118140960795 + 1306913 * 2 ^ 59
def prefixEnd_1306913 : Nat := 4983230072969 + 3 ^ 40 * 1306913 * 2
def baseEnd_1306913 : Nat := 298255352270911302478721

theorem tailTrace_1306913 : CollatzResearch.WordTrace tailWord_1306913 prefixEnd_1306913 298255352270911302478721 := by
  unfold tailWord_1306913
  simp only [CollatzResearch.WordTrace]
  refine ⟨47667033114284878815413393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31778022076189919210275595 47667033114284878815413393)
  ·
    refine ⟨35750274835713659111560045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47667033114284878815413393 35750274835713659111560045)
    ·
      refine ⟨13406353063392622166835017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35750274835713659111560045 13406353063392622166835017)
      ·
        refine ⟨10054764797544466625126263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13406353063392622166835017 10054764797544466625126263)
        ·
          refine ⟨15082147196316699937689395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054764797544466625126263 15082147196316699937689395)
          ·
            refine ⟨22623220794475049906534093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15082147196316699937689395 22623220794475049906534093)
            ·
              refine ⟨8483707797928143714950285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22623220794475049906534093 8483707797928143714950285)
              ·
                refine ⟨3181390424223053893106357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8483707797928143714950285 3181390424223053893106357)
                ·
                  refine ⟨298255352270911302478721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181390424223053893106357 298255352270911302478721)
                  ·
                    rfl

theorem cell21_1306913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_1306913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306913 prefixEnd_1306913 := by exact prefixLift 1306913
  have htrace : WordTrace (prefixWord ++ tailWord_1306913) baseStart_1306913 baseEnd_1306913 := by
    simpa [prefixWord, tailWord_1306913, baseEnd_1306913] using wordTrace_append hprefix tailTrace_1306913
  have hstable : (prefixWord ++ tailWord_1306913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306913).length < 2 ^ (prefixWord ++ tailWord_1306913).sum := by decide
  have hdescent : baseEnd_1306913 < baseStart_1306913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306964 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1306964 : Nat := 118140960795 + 1306964 * 2 ^ 59
def prefixEnd_1306964 : Nat := 4983230072969 + 3 ^ 40 * 1306964 * 2
def baseEnd_1306964 : Nat := 298266991165746547128617

theorem tailTrace_1306964 : CollatzResearch.WordTrace tailWord_1306964 prefixEnd_1306964 298266991165746547128617 := by
  unfold tailWord_1306964
  simp only [CollatzResearch.WordTrace]
  refine ⟨23834446618550057262759973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31779262158066743017013297 23834446618550057262759973)
  ·
    refine ⟨4468958740978135736767495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23834446618550057262759973 4468958740978135736767495)
    ·
      refine ⟨6703438111467203605151243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4468958740978135736767495 6703438111467203605151243)
      ·
        refine ⟨10055157167200805407726865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703438111467203605151243 10055157167200805407726865)
        ·
          refine ⟨7541367875400604055795149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10055157167200805407726865 7541367875400604055795149)
          ·
            refine ⟨2828012953275226520923181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7541367875400604055795149 2828012953275226520923181)
            ·
              refine ⟨1060504857478209945346193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2828012953275226520923181 1060504857478209945346193)
              ·
                refine ⟨795378643108657459009645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060504857478209945346193 795378643108657459009645)
                ·
                  refine ⟨298266991165746547128617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795378643108657459009645 298266991165746547128617)
                  ·
                    rfl

theorem cell21_1306964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1306964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306964 prefixEnd_1306964 := by exact prefixLift 1306964
  have htrace : WordTrace (prefixWord ++ tailWord_1306964) baseStart_1306964 baseEnd_1306964 := by
    simpa [prefixWord, tailWord_1306964, baseEnd_1306964] using wordTrace_append hprefix tailTrace_1306964
  have hstable : (prefixWord ++ tailWord_1306964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306964).length < 2 ^ (prefixWord ++ tailWord_1306964).sum := by decide
  have hdescent : baseEnd_1306964 < baseStart_1306964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306978 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1306978 : Nat := 118140960795 + 1306978 * 2 ^ 59
def prefixEnd_1306978 : Nat := 4983230072969 + 3 ^ 40 * 1306978 * 2
def baseEnd_1306978 : Nat := 298270186156485633895255

theorem tailTrace_1306978 : CollatzResearch.WordTrace tailWord_1306978 prefixEnd_1306978 298270186156485633895255 := by
  unfold tailWord_1306978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11917350964762348729132397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31779602572699596611019725 11917350964762348729132397)
  ·
    refine ⟨4469006611785880773424649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11917350964762348729132397 4469006611785880773424649)
    ·
      refine ⟨3351754958839410580068487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4469006611785880773424649 3351754958839410580068487)
      ·
        refine ⟨5027632438259115870102731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351754958839410580068487 5027632438259115870102731)
        ·
          refine ⟨7541448657388673805154097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027632438259115870102731 7541448657388673805154097)
          ·
            refine ⟨5656086493041505353865573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7541448657388673805154097 5656086493041505353865573)
            ·
              refine ⟨1060516217445282253849795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5656086493041505353865573 1060516217445282253849795)
              ·
                refine ⟨1590774326167923380774693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060516217445282253849795 1590774326167923380774693)
                ·
                  refine ⟨298270186156485633895255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590774326167923380774693 298270186156485633895255)
                  ·
                    rfl

theorem cell21_1306978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1306978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306978 prefixEnd_1306978 := by exact prefixLift 1306978
  have htrace : WordTrace (prefixWord ++ tailWord_1306978) baseStart_1306978 baseEnd_1306978 := by
    simpa [prefixWord, tailWord_1306978, baseEnd_1306978] using wordTrace_append hprefix tailTrace_1306978
  have hstable : (prefixWord ++ tailWord_1306978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306978).length < 2 ^ (prefixWord ++ tailWord_1306978).sum := by decide
  have hdescent : baseEnd_1306978 < baseStart_1306978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306989 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1306989 : Nat := 118140960795 + 1306989 * 2 ^ 59
def prefixEnd_1306989 : Nat := 4983230072969 + 3 ^ 40 * 1306989 * 2
def baseEnd_1306989 : Nat := 298272696506352059211899

theorem tailTrace_1306989 : CollatzResearch.WordTrace tailWord_1306989 prefixEnd_1306989 298272696506352059211899 := by
  unfold tailWord_1306989
  simp only [CollatzResearch.WordTrace]
  refine ⟨47669805062009543795180021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31779870041339695863453347 47669805062009543795180021)
  ·
    refine ⟨4469044224563394730798127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47669805062009543795180021 4469044224563394730798127)
    ·
      refine ⟨6703566336845092096197191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469044224563394730798127 6703566336845092096197191)
      ·
        refine ⟨10055349505267638144295787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703566336845092096197191 10055349505267638144295787)
        ·
          refine ⟨15083024257901457216443681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10055349505267638144295787 15083024257901457216443681)
          ·
            refine ⟨11312268193426092912332761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15083024257901457216443681 11312268193426092912332761)
            ·
              refine ⟨8484201145069569684249571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11312268193426092912332761 8484201145069569684249571)
              ·
                refine ⟨12726301717604354526374357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8484201145069569684249571 12726301717604354526374357)
                ·
                  refine ⟨298272696506352059211899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12726301717604354526374357 298272696506352059211899)
                  ·
                    rfl

theorem cell21_1306989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1306989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1306989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1306989 prefixEnd_1306989 := by exact prefixLift 1306989
  have htrace : WordTrace (prefixWord ++ tailWord_1306989) baseStart_1306989 baseEnd_1306989 := by
    simpa [prefixWord, tailWord_1306989, baseEnd_1306989] using wordTrace_append hprefix tailTrace_1306989
  have hstable : (prefixWord ++ tailWord_1306989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306989).length < 2 ^ (prefixWord ++ tailWord_1306989).sum := by decide
  have hdescent : baseEnd_1306989 < baseStart_1306989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307020 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1307020 : Nat := 118140960795 + 1307020 * 2 ^ 59
def prefixEnd_1307020 : Nat := 4983230072969 + 3 ^ 40 * 1307020 * 2
def baseEnd_1307020 : Nat := 298279771128702894195169

theorem tailTrace_1307020 : CollatzResearch.WordTrace tailWord_1307020 prefixEnd_1307020 298279771128702894195169 := by
  unfold tailWord_1307020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23835467862448618044779257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31780623816598157393039009 23835467862448618044779257)
  ·
    refine ⟨17876600896836463533584443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23835467862448618044779257 17876600896836463533584443)
    ·
      refine ⟨26814901345254695300376665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17876600896836463533584443 26814901345254695300376665)
      ·
        refine ⟨20111176008941021475282499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26814901345254695300376665 20111176008941021475282499)
        ·
          refine ⟨30166764013411532212923749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20111176008941021475282499 30166764013411532212923749)
          ·
            refine ⟨5656268252514662289923203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30166764013411532212923749 5656268252514662289923203)
            ·
              refine ⟨8484402378771993434884805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656268252514662289923203 8484402378771993434884805)
              ·
                refine ⟨1590825446019748769040901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8484402378771993434884805 1590825446019748769040901)
                ·
                  refine ⟨298279771128702894195169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590825446019748769040901 298279771128702894195169)
                  ·
                    rfl

theorem cell21_1307020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1307020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307020 prefixEnd_1307020 := by exact prefixLift 1307020
  have htrace : WordTrace (prefixWord ++ tailWord_1307020) baseStart_1307020 baseEnd_1307020 := by
    simpa [prefixWord, tailWord_1307020, baseEnd_1307020] using wordTrace_append hprefix tailTrace_1307020
  have hstable : (prefixWord ++ tailWord_1307020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307020).length < 2 ^ (prefixWord ++ tailWord_1307020).sum := by decide
  have hdescent : baseEnd_1307020 < baseStart_1307020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307082 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_1307082 : Nat := 118140960795 + 1307082 * 2 ^ 59
def prefixEnd_1307082 : Nat := 4983230072969 + 3 ^ 40 * 1307082 * 2
def baseEnd_1307082 : Nat := 298293920373404564161709

theorem tailTrace_1307082 : CollatzResearch.WordTrace tailWord_1307082 prefixEnd_1307082 298293920373404564161709 := by
  unfold tailWord_1307082
  simp only [CollatzResearch.WordTrace]
  refine ⟨11918299262668155169578875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31782131367115080452210333 11918299262668155169578875)
  ·
    refine ⟨17877448894002232754368313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11918299262668155169578875 17877448894002232754368313)
    ·
      refine ⟨13408086670501674565776235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17877448894002232754368313 13408086670501674565776235)
      ·
        refine ⟨20112130005752511848664353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13408086670501674565776235 20112130005752511848664353)
        ·
          refine ⟨15084097504314383886498265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20112130005752511848664353 15084097504314383886498265)
          ·
            refine ⟨11313073128235787914873699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15084097504314383886498265 11313073128235787914873699)
            ·
              refine ⟨16969609692353681872310549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11313073128235787914873699 16969609692353681872310549)
              ·
                refine ⟨795450454329078837764557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16969609692353681872310549 795450454329078837764557)
                ·
                  refine ⟨298293920373404564161709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795450454329078837764557 298293920373404564161709)
                  ·
                    rfl

theorem cell21_1307082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_1307082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307082 prefixEnd_1307082 := by exact prefixLift 1307082
  have htrace : WordTrace (prefixWord ++ tailWord_1307082) baseStart_1307082 baseEnd_1307082 := by
    simpa [prefixWord, tailWord_1307082, baseEnd_1307082] using wordTrace_append hprefix tailTrace_1307082
  have hstable : (prefixWord ++ tailWord_1307082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307082).length < 2 ^ (prefixWord ++ tailWord_1307082).sum := by decide
  have hdescent : baseEnd_1307082 < baseStart_1307082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307141 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_1307141 : Nat := 118140960795 + 1307141 * 2 ^ 59
def prefixEnd_1307141 : Nat := 4983230072969 + 3 ^ 40 * 1307141 * 2
def baseEnd_1307141 : Nat := 298307384977233572678255

theorem tailTrace_1307141 : CollatzResearch.WordTrace tailWord_1307141 prefixEnd_1307141 298307384977233572678255 := by
  unfold tailWord_1307141
  simp only [CollatzResearch.WordTrace]
  refine ⟨47675348957458873754713277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31783565971639249169808851 47675348957458873754713277)
  ·
    refine ⟨17878255859047077658017479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47675348957458873754713277 17878255859047077658017479)
    ·
      refine ⟨26817383788570616487026219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17878255859047077658017479 26817383788570616487026219)
      ·
        refine ⟨40226075682855924730539329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26817383788570616487026219 40226075682855924730539329)
        ·
          refine ⟨30169556762141943547904497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40226075682855924730539329 30169556762141943547904497)
          ·
            refine ⟨22627167571606457660928373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30169556762141943547904497 22627167571606457660928373)
            ·
              refine ⟨2121296959838105405712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22627167571606457660928373 2121296959838105405712035)
              ·
                refine ⟨3181945439757158108568053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121296959838105405712035 3181945439757158108568053)
                ·
                  refine ⟨298307384977233572678255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181945439757158108568053 298307384977233572678255)
                  ·
                    rfl

theorem cell21_1307141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_1307141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307141 prefixEnd_1307141 := by exact prefixLift 1307141
  have htrace : WordTrace (prefixWord ++ tailWord_1307141) baseStart_1307141 baseEnd_1307141 := by
    simpa [prefixWord, tailWord_1307141, baseEnd_1307141] using wordTrace_append hprefix tailTrace_1307141
  have hstable : (prefixWord ++ tailWord_1307141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307141).length < 2 ^ (prefixWord ++ tailWord_1307141).sum := by decide
  have hdescent : baseEnd_1307141 < baseStart_1307141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307206 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1307206 : Nat := 118140960795 + 1307206 * 2 ^ 59
def prefixEnd_1307206 : Nat := 4983230072969 + 3 ^ 40 * 1307206 * 2
def baseEnd_1307206 : Nat := 298322218862807904094789

theorem tailTrace_1307206 : CollatzResearch.WordTrace tailWord_1307206 prefixEnd_1307206 298322218862807904094789 := by
  unfold tailWord_1307206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489928740694480932994671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31785146468148926570552981 1489928740694480932994671)
  ·
    refine ⟨2234893111041721399492007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489928740694480932994671 2234893111041721399492007)
    ·
      refine ⟨3352339666562582099238011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234893111041721399492007 3352339666562582099238011)
      ·
        refine ⟨5028509499843873148857017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352339666562582099238011 5028509499843873148857017)
        ·
          refine ⟨3771382124882904861642763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5028509499843873148857017 3771382124882904861642763)
          ·
            refine ⟨5657073187324357292464145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771382124882904861642763 5657073187324357292464145)
            ·
              refine ⟨4242804890493267969348109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657073187324357292464145 4242804890493267969348109)
              ·
                refine ⟨1591051833934975488505541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4242804890493267969348109 1591051833934975488505541)
                ·
                  refine ⟨298322218862807904094789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591051833934975488505541 298322218862807904094789)
                  ·
                    rfl

theorem cell21_1307206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1307206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307206 prefixEnd_1307206 := by exact prefixLift 1307206
  have htrace : WordTrace (prefixWord ++ tailWord_1307206) baseStart_1307206 baseEnd_1307206 := by
    simpa [prefixWord, tailWord_1307206, baseEnd_1307206] using wordTrace_append hprefix tailTrace_1307206
  have hstable : (prefixWord ++ tailWord_1307206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307206).length < 2 ^ (prefixWord ++ tailWord_1307206).sum := by decide
  have hdescent : baseEnd_1307206 < baseStart_1307206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307217 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1307217 : Nat := 118140960795 + 1307217 * 2 ^ 59
def prefixEnd_1307217 : Nat := 4983230072969 + 3 ^ 40 * 1307217 * 2
def baseEnd_1307217 : Nat := 298324729212674329411433

theorem tailTrace_1307217 : CollatzResearch.WordTrace tailWord_1307217 prefixEnd_1307217 298324729212674329411433 := by
  unfold tailWord_1307217
  simp only [CollatzResearch.WordTrace]
  refine ⟨47678120905183538734479905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31785413936789025822986603 47678120905183538734479905)
  ·
    refine ⟨35758590678887654050859929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47678120905183538734479905 35758590678887654050859929)
    ·
      refine ⟨26818943009165740538144947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35758590678887654050859929 26818943009165740538144947)
      ·
        refine ⟨40228414513748610807217421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26818943009165740538144947 40228414513748610807217421)
        ·
          refine ⟨15085655442655729052706533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40228414513748610807217421 15085655442655729052706533)
          ·
            refine ⟨2828560395497949197382475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15085655442655729052706533 2828560395497949197382475)
            ·
              refine ⟨4242840593246923796073713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828560395497949197382475 4242840593246923796073713)
              ·
                refine ⟨3182130444935192847055285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4242840593246923796073713 3182130444935192847055285)
                ·
                  refine ⟨298324729212674329411433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3182130444935192847055285 298324729212674329411433)
                  ·
                    rfl

theorem cell21_1307217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1307217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307217 prefixEnd_1307217 := by exact prefixLift 1307217
  have htrace : WordTrace (prefixWord ++ tailWord_1307217) baseStart_1307217 baseEnd_1307217 := by
    simpa [prefixWord, tailWord_1307217, baseEnd_1307217] using wordTrace_append hprefix tailTrace_1307217
  have hstable : (prefixWord ++ tailWord_1307217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307217).length < 2 ^ (prefixWord ++ tailWord_1307217).sum := by decide
  have hdescent : baseEnd_1307217 < baseStart_1307217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307248 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_1307248 : Nat := 118140960795 + 1307248 * 2 ^ 59
def prefixEnd_1307248 : Nat := 4983230072969 + 3 ^ 40 * 1307248 * 2
def baseEnd_1307248 : Nat := 298331803835025164394703

theorem tailTrace_1307248 : CollatzResearch.WordTrace tailWord_1307248 prefixEnd_1307248 298331803835025164394703 := by
  unfold tailWord_1307248
  simp only [CollatzResearch.WordTrace]
  refine ⟨23839625784035615514429199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31786167712047487352572265 23839625784035615514429199)
  ·
    refine ⟨35759438676053423271643799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23839625784035615514429199 35759438676053423271643799)
    ·
      refine ⟨53639158014080134907465699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35759438676053423271643799 53639158014080134907465699)
      ·
        refine ⟨80458737021120202361198549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53639158014080134907465699 80458737021120202361198549)
        ·
          refine ⟨1885751648932504742840591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80458737021120202361198549 1885751648932504742840591)
          ·
            refine ⟨2828627473398757114260887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885751648932504742840591 2828627473398757114260887)
            ·
              refine ⟨4242941210098135671391331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828627473398757114260887 4242941210098135671391331)
              ·
                refine ⟨6364411815147203507086997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242941210098135671391331 6364411815147203507086997)
                ·
                  refine ⟨298331803835025164394703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6364411815147203507086997 298331803835025164394703)
                  ·
                    rfl

theorem cell21_1307248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_1307248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307248 prefixEnd_1307248 := by exact prefixLift 1307248
  have htrace : WordTrace (prefixWord ++ tailWord_1307248) baseStart_1307248 baseEnd_1307248 := by
    simpa [prefixWord, tailWord_1307248, baseEnd_1307248] using wordTrace_append hprefix tailTrace_1307248
  have hstable : (prefixWord ++ tailWord_1307248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307248).length < 2 ^ (prefixWord ++ tailWord_1307248).sum := by decide
  have hdescent : baseEnd_1307248 < baseStart_1307248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307265 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 4]
def baseStart_1307265 : Nat := 118140960795 + 1307265 * 2 ^ 59
def prefixEnd_1307265 : Nat := 4983230072969 + 3 ^ 40 * 1307265 * 2
def baseEnd_1307265 : Nat := 298335683466636912611335

theorem tailTrace_1307265 : CollatzResearch.WordTrace tailWord_1307265 prefixEnd_1307265 298335683466636912611335 := by
  unfold tailWord_1307265
  simp only [CollatzResearch.WordTrace]
  refine ⟨47679871609009642932227249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31786581072673095288151499 47679871609009642932227249)
  ·
    refine ⟨35759903706757232199170437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47679871609009642932227249 35759903706757232199170437)
    ·
      refine ⟨6704981945016981037344457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35759903706757232199170437 6704981945016981037344457)
      ·
        refine ⟨5028736458762735778008343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6704981945016981037344457 5028736458762735778008343)
        ·
          refine ⟨7543104688144103667012515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028736458762735778008343 7543104688144103667012515)
          ·
            refine ⟨11314657032216155500518773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543104688144103667012515 11314657032216155500518773)
            ·
              refine ⟨1060749096770264578173635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11314657032216155500518773 1060749096770264578173635)
              ·
                refine ⟨1591123645155396867260453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060749096770264578173635 1591123645155396867260453)
                ·
                  refine ⟨298335683466636912611335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591123645155396867260453 298335683466636912611335)
                  ·
                    rfl

theorem cell21_1307265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_1307265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307265 prefixEnd_1307265 := by exact prefixLift 1307265
  have htrace : WordTrace (prefixWord ++ tailWord_1307265) baseStart_1307265 baseEnd_1307265 := by
    simpa [prefixWord, tailWord_1307265, baseEnd_1307265] using wordTrace_append hprefix tailTrace_1307265
  have hstable : (prefixWord ++ tailWord_1307265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307265).length < 2 ^ (prefixWord ++ tailWord_1307265).sum := by decide
  have hdescent : baseEnd_1307265 < baseStart_1307265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307276 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1307276 : Nat := 118140960795 + 1307276 * 2 ^ 59
def prefixEnd_1307276 : Nat := 4983230072969 + 3 ^ 40 * 1307276 * 2
def baseEnd_1307276 : Nat := 298338193816503337927979

theorem tailTrace_1307276 : CollatzResearch.WordTrace tailWord_1307276 prefixEnd_1307276 298338193816503337927979 := by
  unfold tailWord_1307276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23840136405984895905438841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31786848541313194540585121 23840136405984895905438841)
  ·
    refine ⟨17880102304488671929079131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23840136405984895905438841 17880102304488671929079131)
    ·
      refine ⟨26820153456733007893618697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17880102304488671929079131 26820153456733007893618697)
      ·
        refine ⟨20115115092549755920214023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26820153456733007893618697 20115115092549755920214023)
        ·
          refine ⟨30172672638824633880321035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20115115092549755920214023 30172672638824633880321035)
          ·
            refine ⟨45259008958236950820481553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30172672638824633880321035 45259008958236950820481553)
            ·
              refine ⟨33944256718677713115361165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45259008958236950820481553 33944256718677713115361165)
              ·
                refine ⟨12729096269504142418260437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33944256718677713115361165 12729096269504142418260437)
                ·
                  refine ⟨298338193816503337927979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12729096269504142418260437 298338193816503337927979)
                  ·
                    rfl

theorem cell21_1307276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1307276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307276 prefixEnd_1307276 := by exact prefixLift 1307276
  have htrace : WordTrace (prefixWord ++ tailWord_1307276) baseStart_1307276 baseEnd_1307276 := by
    simpa [prefixWord, tailWord_1307276, baseEnd_1307276] using wordTrace_append hprefix tailTrace_1307276
  have hstable : (prefixWord ++ tailWord_1307276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307276).length < 2 ^ (prefixWord ++ tailWord_1307276).sum := by decide
  have hdescent : baseEnd_1307276 < baseStart_1307276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307324 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1307324 : Nat := 118140960795 + 1307324 * 2 ^ 59
def prefixEnd_1307324 : Nat := 4983230072969 + 3 ^ 40 * 1307324 * 2
def baseEnd_1307324 : Nat := 298349148070465921127881

theorem tailTrace_1307324 : CollatzResearch.WordTrace tailWord_1307324 prefixEnd_1307324 298349148070465921127881 := by
  unfold tailWord_1307324
  simp only [CollatzResearch.WordTrace]
  refine ⟨23841011757897948004312513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31788015677197264005750017 23841011757897948004312513)
  ·
    refine ⟨17880758818423461003234385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23841011757897948004312513 17880758818423461003234385)
    ·
      refine ⟨13410569113817595752425789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17880758818423461003234385 13410569113817595752425789)
      ·
        refine ⟨5028963417681598407159671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13410569113817595752425789 5028963417681598407159671)
        ·
          refine ⟨7543445126522397610739507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028963417681598407159671 7543445126522397610739507)
          ·
            refine ⟨11315167689783596416109261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543445126522397610739507 11315167689783596416109261)
            ·
              refine ⟨4243187883668848656040973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11315167689783596416109261 4243187883668848656040973)
              ·
                refine ⟨1591195456375818246015365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4243187883668848656040973 1591195456375818246015365)
                ·
                  refine ⟨298349148070465921127881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591195456375818246015365 298349148070465921127881)
                  ·
                    rfl

theorem cell21_1307324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1307324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307324 prefixEnd_1307324 := by exact prefixLift 1307324
  have htrace : WordTrace (prefixWord ++ tailWord_1307324) baseStart_1307324 baseEnd_1307324 := by
    simpa [prefixWord, tailWord_1307324, baseEnd_1307324] using wordTrace_append hprefix tailTrace_1307324
  have hstable : (prefixWord ++ tailWord_1307324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307324).length < 2 ^ (prefixWord ++ tailWord_1307324).sum := by decide
  have hdescent : baseEnd_1307324 < baseStart_1307324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307338 : List Nat := [3, 1, 2, 1, 4, 1, 2, 7]
def baseStart_1307338 : Nat := 118140960795 + 1307338 * 2 ^ 59
def prefixEnd_1307338 : Nat := 4983230072969 + 3 ^ 40 * 1307338 * 2
def baseEnd_1307338 : Nat := 99450781020401669298173

theorem tailTrace_1307338 : CollatzResearch.WordTrace tailWord_1307338 prefixEnd_1307338 99450781020401669298173 := by
  unfold tailWord_1307338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920633534436294099908667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31788356091830117599756445 11920633534436294099908667)
  ·
    refine ⟨17880950301654441149863001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11920633534436294099908667 17880950301654441149863001)
    ·
      refine ⟨13410712726240830862397251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17880950301654441149863001 13410712726240830862397251)
      ·
        refine ⟨20116069089361246293595877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13410712726240830862397251 20116069089361246293595877)
        ·
          refine ⟨3771762954255233680049227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20116069089361246293595877 3771762954255233680049227)
          ·
            refine ⟨5657644431382850520073841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771762954255233680049227 5657644431382850520073841)
            ·
              refine ⟨4243233323537137890055381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657644431382850520073841 4243233323537137890055381)
              ·
                refine ⟨99450781020401669298173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4243233323537137890055381 99450781020401669298173)
                ·
                  rfl

theorem cell21_1307338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_1307338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307338 prefixEnd_1307338 := by exact prefixLift 1307338
  have htrace : WordTrace (prefixWord ++ tailWord_1307338) baseStart_1307338 baseEnd_1307338 := by
    simpa [prefixWord, tailWord_1307338, baseEnd_1307338] using wordTrace_append hprefix tailTrace_1307338
  have hstable : (prefixWord ++ tailWord_1307338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307338).length < 2 ^ (prefixWord ++ tailWord_1307338).sum := by decide
  have hdescent : baseEnd_1307338 < baseStart_1307338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307397 : List Nat := [1, 3, 1, 1, 2, 1, 1, 11]
def baseStart_1307397 : Nat := 118140960795 + 1307397 * 2 ^ 59
def prefixEnd_1307397 : Nat := 4983230072969 + 3 ^ 40 * 1307397 * 2
def baseEnd_1307397 : Nat := 99455269221678005470355

theorem tailTrace_1307397 : CollatzResearch.WordTrace tailWord_1307397 prefixEnd_1307397 99455269221678005470355 := by
  unfold tailWord_1307397
  simp only [CollatzResearch.WordTrace]
  refine ⟨47684686044531429476032445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31789790696354286317354963 47684686044531429476032445)
  ·
    refine ⟨17881757266699286053512167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47684686044531429476032445 17881757266699286053512167)
    ·
      refine ⟨26822635900048929080268251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17881757266699286053512167 26822635900048929080268251)
      ·
        refine ⟨40233953850073393620402377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26822635900048929080268251 40233953850073393620402377)
        ·
          refine ⟨30175465387555045215301783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40233953850073393620402377 30175465387555045215301783)
          ·
            refine ⟨45263198081332567822952675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30175465387555045215301783 45263198081332567822952675)
            ·
              refine ⟨67894797121998851734429013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45263198081332567822952675 67894797121998851734429013)
              ·
                refine ⟨99455269221678005470355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67894797121998851734429013 99455269221678005470355)
                ·
                  rfl

theorem cell21_1307397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_1307397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307397 prefixEnd_1307397 := by exact prefixLift 1307397
  have htrace : WordTrace (prefixWord ++ tailWord_1307397) baseStart_1307397 baseEnd_1307397 := by
    simpa [prefixWord, tailWord_1307397, baseEnd_1307397] using wordTrace_append hprefix tailTrace_1307397
  have hstable : (prefixWord ++ tailWord_1307397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307397).length < 2 ^ (prefixWord ++ tailWord_1307397).sum := by decide
  have hdescent : baseEnd_1307397 < baseStart_1307397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307445 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1307445 : Nat := 118140960795 + 1307445 * 2 ^ 59
def prefixEnd_1307445 : Nat := 4983230072969 + 3 ^ 40 * 1307445 * 2
def baseEnd_1307445 : Nat := 298376761918996599610967

theorem tailTrace_1307445 : CollatzResearch.WordTrace tailWord_1307445 prefixEnd_1307445 298376761918996599610967 := by
  unfold tailWord_1307445
  simp only [CollatzResearch.WordTrace]
  refine ⟨47686436748357533673779789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31790957832238355782519859 47686436748357533673779789)
  ·
    refine ⟨17882413780634075127667421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47686436748357533673779789 17882413780634075127667421)
    ·
      refine ⟨6705905167737778172875283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17882413780634075127667421 6705905167737778172875283)
      ·
        refine ⟨10058857751606667259312925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705905167737778172875283 10058857751606667259312925)
        ·
          refine ⟨3772071656852500222242347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10058857751606667259312925 3772071656852500222242347)
          ·
            refine ⟨5658107485278750333363521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772071656852500222242347 5658107485278750333363521)
            ·
              refine ⟨4243580613959062750022641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658107485278750333363521 4243580613959062750022641)
              ·
                refine ⟨3182685460469297062516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4243580613959062750022641 3182685460469297062516981)
                ·
                  refine ⟨298376761918996599610967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3182685460469297062516981 298376761918996599610967)
                  ·
                    rfl

theorem cell21_1307445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1307445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307445 prefixEnd_1307445 := by exact prefixLift 1307445
  have htrace : WordTrace (prefixWord ++ tailWord_1307445) baseStart_1307445 baseEnd_1307445 := by
    simpa [prefixWord, tailWord_1307445, baseEnd_1307445] using wordTrace_append hprefix tailTrace_1307445
  have hstable : (prefixWord ++ tailWord_1307445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307445).length < 2 ^ (prefixWord ++ tailWord_1307445).sum := by decide
  have hdescent : baseEnd_1307445 < baseStart_1307445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307479 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 3]
def baseStart_1307479 : Nat := 118140960795 + 1307479 * 2 ^ 59
def prefixEnd_1307479 : Nat := 4983230072969 + 3 ^ 40 * 1307479 * 2
def baseEnd_1307479 : Nat := 298384521182220096044231

theorem tailTrace_1307479 : CollatzResearch.WordTrace tailWord_1307479 prefixEnd_1307479 298384521182220096044231 := by
  unfold tailWord_1307479
  simp only [CollatzResearch.WordTrace]
  refine ⟨47687676830234357480517491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31791784553489571653678327 47687676830234357480517491)
  ·
    refine ⟨71531515245351536220776237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47687676830234357480517491 71531515245351536220776237)
    ·
      refine ⟨26824318217006826082791089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71531515245351536220776237 26824318217006826082791089)
      ·
        refine ⟨20118238662755119562093317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26824318217006826082791089 20118238662755119562093317)
        ·
          refine ⟨3772169749266584917892497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20118238662755119562093317 3772169749266584917892497)
          ·
            refine ⟨2829127311949938688419373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772169749266584917892497 2829127311949938688419373)
            ·
              refine ⟨1060922741981227008157265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2829127311949938688419373 1060922741981227008157265)
              ·
                refine ⟨795692056485920256117949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060922741981227008157265 795692056485920256117949)
                ·
                  refine ⟨298384521182220096044231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795692056485920256117949 298384521182220096044231)
                  ·
                    rfl

theorem cell21_1307479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3].length) (baseStart_1307479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307479 prefixEnd_1307479 := by exact prefixLift 1307479
  have htrace : WordTrace (prefixWord ++ tailWord_1307479) baseStart_1307479 baseEnd_1307479 := by
    simpa [prefixWord, tailWord_1307479, baseEnd_1307479] using wordTrace_append hprefix tailTrace_1307479
  have hstable : (prefixWord ++ tailWord_1307479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307479).length < 2 ^ (prefixWord ++ tailWord_1307479).sum := by decide
  have hdescent : baseEnd_1307479 < baseStart_1307479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307504 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_1307504 : Nat := 118140960795 + 1307504 * 2 ^ 59
def prefixEnd_1307504 : Nat := 4983230072969 + 3 ^ 40 * 1307504 * 2
def baseEnd_1307504 : Nat := 298390226522825608127513

theorem tailTrace_1307504 : CollatzResearch.WordTrace tailWord_1307504 prefixEnd_1307504 298390226522825608127513 := by
  unfold tailWord_1307504
  simp only [CollatzResearch.WordTrace]
  refine ⟨23844294327571893375088783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31792392436762524500118377 23844294327571893375088783)
  ·
    refine ⟨35766441491357840062633175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23844294327571893375088783 35766441491357840062633175)
    ·
      refine ⟨53649662237036760093949763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35766441491357840062633175 53649662237036760093949763)
      ·
        refine ⟨80474493355555140140924645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53649662237036760093949763 80474493355555140140924645)
        ·
          refine ⟨15088967504166588776423371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80474493355555140140924645 15088967504166588776423371)
          ·
            refine ⟨22633451256249883164635057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15088967504166588776423371 22633451256249883164635057)
            ·
              refine ⟨16975088442187412373476293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22633451256249883164635057 16975088442187412373476293)
              ·
                refine ⟨3182829082910139820026805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16975088442187412373476293 3182829082910139820026805)
                ·
                  refine ⟨298390226522825608127513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3182829082910139820026805 298390226522825608127513)
                  ·
                    rfl

theorem cell21_1307504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_1307504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307504 prefixEnd_1307504 := by exact prefixLift 1307504
  have htrace : WordTrace (prefixWord ++ tailWord_1307504) baseStart_1307504 baseEnd_1307504 := by
    simpa [prefixWord, tailWord_1307504, baseEnd_1307504] using wordTrace_append hprefix tailTrace_1307504
  have hstable : (prefixWord ++ tailWord_1307504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307504).length < 2 ^ (prefixWord ++ tailWord_1307504).sum := by decide
  have hdescent : baseEnd_1307504 < baseStart_1307504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307572 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1307572 : Nat := 118140960795 + 1307572 * 2 ^ 59
def prefixEnd_1307572 : Nat := 4983230072969 + 3 ^ 40 * 1307572 * 2
def baseEnd_1307572 : Nat := 298405745049272600994041

theorem tailTrace_1307572 : CollatzResearch.WordTrace tailWord_1307572 prefixEnd_1307572 298405745049272600994041 := by
  unfold tailWord_1307572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845534409448717181826485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31794045879264956242435313 23845534409448717181826485)
  ·
    refine ⟨2235518850885817235796233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23845534409448717181826485 2235518850885817235796233)
    ·
      refine ⟨1676639138164362926847175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2235518850885817235796233 1676639138164362926847175)
      ·
        refine ⟨2514958707246544390270763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676639138164362926847175 2514958707246544390270763)
        ·
          refine ⟨3772438060869816585406145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514958707246544390270763 3772438060869816585406145)
          ·
            refine ⟨2829328545652362439054609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772438060869816585406145 2829328545652362439054609)
            ·
              refine ⟨2121996409239271829290957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829328545652362439054609 2121996409239271829290957)
              ·
                refine ⟨795748653464726935984109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2121996409239271829290957 795748653464726935984109)
                ·
                  refine ⟨298405745049272600994041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795748653464726935984109 298405745049272600994041)
                  ·
                    rfl

theorem cell21_1307572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1307572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307572 prefixEnd_1307572 := by exact prefixLift 1307572
  have htrace : WordTrace (prefixWord ++ tailWord_1307572) baseStart_1307572 baseEnd_1307572 := by
    simpa [prefixWord, tailWord_1307572, baseEnd_1307572] using wordTrace_append hprefix tailTrace_1307572
  have hstable : (prefixWord ++ tailWord_1307572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307572).length < 2 ^ (prefixWord ++ tailWord_1307572).sum := by decide
  have hdescent : baseEnd_1307572 < baseStart_1307572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307704 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_1307704 : Nat := 118140960795 + 1307704 * 2 ^ 59
def prefixEnd_1307704 : Nat := 4983230072969 + 3 ^ 40 * 1307704 * 2
def baseEnd_1307704 : Nat := 298435869247669704793771

theorem tailTrace_1307704 : CollatzResearch.WordTrace tailWord_1307704 prefixEnd_1307704 298435869247669704793771 := by
  unfold tailWord_1307704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23847941627209610453729083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31797255502946147271638777 23847941627209610453729083)
  ·
    refine ⟨35771912440814415680593625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23847941627209610453729083 35771912440814415680593625)
    ·
      refine ⟨26828934330610811760445219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35771912440814415680593625 26828934330610811760445219)
      ·
        refine ⟨40243401495916217640667829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26828934330610811760445219 40243401495916217640667829)
        ·
          refine ⟨3772818890242145403812609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40243401495916217640667829 3772818890242145403812609)
          ·
            refine ⟨2829614167681609052859457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772818890242145403812609 2829614167681609052859457)
            ·
              refine ⟨2122210625761206789644593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829614167681609052859457 2122210625761206789644593)
              ·
                refine ⟨1591657969320905092233445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122210625761206789644593 1591657969320905092233445)
                ·
                  refine ⟨298435869247669704793771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591657969320905092233445 298435869247669704793771)
                  ·
                    rfl

theorem cell21_1307704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_1307704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307704 prefixEnd_1307704 := by exact prefixLift 1307704
  have htrace : WordTrace (prefixWord ++ tailWord_1307704) baseStart_1307704 baseEnd_1307704 := by
    simpa [prefixWord, tailWord_1307704, baseEnd_1307704] using wordTrace_append hprefix tailTrace_1307704
  have hstable : (prefixWord ++ tailWord_1307704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307704).length < 2 ^ (prefixWord ++ tailWord_1307704).sum := by decide
  have hdescent : baseEnd_1307704 < baseStart_1307704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307732 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1307732 : Nat := 118140960795 + 1307732 * 2 ^ 59
def prefixEnd_1307732 : Nat := 4983230072969 + 3 ^ 40 * 1307732 * 2
def baseEnd_1307732 : Nat := 298442259229147878327047

theorem tailTrace_1307732 : CollatzResearch.WordTrace tailWord_1307732 prefixEnd_1307732 298442259229147878327047 := by
  unfold tailWord_1307732
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848452249158890844738725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31797936332211854459651633 23848452249158890844738725)
  ·
    refine ⟨4471584796717292033388511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23848452249158890844738725 4471584796717292033388511)
    ·
      refine ⟨6707377195075938050082767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471584796717292033388511 6707377195075938050082767)
      ·
        refine ⟨10061065792613907075124151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707377195075938050082767 10061065792613907075124151)
        ·
          refine ⟨15091598688920860612686227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061065792613907075124151 15091598688920860612686227)
          ·
            refine ⟨22637398033381290919029341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15091598688920860612686227 22637398033381290919029341)
            ·
              refine ⟨8489024262517984094636003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22637398033381290919029341 8489024262517984094636003)
              ·
                refine ⟨12733536393776976141954005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8489024262517984094636003 12733536393776976141954005)
                ·
                  refine ⟨298442259229147878327047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12733536393776976141954005 298442259229147878327047)
                  ·
                    rfl

theorem cell21_1307732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1307732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307732 prefixEnd_1307732 := by exact prefixLift 1307732
  have htrace : WordTrace (prefixWord ++ tailWord_1307732) baseStart_1307732 baseEnd_1307732 := by
    simpa [prefixWord, tailWord_1307732, baseEnd_1307732] using wordTrace_append hprefix tailTrace_1307732
  have hstable : (prefixWord ++ tailWord_1307732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307732).length < 2 ^ (prefixWord ++ tailWord_1307732).sum := by decide
  have hdescent : baseEnd_1307732 < baseStart_1307732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307766 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1307766 : Nat := 118140960795 + 1307766 * 2 ^ 59
def prefixEnd_1307766 : Nat := 4983230072969 + 3 ^ 40 * 1307766 * 2
def baseEnd_1307766 : Nat := 298450018492371374760311

theorem tailTrace_1307766 : CollatzResearch.WordTrace tailWord_1307766 prefixEnd_1307766 298450018492371374760311 := by
  unfold tailWord_1307766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981134036262162843513447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31798763053463070330810101 2981134036262162843513447)
  ·
    refine ⟨4471701054393244265270171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981134036262162843513447 4471701054393244265270171)
    ·
      refine ⟨6707551581589866397905257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471701054393244265270171 6707551581589866397905257)
      ·
        refine ⟨5030663686192399798428943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6707551581589866397905257 5030663686192399798428943)
        ·
          refine ⟨7545995529288599697643415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030663686192399798428943 7545995529288599697643415)
          ·
            refine ⟨11318993293932899546465123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545995529288599697643415 11318993293932899546465123)
            ·
              refine ⟨16978489940899349319697685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318993293932899546465123 16978489940899349319697685)
              ·
                refine ⟨795866715979656999360829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16978489940899349319697685 795866715979656999360829)
                ·
                  refine ⟨298450018492371374760311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795866715979656999360829 298450018492371374760311)
                  ·
                    rfl

theorem cell21_1307766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1307766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307766 prefixEnd_1307766 := by exact prefixLift 1307766
  have htrace : WordTrace (prefixWord ++ tailWord_1307766) baseStart_1307766 baseEnd_1307766 := by
    simpa [prefixWord, tailWord_1307766, baseEnd_1307766] using wordTrace_append hprefix tailTrace_1307766
  have hstable : (prefixWord ++ tailWord_1307766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307766).length < 2 ^ (prefixWord ++ tailWord_1307766).sum := by decide
  have hdescent : baseEnd_1307766 < baseStart_1307766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307791 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_1307791 : Nat := 118140960795 + 1307791 * 2 ^ 59
def prefixEnd_1307791 : Nat := 4983230072969 + 3 ^ 40 * 1307791 * 2
def baseEnd_1307791 : Nat := 298455723832976886843593

theorem tailTrace_1307791 : CollatzResearch.WordTrace tailWord_1307791 prefixEnd_1307791 298455723832976886843593 := by
  unfold tailWord_1307791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47699056405104034765875227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31799370936736023177250151 47699056405104034765875227)
  ·
    refine ⟨71548584607656052148812841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47699056405104034765875227 71548584607656052148812841)
    ·
      refine ⟨53661438455742039111609631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71548584607656052148812841 53661438455742039111609631)
      ·
        refine ⟨80492157683613058667414447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53661438455742039111609631 80492157683613058667414447)
        ·
          refine ⟨120738236525419588001121671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80492157683613058667414447 120738236525419588001121671)
          ·
            refine ⟨181107354788129382001682507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120738236525419588001121671 181107354788129382001682507)
            ·
              refine ⟨271661032182194073002523761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181107354788129382001682507 271661032182194073002523761)
              ·
                refine ⟨203745774136645554751892821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271661032182194073002523761 203745774136645554751892821)
                ·
                  refine ⟨298455723832976886843593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 203745774136645554751892821 298455723832976886843593)
                  ·
                    rfl

theorem cell21_1307791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_1307791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307791 prefixEnd_1307791 := by exact prefixLift 1307791
  have htrace : WordTrace (prefixWord ++ tailWord_1307791) baseStart_1307791 baseEnd_1307791 := by
    simpa [prefixWord, tailWord_1307791, baseEnd_1307791] using wordTrace_append hprefix tailTrace_1307791
  have hstable : (prefixWord ++ tailWord_1307791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307791).length < 2 ^ (prefixWord ++ tailWord_1307791).sum := by decide
  have hdescent : baseEnd_1307791 < baseStart_1307791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307794 : List Nat := [3, 2, 3, 1, 1, 3, 1, 7]
def baseStart_1307794 : Nat := 118140960795 + 1307794 * 2 ^ 59
def prefixEnd_1307794 : Nat := 4983230072969 + 3 ^ 40 * 1307794 * 2
def baseEnd_1307794 : Nat := 99485469491283182764529

theorem tailTrace_1307794 : CollatzResearch.WordTrace tailWord_1307794 prefixEnd_1307794 99485469491283182764529 := by
  unfold tailWord_1307794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924791456023291569558609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31799443882728777518822957 11924791456023291569558609)
  ·
    refine ⟨8943593592017468677168957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11924791456023291569558609 8943593592017468677168957)
    ·
      refine ⟨3353847597006550753938359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8943593592017468677168957 3353847597006550753938359)
      ·
        refine ⟨5030771395509826130907539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353847597006550753938359 5030771395509826130907539)
        ·
          refine ⟨7546157093264739196361309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030771395509826130907539 7546157093264739196361309)
          ·
            refine ⟨2829808909974277198635491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7546157093264739196361309 2829808909974277198635491)
            ·
              refine ⟨4244713364961415797953237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829808909974277198635491 4244713364961415797953237)
              ·
                refine ⟨99485469491283182764529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4244713364961415797953237 99485469491283182764529)
                ·
                  rfl

theorem cell21_1307794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_1307794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307794 prefixEnd_1307794 := by exact prefixLift 1307794
  have htrace : WordTrace (prefixWord ++ tailWord_1307794) baseStart_1307794 baseEnd_1307794 := by
    simpa [prefixWord, tailWord_1307794, baseEnd_1307794] using wordTrace_append hprefix tailTrace_1307794
  have hstable : (prefixWord ++ tailWord_1307794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307794).length < 2 ^ (prefixWord ++ tailWord_1307794).sum := by decide
  have hdescent : baseEnd_1307794 < baseStart_1307794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307825 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_1307825 : Nat := 118140960795 + 1307825 * 2 ^ 59
def prefixEnd_1307825 : Nat := 4983230072969 + 3 ^ 40 * 1307825 * 2
def baseEnd_1307825 : Nat := 298463483096200383276857

theorem tailTrace_1307825 : CollatzResearch.WordTrace tailWord_1307825 prefixEnd_1307825 298463483096200383276857 := by
  unfold tailWord_1307825
  simp only [CollatzResearch.WordTrace]
  refine ⟨47700296486980858572612929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31800197657987239048408619 47700296486980858572612929)
  ·
    refine ⟨35775222365235643929459697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47700296486980858572612929 35775222365235643929459697)
    ·
      refine ⟨26831416773926732947094773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35775222365235643929459697 26831416773926732947094773)
      ·
        refine ⟨2515445322555631213790135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26831416773926732947094773 2515445322555631213790135)
        ·
          refine ⟨3773167983833446820685203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515445322555631213790135 3773167983833446820685203)
          ·
            refine ⟨5659751975750170231027805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773167983833446820685203 5659751975750170231027805)
            ·
              refine ⟨2122406990906313836635427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5659751975750170231027805 2122406990906313836635427)
              ·
                refine ⟨3183610486359470754953141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122406990906313836635427 3183610486359470754953141)
                ·
                  refine ⟨298463483096200383276857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3183610486359470754953141 298463483096200383276857)
                  ·
                    rfl

theorem cell21_1307825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_1307825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307825 prefixEnd_1307825 := by exact prefixLift 1307825
  have htrace : WordTrace (prefixWord ++ tailWord_1307825) baseStart_1307825 baseEnd_1307825 := by
    simpa [prefixWord, tailWord_1307825, baseEnd_1307825] using wordTrace_append hprefix tailTrace_1307825
  have hstable : (prefixWord ++ tailWord_1307825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307825).length < 2 ^ (prefixWord ++ tailWord_1307825).sum := by decide
  have hdescent : baseEnd_1307825 < baseStart_1307825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307887 : List Nat := [1, 1, 2, 1, 8, 1, 1, 6]
def baseStart_1307887 : Nat := 118140960795 + 1307887 * 2 ^ 59
def prefixEnd_1307887 : Nat := 4983230072969 + 3 ^ 40 * 1307887 * 2
def baseEnd_1307887 : Nat := 99492544113634017747799

theorem tailTrace_1307887 : CollatzResearch.WordTrace tailWord_1307887 prefixEnd_1307887 99492544113634017747799 := by
  unfold tailWord_1307887
  simp only [CollatzResearch.WordTrace]
  refine ⟨47702557812756243161369915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31801705208504162107579943 47702557812756243161369915)
  ·
    refine ⟨71553836719134364742054873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47702557812756243161369915 71553836719134364742054873)
    ·
      refine ⟨53665377539350773556541155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71553836719134364742054873 53665377539350773556541155)
      ·
        refine ⟨80498066309026160334811733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53665377539350773556541155 80498066309026160334811733)
        ·
          refine ⟨943336714558900316423575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 80498066309026160334811733 943336714558900316423575)
          ·
            refine ⟨1415005071838350474635363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943336714558900316423575 1415005071838350474635363)
            ·
              refine ⟨2122507607757525711953045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415005071838350474635363 2122507607757525711953045)
              ·
                refine ⟨99492544113634017747799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2122507607757525711953045 99492544113634017747799)
                ·
                  rfl

theorem cell21_1307887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 6].length) (baseStart_1307887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307887 prefixEnd_1307887 := by exact prefixLift 1307887
  have htrace : WordTrace (prefixWord ++ tailWord_1307887) baseStart_1307887 baseEnd_1307887 := by
    simpa [prefixWord, tailWord_1307887, baseEnd_1307887] using wordTrace_append hprefix tailTrace_1307887
  have hstable : (prefixWord ++ tailWord_1307887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307887).length < 2 ^ (prefixWord ++ tailWord_1307887).sum := by decide
  have hdescent : baseEnd_1307887 < baseStart_1307887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307918 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_1307918 : Nat := 118140960795 + 1307918 * 2 ^ 59
def prefixEnd_1307918 : Nat := 4983230072969 + 3 ^ 40 * 1307918 * 2
def baseEnd_1307918 : Nat := 298484706963252888226667

theorem tailTrace_1307918 : CollatzResearch.WordTrace tailWord_1307918 prefixEnd_1307918 298484706963252888226667 := by
  unfold tailWord_1307918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962961059455491931968551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31802458983762623637165605 5962961059455491931968551)
  ·
    refine ⟨8944441589183237897952827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962961059455491931968551 8944441589183237897952827)
    ·
      refine ⟨13416662383774856846929241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944441589183237897952827 13416662383774856846929241)
      ·
        refine ⟨10062496787831142635196931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13416662383774856846929241 10062496787831142635196931)
        ·
          refine ⟨15093745181746713952795397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10062496787831142635196931 15093745181746713952795397)
          ·
            refine ⟨2830077221577508866149137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15093745181746713952795397 2830077221577508866149137)
            ·
              refine ⟨2122557916183131649611853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830077221577508866149137 2122557916183131649611853)
              ·
                refine ⟨795959218568674368604445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122557916183131649611853 795959218568674368604445)
                ·
                  refine ⟨298484706963252888226667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795959218568674368604445 298484706963252888226667)
                  ·
                    rfl

theorem cell21_1307918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_1307918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307918 prefixEnd_1307918 := by exact prefixLift 1307918
  have htrace : WordTrace (prefixWord ++ tailWord_1307918) baseStart_1307918 baseEnd_1307918 := by
    simpa [prefixWord, tailWord_1307918, baseEnd_1307918] using wordTrace_append hprefix tailTrace_1307918
  have hstable : (prefixWord ++ tailWord_1307918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307918).length < 2 ^ (prefixWord ++ tailWord_1307918).sum := by decide
  have hdescent : baseEnd_1307918 < baseStart_1307918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307977 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 3]
def baseStart_1307977 : Nat := 118140960795 + 1307977 * 2 ^ 59
def prefixEnd_1307977 : Nat := 4983230072969 + 3 ^ 40 * 1307977 * 2
def baseEnd_1307977 : Nat := 298498171567081896743213

theorem tailTrace_1307977 : CollatzResearch.WordTrace tailWord_1307977 prefixEnd_1307977 298498171567081896743213 := by
  unfold tailWord_1307977
  simp only [CollatzResearch.WordTrace]
  refine ⟨47705840382430188532146185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31803893588286792354764123 47705840382430188532146185)
  ·
    refine ⟨35779380286822641399109639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47705840382430188532146185 35779380286822641399109639)
    ·
      refine ⟨53669070430233962098664459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35779380286822641399109639 53669070430233962098664459)
      ·
        refine ⟨80503605645350943147996689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53669070430233962098664459 80503605645350943147996689)
        ·
          refine ⟨60377704234013207360997517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80503605645350943147996689 60377704234013207360997517)
          ·
            refine ⟨22641639087754952760374069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60377704234013207360997517 22641639087754952760374069)
            ·
              refine ⟨2122653664477026821285069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22641639087754952760374069 2122653664477026821285069)
              ·
                refine ⟨795995124178885057981901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122653664477026821285069 795995124178885057981901)
                ·
                  refine ⟨298498171567081896743213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795995124178885057981901 298498171567081896743213)
                  ·
                    rfl

theorem cell21_1307977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_1307977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1307977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1307977 prefixEnd_1307977 := by exact prefixLift 1307977
  have htrace : WordTrace (prefixWord ++ tailWord_1307977) baseStart_1307977 baseEnd_1307977 := by
    simpa [prefixWord, tailWord_1307977, baseEnd_1307977] using wordTrace_append hprefix tailTrace_1307977
  have hstable : (prefixWord ++ tailWord_1307977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307977).length < 2 ^ (prefixWord ++ tailWord_1307977).sum := by decide
  have hdescent : baseEnd_1307977 < baseStart_1307977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308005 : List Nat := [1, 3, 1, 3, 1, 2, 4, 6]
def baseStart_1308005 : Nat := 118140960795 + 1308005 * 2 ^ 59
def prefixEnd_1308005 : Nat := 4983230072969 + 3 ^ 40 * 1308005 * 2
def baseEnd_1308005 : Nat := 99501520516186690092163

theorem tailTrace_1308005 : CollatzResearch.WordTrace tailWord_1308005 prefixEnd_1308005 99501520516186690092163 := by
  unfold tailWord_1308005
  simp only [CollatzResearch.WordTrace]
  refine ⟨47706861626328749314165469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31804574417552499542776979 47706861626328749314165469)
  ·
    refine ⟨17890073109873280992812051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47706861626328749314165469 17890073109873280992812051)
    ·
      refine ⟨26835109664809921489218077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17890073109873280992812051 26835109664809921489218077)
      ·
        refine ⟨10063166124303720558456779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26835109664809921489218077 10063166124303720558456779)
        ·
          refine ⟨15094749186455580837685169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10063166124303720558456779 15094749186455580837685169)
          ·
            refine ⟨11321061889841685628263877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15094749186455580837685169 11321061889841685628263877)
            ·
              refine ⟨2122699104345316055299477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11321061889841685628263877 2122699104345316055299477)
              ·
                refine ⟨99501520516186690092163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2122699104345316055299477 99501520516186690092163)
                ·
                  rfl

theorem cell21_1308005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_1308005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308005 prefixEnd_1308005 := by exact prefixLift 1308005
  have htrace : WordTrace (prefixWord ++ tailWord_1308005) baseStart_1308005 baseEnd_1308005 := by
    simpa [prefixWord, tailWord_1308005, baseEnd_1308005] using wordTrace_append hprefix tailTrace_1308005
  have hstable : (prefixWord ++ tailWord_1308005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308005).length < 2 ^ (prefixWord ++ tailWord_1308005).sum := by decide
  have hdescent : baseEnd_1308005 < baseStart_1308005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308008 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_1308008 : Nat := 118140960795 + 1308008 * 2 ^ 59
def prefixEnd_1308008 : Nat := 4983230072969 + 3 ^ 40 * 1308008 * 2
def baseEnd_1308008 : Nat := 298505246189432731726483

theorem tailTrace_1308008 : CollatzResearch.WordTrace tailWord_1308008 prefixEnd_1308008 298505246189432731726483 := by
  unfold tailWord_1308008
  simp only [CollatzResearch.WordTrace]
  refine ⟨23853485522658940413262339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31804647363545253884349785 23853485522658940413262339)
  ·
    refine ⟨35780228283988410619893509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23853485522658940413262339 35780228283988410619893509)
    ·
      refine ⟨6708792803247826991230033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35780228283988410619893509 6708792803247826991230033)
      ·
        refine ⟨5031594602435870243422525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6708792803247826991230033 5031594602435870243422525)
        ·
          refine ⟨1886847975913451341283447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5031594602435870243422525 1886847975913451341283447)
          ·
            refine ⟨2830271963870177011925171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886847975913451341283447 2830271963870177011925171)
            ·
              refine ⟨4245407945805265517887757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830271963870177011925171 4245407945805265517887757)
              ·
                refine ⟨1592027979676974569207909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4245407945805265517887757 1592027979676974569207909)
                ·
                  refine ⟨298505246189432731726483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592027979676974569207909 298505246189432731726483)
                  ·
                    rfl

theorem cell21_1308008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_1308008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308008 prefixEnd_1308008 := by exact prefixLift 1308008
  have htrace : WordTrace (prefixWord ++ tailWord_1308008) baseStart_1308008 baseEnd_1308008 := by
    simpa [prefixWord, tailWord_1308008, baseEnd_1308008] using wordTrace_append hprefix tailTrace_1308008
  have hstable : (prefixWord ++ tailWord_1308008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308008).length < 2 ^ (prefixWord ++ tailWord_1308008).sum := by decide
  have hdescent : baseEnd_1308008 < baseStart_1308008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308146 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1308146 : Nat := 118140960795 + 1308146 * 2 ^ 59
def prefixEnd_1308146 : Nat := 4983230072969 + 3 ^ 40 * 1308146 * 2
def baseEnd_1308146 : Nat := 298536739669575158426201

theorem tailTrace_1308146 : CollatzResearch.WordTrace tailWord_1308146 prefixEnd_1308146 298536739669575158426201 := by
  unfold tailWord_1308146
  simp only [CollatzResearch.WordTrace]
  refine ⟨11928001079704482598762073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31808002879211953596698861 11928001079704482598762073)
  ·
    refine ⟨8946000809778361949071555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11928001079704482598762073 8946000809778361949071555)
    ·
      refine ⟨13419001214667542923607333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8946000809778361949071555 13419001214667542923607333)
      ·
        refine ⟨2516062727750164298176375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13419001214667542923607333 2516062727750164298176375)
        ·
          refine ⟨3774094091625246447264563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516062727750164298176375 3774094091625246447264563)
          ·
            refine ⟨5661141137437869670896845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774094091625246447264563 5661141137437869670896845)
            ·
              refine ⟨2122927926539201126586317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5661141137437869670896845 2122927926539201126586317)
              ·
                refine ⟨796097972452200422469869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122927926539201126586317 796097972452200422469869)
                ·
                  refine ⟨298536739669575158426201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796097972452200422469869 298536739669575158426201)
                  ·
                    rfl

theorem cell21_1308146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1308146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308146 prefixEnd_1308146 := by exact prefixLift 1308146
  have htrace : WordTrace (prefixWord ++ tailWord_1308146) baseStart_1308146 baseEnd_1308146 := by
    simpa [prefixWord, tailWord_1308146, baseEnd_1308146] using wordTrace_append hprefix tailTrace_1308146
  have hstable : (prefixWord ++ tailWord_1308146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308146).length < 2 ^ (prefixWord ++ tailWord_1308146).sum := by decide
  have hdescent : baseEnd_1308146 < baseStart_1308146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308157 : List Nat := [1, 4, 1, 1, 1, 6, 7]
def baseStart_1308157 : Nat := 118140960795 + 1308157 * 2 ^ 59
def prefixEnd_1308157 : Nat := 4983230072969 + 3 ^ 40 * 1308157 * 2
def baseEnd_1308157 : Nat := 33171027779937953749205

theorem tailTrace_1308157 : CollatzResearch.WordTrace tailWord_1308157 prefixEnd_1308157 33171027779937953749205 := by
  unfold tailWord_1308157
  simp only [CollatzResearch.WordTrace]
  refine ⟨47712405521778079273698725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31808270347852052849132483 47712405521778079273698725)
  ·
    refine ⟨8946076035333389863818511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47712405521778079273698725 8946076035333389863818511)
    ·
      refine ⟨13419114053000084795727767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8946076035333389863818511 13419114053000084795727767)
      ·
        refine ⟨20128671079500127193591651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13419114053000084795727767 20128671079500127193591651)
        ·
          refine ⟨30193006619250190790387477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20128671079500127193591651 30193006619250190790387477)
          ·
            refine ⟨1415297185277352693299413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30193006619250190790387477 1415297185277352693299413)
            ·
              refine ⟨33171027779937953749205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1415297185277352693299413 33171027779937953749205)
              ·
                rfl

theorem cell21_1308157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 7].length) (baseStart_1308157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308157 prefixEnd_1308157 := by exact prefixLift 1308157
  have htrace : WordTrace (prefixWord ++ tailWord_1308157) baseStart_1308157 baseEnd_1308157 := by
    simpa [prefixWord, tailWord_1308157, baseEnd_1308157] using wordTrace_append hprefix tailTrace_1308157
  have hstable : (prefixWord ++ tailWord_1308157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308157).length < 2 ^ (prefixWord ++ tailWord_1308157).sum := by decide
  have hdescent : baseEnd_1308157 < baseStart_1308157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308174 : List Nat := [4, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1308174 : Nat := 118140960795 + 1308174 * 2 ^ 59
def prefixEnd_1308174 : Nat := 4983230072969 + 3 ^ 40 * 1308174 * 2
def baseEnd_1308174 : Nat := 99514376550351110653159

theorem tailTrace_1308174 : CollatzResearch.WordTrace tailWord_1308174 prefixEnd_1308174 99514376550351110653159 := by
  unfold tailWord_1308174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964128195339561397133447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31808683708477660784711717 5964128195339561397133447)
  ·
    refine ⟨8946192293009342095700171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5964128195339561397133447 8946192293009342095700171)
    ·
      refine ⟨13419288439514013143550257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8946192293009342095700171 13419288439514013143550257)
      ·
        refine ⟨10064466329635509857662693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13419288439514013143550257 10064466329635509857662693)
        ·
          refine ⟨1887087436806658098311755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10064466329635509857662693 1887087436806658098311755)
          ·
            refine ⟨2830631155209987147467633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887087436806658098311755 2830631155209987147467633)
            ·
              refine ⟨2122973366407490360600725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830631155209987147467633 2122973366407490360600725)
              ·
                refine ⟨99514376550351110653159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2122973366407490360600725 99514376550351110653159)
                ·
                  rfl

theorem cell21_1308174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1308174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308174 prefixEnd_1308174 := by exact prefixLift 1308174
  have htrace : WordTrace (prefixWord ++ tailWord_1308174) baseStart_1308174 baseEnd_1308174 := by
    simpa [prefixWord, tailWord_1308174, baseEnd_1308174] using wordTrace_append hprefix tailTrace_1308174
  have hstable : (prefixWord ++ tailWord_1308174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308174).length < 2 ^ (prefixWord ++ tailWord_1308174).sum := by decide
  have hdescent : baseEnd_1308174 < baseStart_1308174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308216 : List Nat := [2, 1, 2, 1, 4, 11]
def baseStart_1308216 : Nat := 118140960795 + 1308216 * 2 ^ 59
def prefixEnd_1308216 : Nat := 4983230072969 + 3 ^ 40 * 1308216 * 2
def baseEnd_1308216 : Nat := 11057507949010021935533

theorem tailTrace_1308216 : CollatzResearch.WordTrace tailWord_1308216 prefixEnd_1308216 11057507949010021935533 := by
  unfold tailWord_1308216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857278714282166175048251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31809704952376221566731001 23857278714282166175048251)
  ·
    refine ⟨35785918071423249262572377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23857278714282166175048251 35785918071423249262572377)
    ·
      refine ⟨26839438553567436946929283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35785918071423249262572377 26839438553567436946929283)
      ·
        refine ⟨40259157830351155420393925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26839438553567436946929283 40259157830351155420393925)
        ·
          refine ⟨7548592093190841641323861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40259157830351155420393925 7548592093190841641323861)
          ·
            refine ⟨11057507949010021935533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7548592093190841641323861 11057507949010021935533)
            ·
              rfl

theorem cell21_1308216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 11].length) (baseStart_1308216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308216 prefixEnd_1308216 := by exact prefixLift 1308216
  have htrace : WordTrace (prefixWord ++ tailWord_1308216) baseStart_1308216 baseEnd_1308216 := by
    simpa [prefixWord, tailWord_1308216, baseEnd_1308216] using wordTrace_append hprefix tailTrace_1308216
  have hstable : (prefixWord ++ tailWord_1308216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308216).length < 2 ^ (prefixWord ++ tailWord_1308216).sum := by decide
  have hdescent : baseEnd_1308216 < baseStart_1308216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308247 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_1308247 : Nat := 118140960795 + 1308247 * 2 ^ 59
def prefixEnd_1308247 : Nat := 4983230072969 + 3 ^ 40 * 1308247 * 2
def baseEnd_1308247 : Nat := 298559789245621427242661

theorem tailTrace_1308247 : CollatzResearch.WordTrace tailWord_1308247 prefixEnd_1308247 298559789245621427242661 := by
  unfold tailWord_1308247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47715688091452024644474995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31810458727634683096316663 47715688091452024644474995)
  ·
    refine ⟨71573532137178036966712493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47715688091452024644474995 71573532137178036966712493)
    ·
      refine ⟨26840074551441763862517185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71573532137178036966712493 26840074551441763862517185)
      ·
        refine ⟨20130055913581322896887889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26840074551441763862517185 20130055913581322896887889)
        ·
          refine ⟨15097541935185992172665917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20130055913581322896887889 15097541935185992172665917)
          ·
            refine ⟨5661578225694747064749719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15097541935185992172665917 5661578225694747064749719)
            ·
              refine ⟨8492367338542120597124579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661578225694747064749719 8492367338542120597124579)
              ·
                refine ⟨12738551007813180895686869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492367338542120597124579 12738551007813180895686869)
                ·
                  refine ⟨298559789245621427242661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12738551007813180895686869 298559789245621427242661)
                  ·
                    rfl

theorem cell21_1308247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_1308247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308247 prefixEnd_1308247 := by exact prefixLift 1308247
  have htrace : WordTrace (prefixWord ++ tailWord_1308247) baseStart_1308247 baseEnd_1308247 := by
    simpa [prefixWord, tailWord_1308247, baseEnd_1308247] using wordTrace_append hprefix tailTrace_1308247
  have hstable : (prefixWord ++ tailWord_1308247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308247).length < 2 ^ (prefixWord ++ tailWord_1308247).sum := by decide
  have hdescent : baseEnd_1308247 < baseStart_1308247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308385 : List Nat := [1, 2, 3, 1, 6, 8]
def baseStart_1308385 : Nat := 118140960795 + 1308385 * 2 ^ 59
def prefixEnd_1308385 : Nat := 4983230072969 + 3 ^ 40 * 1308385 * 2
def baseEnd_1308385 : Nat := 11058936397250513108977

theorem tailTrace_1308385 : CollatzResearch.WordTrace tailWord_1308385 prefixEnd_1308385 11058936397250513108977 := by
  unfold tailWord_1308385
  simp only [CollatzResearch.WordTrace]
  refine ⟨47720721364952074212998609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31813814243301382808665739 47720721364952074212998609)
  ·
    refine ⟨35790541023714055659748957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47720721364952074212998609 35790541023714055659748957)
    ·
      refine ⟨13421452883892770872405859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35790541023714055659748957 13421452883892770872405859)
      ·
        refine ⟨20132179325839156308608789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13421452883892770872405859 20132179325839156308608789)
        ·
          refine ⟨943695905898710451966037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20132179325839156308608789 943695905898710451966037)
          ·
            refine ⟨11058936397250513108977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 943695905898710451966037 11058936397250513108977)
            ·
              rfl

theorem cell21_1308385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 8].length) (baseStart_1308385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308385 prefixEnd_1308385 := by exact prefixLift 1308385
  have htrace : WordTrace (prefixWord ++ tailWord_1308385) baseStart_1308385 baseEnd_1308385 := by
    simpa [prefixWord, tailWord_1308385, baseEnd_1308385] using wordTrace_append hprefix tailTrace_1308385
  have hstable : (prefixWord ++ tailWord_1308385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308385).length < 2 ^ (prefixWord ++ tailWord_1308385).sum := by decide
  have hdescent : baseEnd_1308385 < baseStart_1308385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308399 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_1308399 : Nat := 118140960795 + 1308399 * 2 ^ 59
def prefixEnd_1308399 : Nat := 4983230072969 + 3 ^ 40 * 1308399 * 2
def baseEnd_1308399 : Nat := 298594477716502940709017

theorem tailTrace_1308399 : CollatzResearch.WordTrace tailWord_1308399 prefixEnd_1308399 298594477716502940709017 := by
  unfold tailWord_1308399
  simp only [CollatzResearch.WordTrace]
  refine ⟨47721231986901354604008251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31814154657934236402672167 47721231986901354604008251)
  ·
    refine ⟨71581847980352031906012377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47721231986901354604008251 71581847980352031906012377)
    ·
      refine ⟨53686385985264023929509283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71581847980352031906012377 53686385985264023929509283)
      ·
        refine ⟨80529578977896035894263925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53686385985264023929509283 80529578977896035894263925)
        ·
          refine ⟨7549648029177753365087243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80529578977896035894263925 7549648029177753365087243)
          ·
            refine ⟨11324472043766630047630865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7549648029177753365087243 11324472043766630047630865)
            ·
              refine ⟨8493354032824972535723149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11324472043766630047630865 8493354032824972535723149)
              ·
                refine ⟨3185007762309364700896181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8493354032824972535723149 3185007762309364700896181)
                ·
                  refine ⟨298594477716502940709017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3185007762309364700896181 298594477716502940709017)
                  ·
                    rfl

theorem cell21_1308399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_1308399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308399 prefixEnd_1308399 := by exact prefixLift 1308399
  have htrace : WordTrace (prefixWord ++ tailWord_1308399) baseStart_1308399 baseEnd_1308399 := by
    simpa [prefixWord, tailWord_1308399, baseEnd_1308399] using wordTrace_append hprefix tailTrace_1308399
  have hstable : (prefixWord ++ tailWord_1308399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308399).length < 2 ^ (prefixWord ++ tailWord_1308399).sum := by decide
  have hdescent : baseEnd_1308399 < baseStart_1308399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308444 : List Nat := [2, 2, 3, 1, 1, 2, 10]
def baseStart_1308444 : Nat := 118140960795 + 1308444 * 2 ^ 59
def prefixEnd_1308444 : Nat := 4983230072969 + 3 ^ 40 * 1308444 * 2
def baseEnd_1308444 : Nat := 33178305258843651384325

theorem tailTrace_1308444 : CollatzResearch.WordTrace tailWord_1308444 prefixEnd_1308444 33178305258843651384325 := by
  unfold tailWord_1308444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23861436635869163644698193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31815248847825551526264257 23861436635869163644698193)
  ·
    refine ⟨17896077476901872733523645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23861436635869163644698193 17896077476901872733523645)
    ·
      refine ⟨6711029053838202275071367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17896077476901872733523645 6711029053838202275071367)
      ·
        refine ⟨10066543580757303412607051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6711029053838202275071367 10066543580757303412607051)
        ·
          refine ⟨15099815371135955118910577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10066543580757303412607051 15099815371135955118910577)
          ·
            refine ⟨11324861528351966339182933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15099815371135955118910577 11324861528351966339182933)
            ·
              refine ⟨33178305258843651384325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11324861528351966339182933 33178305258843651384325)
              ·
                rfl

theorem cell21_1308444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 10].length) (baseStart_1308444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308444 prefixEnd_1308444 := by exact prefixLift 1308444
  have htrace : WordTrace (prefixWord ++ tailWord_1308444) baseStart_1308444 baseEnd_1308444 := by
    simpa [prefixWord, tailWord_1308444, baseEnd_1308444] using wordTrace_append hprefix tailTrace_1308444
  have hstable : (prefixWord ++ tailWord_1308444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308444).length < 2 ^ (prefixWord ++ tailWord_1308444).sum := by decide
  have hdescent : baseEnd_1308444 < baseStart_1308444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308478 : List Nat := [4, 2, 1, 2, 2, 1, 4, 5]
def baseStart_1308478 : Nat := 118140960795 + 1308478 * 2 ^ 59
def prefixEnd_1308478 : Nat := 4983230072969 + 3 ^ 40 * 1308478 * 2
def baseEnd_1308478 : Nat := 99537502197605452964063

theorem tailTrace_1308478 : CollatzResearch.WordTrace tailWord_1308478 prefixEnd_1308478 99537502197605452964063 := by
  unfold tailWord_1308478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965514169201893887016761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31816075569076767397422725 5965514169201893887016761)
  ·
    refine ⟨4474135626901420415262571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5965514169201893887016761 4474135626901420415262571)
    ·
      refine ⟨6711203440352130622893857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4474135626901420415262571 6711203440352130622893857)
      ·
        refine ⟨5033402580264097967170393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6711203440352130622893857 5033402580264097967170393)
        ·
          refine ⟨3775051935198073475377795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5033402580264097967170393 3775051935198073475377795)
          ·
            refine ⟨5662577902797110213066693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775051935198073475377795 5662577902797110213066693)
            ·
              refine ⟨1061733356774458164950005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5662577902797110213066693 1061733356774458164950005)
              ·
                refine ⟨99537502197605452964063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061733356774458164950005 99537502197605452964063)
                ·
                  rfl

theorem cell21_1308478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_1308478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308478 prefixEnd_1308478 := by exact prefixLift 1308478
  have htrace : WordTrace (prefixWord ++ tailWord_1308478) baseStart_1308478 baseEnd_1308478 := by
    simpa [prefixWord, tailWord_1308478, baseEnd_1308478] using wordTrace_append hprefix tailTrace_1308478
  have hstable : (prefixWord ++ tailWord_1308478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308478).length < 2 ^ (prefixWord ++ tailWord_1308478).sum := by decide
  have hdescent : baseEnd_1308478 < baseStart_1308478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308489 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1308489 : Nat := 118140960795 + 1308489 * 2 ^ 59
def prefixEnd_1308489 : Nat := 4983230072969 + 3 ^ 40 * 1308489 * 2
def baseEnd_1308489 : Nat := 298615016942682784208833

theorem tailTrace_1308489 : CollatzResearch.WordTrace tailWord_1308489 prefixEnd_1308489 298615016942682784208833 := by
  unfold tailWord_1308489
  simp only [CollatzResearch.WordTrace]
  refine ⟨47724514556575299974784521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31816343037716866649856347 47724514556575299974784521)
  ·
    refine ⟨35793385917431474981088391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47724514556575299974784521 35793385917431474981088391)
    ·
      refine ⟨53690078876147212471632587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35793385917431474981088391 53690078876147212471632587)
      ·
        refine ⟨80535118314220818707448881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53690078876147212471632587 80535118314220818707448881)
        ·
          refine ⟨60401338735665614030586661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80535118314220818707448881 60401338735665614030586661)
          ·
            refine ⟨11325251012937302630734999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60401338735665614030586661 11325251012937302630734999)
            ·
              refine ⟨16987876519405953946102499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11325251012937302630734999 16987876519405953946102499)
              ·
                refine ⟨25481814779108930919153749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16987876519405953946102499 25481814779108930919153749)
                ·
                  refine ⟨298615016942682784208833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25481814779108930919153749 298615016942682784208833)
                  ·
                    rfl

theorem cell21_1308489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1308489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308489 prefixEnd_1308489 := by exact prefixLift 1308489
  have htrace : WordTrace (prefixWord ++ tailWord_1308489) baseStart_1308489 baseEnd_1308489 := by
    simpa [prefixWord, tailWord_1308489, baseEnd_1308489] using wordTrace_append hprefix tailTrace_1308489
  have hstable : (prefixWord ++ tailWord_1308489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308489).length < 2 ^ (prefixWord ++ tailWord_1308489).sum := by decide
  have hdescent : baseEnd_1308489 < baseStart_1308489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308506 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_1308506 : Nat := 118140960795 + 1308506 * 2 ^ 59
def prefixEnd_1308506 : Nat := 4983230072969 + 3 ^ 40 * 1308506 * 2
def baseEnd_1308506 : Nat := 298618896574294532425465

theorem tailTrace_1308506 : CollatzResearch.WordTrace tailWord_1308506 prefixEnd_1308506 298618896574294532425465 := by
  unfold tailWord_1308506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931283649378427969538343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31816756398342474585435581 11931283649378427969538343)
  ·
    refine ⟨17896925474067641954307515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11931283649378427969538343 17896925474067641954307515)
    ·
      refine ⟨26845388211101462931461273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17896925474067641954307515 26845388211101462931461273)
      ·
        refine ⟨20134041158326097198595955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26845388211101462931461273 20134041158326097198595955)
        ·
          refine ⟨30201061737489145797893933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20134041158326097198595955 30201061737489145797893933)
          ·
            refine ⟨11325398151558429674210225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30201061737489145797893933 11325398151558429674210225)
            ·
              refine ⟨8494048613668822255657669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11325398151558429674210225 8494048613668822255657669)
              ·
                refine ⟨1592634115062904172935813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8494048613668822255657669 1592634115062904172935813)
                ·
                  refine ⟨298618896574294532425465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592634115062904172935813 298618896574294532425465)
                  ·
                    rfl

theorem cell21_1308506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_1308506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308506 prefixEnd_1308506 := by exact prefixLift 1308506
  have htrace : WordTrace (prefixWord ++ tailWord_1308506) baseStart_1308506 baseEnd_1308506 := by
    simpa [prefixWord, tailWord_1308506, baseEnd_1308506] using wordTrace_append hprefix tailTrace_1308506
  have hstable : (prefixWord ++ tailWord_1308506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308506).length < 2 ^ (prefixWord ++ tailWord_1308506).sum := by decide
  have hdescent : baseEnd_1308506 < baseStart_1308506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308647 : List Nat := [1, 1, 5, 2, 4, 1, 2, 5]
def baseStart_1308647 : Nat := 118140960795 + 1308647 * 2 ^ 59
def prefixEnd_1308647 : Nat := 4983230072969 + 3 ^ 40 * 1308647 * 2
def baseEnd_1308647 : Nat := 99550358231769873525059

theorem tailTrace_1308647 : CollatzResearch.WordTrace tailWord_1308647 prefixEnd_1308647 99550358231769873525059 := by
  unfold tailWord_1308647
  simp only [CollatzResearch.WordTrace]
  refine ⟨47730277290002892959036195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31820184860001928639357463 47730277290002892959036195)
  ·
    refine ⟨71595415935004339438554293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47730277290002892959036195 71595415935004339438554293)
    ·
      refine ⟨6712070243906656822364465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71595415935004339438554293 6712070243906656822364465)
      ·
        refine ⟨5034052682929992616773349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6712070243906656822364465 5034052682929992616773349)
        ·
          refine ⟨943884878049373615645003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5034052682929992616773349 943884878049373615645003)
          ·
            refine ⟨1415827317074060423467505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943884878049373615645003 1415827317074060423467505)
            ·
              refine ⟨1061870487805545317600629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415827317074060423467505 1061870487805545317600629)
              ·
                refine ⟨99550358231769873525059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1061870487805545317600629 99550358231769873525059)
                ·
                  rfl

theorem cell21_1308647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 5].length) (baseStart_1308647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308647 prefixEnd_1308647 := by exact prefixLift 1308647
  have htrace : WordTrace (prefixWord ++ tailWord_1308647) baseStart_1308647 baseEnd_1308647 := by
    simpa [prefixWord, tailWord_1308647, baseEnd_1308647] using wordTrace_append hprefix tailTrace_1308647
  have hstable : (prefixWord ++ tailWord_1308647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308647).length < 2 ^ (prefixWord ++ tailWord_1308647).sum := by decide
  have hdescent : baseEnd_1308647 < baseStart_1308647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308737 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 3]
def baseStart_1308737 : Nat := 118140960795 + 1308737 * 2 ^ 59
def prefixEnd_1308737 : Nat := 4983230072969 + 3 ^ 40 * 1308737 * 2
def baseEnd_1308737 : Nat := 298671613921489464074993

theorem tailTrace_1308737 : CollatzResearch.WordTrace tailWord_1308737 prefixEnd_1308737 298671613921489464074993 := by
  unfold tailWord_1308737
  simp only [CollatzResearch.WordTrace]
  refine ⟨47733559859676838329812465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31822373239784558886541643 47733559859676838329812465)
  ·
    refine ⟨35800169894757628747359349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47733559859676838329812465 35800169894757628747359349)
    ·
      refine ⟨3356265927633527695064939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35800169894757628747359349 3356265927633527695064939)
      ·
        refine ⟨5034398891450291542597409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356265927633527695064939 5034398891450291542597409)
        ·
          refine ⟨3775799168587718656948057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034398891450291542597409 3775799168587718656948057)
          ·
            refine ⟨2831849376440788992711043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775799168587718656948057 2831849376440788992711043)
            ·
              refine ⟨4247774064661183489066565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831849376440788992711043 4247774064661183489066565)
              ·
                refine ⟨796457637123971904199981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4247774064661183489066565 796457637123971904199981)
                ·
                  refine ⟨298671613921489464074993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796457637123971904199981 298671613921489464074993)
                  ·
                    rfl

theorem cell21_1308737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_1308737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308737 prefixEnd_1308737 := by exact prefixLift 1308737
  have htrace : WordTrace (prefixWord ++ tailWord_1308737) baseStart_1308737 baseEnd_1308737 := by
    simpa [prefixWord, tailWord_1308737, baseEnd_1308737] using wordTrace_append hprefix tailTrace_1308737
  have hstable : (prefixWord ++ tailWord_1308737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308737).length < 2 ^ (prefixWord ++ tailWord_1308737).sum := by decide
  have hdescent : baseEnd_1308737 < baseStart_1308737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308748 : List Nat := [2, 2, 1, 3, 1, 1, 5, 6]
def baseStart_1308748 : Nat := 118140960795 + 1308748 * 2 ^ 59
def prefixEnd_1308748 : Nat := 4983230072969 + 3 ^ 40 * 1308748 * 2
def baseEnd_1308748 : Nat := 99558041423785296463879

theorem tailTrace_1308748 : CollatzResearch.WordTrace tailWord_1308748 prefixEnd_1308748 99558041423785296463879 := by
  unfold tailWord_1308748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23866980531318493604231449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31822640708424658138975265 23866980531318493604231449)
  ·
    refine ⟨17900235398488870203173587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23866980531318493604231449 17900235398488870203173587)
    ·
      refine ⟨26850353097733305304760381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17900235398488870203173587 26850353097733305304760381)
      ·
        refine ⟨10068882411649989489285143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26850353097733305304760381 10068882411649989489285143)
        ·
          refine ⟨15103323617474984233927715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10068882411649989489285143 15103323617474984233927715)
          ·
            refine ⟨22654985426212476350891573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15103323617474984233927715 22654985426212476350891573)
            ·
              refine ⟨2123904883707419657896085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22654985426212476350891573 2123904883707419657896085)
              ·
                refine ⟨99558041423785296463879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2123904883707419657896085 99558041423785296463879)
                ·
                  rfl

theorem cell21_1308748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_1308748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308748 prefixEnd_1308748 := by exact prefixLift 1308748
  have htrace : WordTrace (prefixWord ++ tailWord_1308748) baseStart_1308748 baseEnd_1308748 := by
    simpa [prefixWord, tailWord_1308748, baseEnd_1308748] using wordTrace_append hprefix tailTrace_1308748
  have hstable : (prefixWord ++ tailWord_1308748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308748).length < 2 ^ (prefixWord ++ tailWord_1308748).sum := by decide
  have hdescent : baseEnd_1308748 < baseStart_1308748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308796 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1308796 : Nat := 118140960795 + 1308796 * 2 ^ 59
def prefixEnd_1308796 : Nat := 4983230072969 + 3 ^ 40 * 1308796 * 2
def baseEnd_1308796 : Nat := 298685078525318472591539

theorem tailTrace_1308796 : CollatzResearch.WordTrace tailWord_1308796 prefixEnd_1308796 298685078525318472591539 := by
  unfold tailWord_1308796
  simp only [CollatzResearch.WordTrace]
  refine ⟨23867855883231545703105121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31823807844308727604140161 23867855883231545703105121)
  ·
    refine ⟨17900891912423659277328841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23867855883231545703105121 17900891912423659277328841)
    ·
      refine ⟨13425668934317744457996631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17900891912423659277328841 13425668934317744457996631)
      ·
        refine ⟨20138503401476616686994947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13425668934317744457996631 20138503401476616686994947)
        ·
          refine ⟨30207755102214925030492421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20138503401476616686994947 30207755102214925030492421)
          ·
            refine ⟨5663954081665298443217329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30207755102214925030492421 5663954081665298443217329)
            ·
              refine ⟨4247965561248973832412997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663954081665298443217329 4247965561248973832412997)
              ·
                refine ⟨796493542734182593577437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4247965561248973832412997 796493542734182593577437)
                ·
                  refine ⟨298685078525318472591539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796493542734182593577437 298685078525318472591539)
                  ·
                    rfl

theorem cell21_1308796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1308796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308796 prefixEnd_1308796 := by exact prefixLift 1308796
  have htrace : WordTrace (prefixWord ++ tailWord_1308796) baseStart_1308796 baseEnd_1308796 := by
    simpa [prefixWord, tailWord_1308796, baseEnd_1308796] using wordTrace_append hprefix tailTrace_1308796
  have hstable : (prefixWord ++ tailWord_1308796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308796).length < 2 ^ (prefixWord ++ tailWord_1308796).sum := by decide
  have hdescent : baseEnd_1308796 < baseStart_1308796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308822 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1308822 : Nat := 118140960795 + 1308822 * 2 ^ 59
def prefixEnd_1308822 : Nat := 4983230072969 + 3 ^ 40 * 1308822 * 2
def baseEnd_1308822 : Nat := 298691012079548205158153

theorem tailTrace_1308822 : CollatzResearch.WordTrace tailWord_1308822 prefixEnd_1308822 298691012079548205158153 := by
  unfold tailWord_1308822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983541254023056115416045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31824440042912598564437813 2983541254023056115416045)
  ·
    refine ⟨1118827970258646043281017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2983541254023056115416045 1118827970258646043281017)
    ·
      refine ⟨839120977693984532460763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118827970258646043281017 839120977693984532460763)
      ·
        refine ⟨1258681466540976798691145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839120977693984532460763 1258681466540976798691145)
        ·
          refine ⟨944011099905732599018359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258681466540976798691145 944011099905732599018359)
          ·
            refine ⟨1416016649858598898527539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944011099905732599018359 1416016649858598898527539)
            ·
              refine ⟨2124024974787898347791309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416016649858598898527539 2124024974787898347791309)
              ·
                refine ⟨796509365545461880421741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2124024974787898347791309 796509365545461880421741)
                ·
                  refine ⟨298691012079548205158153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796509365545461880421741 298691012079548205158153)
                  ·
                    rfl

theorem cell21_1308822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1308822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308822 prefixEnd_1308822 := by exact prefixLift 1308822
  have htrace : WordTrace (prefixWord ++ tailWord_1308822) baseStart_1308822 baseEnd_1308822 := by
    simpa [prefixWord, tailWord_1308822, baseEnd_1308822] using wordTrace_append hprefix tailTrace_1308822
  have hstable : (prefixWord ++ tailWord_1308822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308822).length < 2 ^ (prefixWord ++ tailWord_1308822).sum := by decide
  have hdescent : baseEnd_1308822 < baseStart_1308822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308855 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 5]
def baseStart_1308855 : Nat := 118140960795 + 1308855 * 2 ^ 59
def prefixEnd_1308855 : Nat := 4983230072969 + 3 ^ 40 * 1308855 * 2
def baseEnd_1308855 : Nat := 298698543129147481108085

theorem tailTrace_1308855 : CollatzResearch.WordTrace tailWord_1308855 prefixEnd_1308855 298698543129147481108085 := by
  unfold tailWord_1308855
  simp only [CollatzResearch.WordTrace]
  refine ⟨47737863673249344482608019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31825242448832896321738679 47737863673249344482608019)
  ·
    refine ⟨71606795509874016723912029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47737863673249344482608019 71606795509874016723912029)
    ·
      refine ⟨26852548316202756271467011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71606795509874016723912029 26852548316202756271467011)
      ·
        refine ⟨40278822474304134407200517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26852548316202756271467011 40278822474304134407200517)
        ·
          refine ⟨7552279213932025201350097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40278822474304134407200517 7552279213932025201350097)
          ·
            refine ⟨5664209410449018901012573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7552279213932025201350097 5664209410449018901012573)
            ·
              refine ⟨2124078528918382087879715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664209410449018901012573 2124078528918382087879715)
              ·
                refine ⟨3186117793377573131819573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124078528918382087879715 3186117793377573131819573)
                ·
                  refine ⟨298698543129147481108085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3186117793377573131819573 298698543129147481108085)
                  ·
                    rfl

theorem cell21_1308855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 5].length) (baseStart_1308855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308855 prefixEnd_1308855 := by exact prefixLift 1308855
  have htrace : WordTrace (prefixWord ++ tailWord_1308855) baseStart_1308855 baseEnd_1308855 := by
    simpa [prefixWord, tailWord_1308855, baseEnd_1308855] using wordTrace_append hprefix tailTrace_1308855
  have hstable : (prefixWord ++ tailWord_1308855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308855).length < 2 ^ (prefixWord ++ tailWord_1308855).sum := by decide
  have hdescent : baseEnd_1308855 < baseStart_1308855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308903 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_1308903 : Nat := 118140960795 + 1308903 * 2 ^ 59
def prefixEnd_1308903 : Nat := 4983230072969 + 3 ^ 40 * 1308903 * 2
def baseEnd_1308903 : Nat := 298709497383110064307987

theorem tailTrace_1308903 : CollatzResearch.WordTrace tailWord_1308903 prefixEnd_1308903 298709497383110064307987 := by
  unfold tailWord_1308903
  simp only [CollatzResearch.WordTrace]
  refine ⟨47739614377075448680355363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31826409584716965786903575 47739614377075448680355363)
  ·
    refine ⟨71609421565613173020533045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47739614377075448680355363 71609421565613173020533045)
    ·
      refine ⟨6713383271776234970674973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71609421565613173020533045 6713383271776234970674973)
      ·
        refine ⟨2517518726916088114003115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6713383271776234970674973 2517518726916088114003115)
        ·
          refine ⟨3776278090374132171004673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517518726916088114003115 3776278090374132171004673)
          ·
            refine ⟨2832208567780599128253505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776278090374132171004673 2832208567780599128253505)
            ·
              refine ⟨2124156425835449346190129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2832208567780599128253505 2124156425835449346190129)
              ·
                refine ⟨1593117319376587009642597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124156425835449346190129 1593117319376587009642597)
                ·
                  refine ⟨298709497383110064307987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1593117319376587009642597 298709497383110064307987)
                  ·
                    rfl

theorem cell21_1308903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_1308903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308903 prefixEnd_1308903 := by exact prefixLift 1308903
  have htrace : WordTrace (prefixWord ++ tailWord_1308903) baseStart_1308903 baseEnd_1308903 := by
    simpa [prefixWord, tailWord_1308903, baseEnd_1308903] using wordTrace_append hprefix tailTrace_1308903
  have hstable : (prefixWord ++ tailWord_1308903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308903).length < 2 ^ (prefixWord ++ tailWord_1308903).sum := by decide
  have hdescent : baseEnd_1308903 < baseStart_1308903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308962 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1308962 : Nat := 118140960795 + 1308962 * 2 ^ 59
def prefixEnd_1308962 : Nat := 4983230072969 + 3 ^ 40 * 1308962 * 2
def baseEnd_1308962 : Nat := 298722961986939072824533

theorem tailTrace_1308962 : CollatzResearch.WordTrace tailWord_1308962 prefixEnd_1308962 298722961986939072824533 := by
  unfold tailWord_1308962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935441570965425439188285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31827844189241134504502093 11935441570965425439188285)
  ·
    refine ⟨4475790589112034539695607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11935441570965425439188285 4475790589112034539695607)
    ·
      refine ⟨6713685883668051809543411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475790589112034539695607 6713685883668051809543411)
      ·
        refine ⟨10070528825502077714315117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713685883668051809543411 10070528825502077714315117)
        ·
          refine ⟨3776448309563279142868169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10070528825502077714315117 3776448309563279142868169)
          ·
            refine ⟨2832336232172459357151127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776448309563279142868169 2832336232172459357151127)
            ·
              refine ⟨4248504348258689035726691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832336232172459357151127 4248504348258689035726691)
              ·
                refine ⟨6372756522388033553590037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248504348258689035726691 6372756522388033553590037)
                ·
                  refine ⟨298722961986939072824533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6372756522388033553590037 298722961986939072824533)
                  ·
                    rfl

theorem cell21_1308962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1308962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308962 prefixEnd_1308962 := by exact prefixLift 1308962
  have htrace : WordTrace (prefixWord ++ tailWord_1308962) baseStart_1308962 baseEnd_1308962 := by
    simpa [prefixWord, tailWord_1308962, baseEnd_1308962] using wordTrace_append hprefix tailTrace_1308962
  have hstable : (prefixWord ++ tailWord_1308962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308962).length < 2 ^ (prefixWord ++ tailWord_1308962).sum := by decide
  have hdescent : baseEnd_1308962 < baseStart_1308962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308993 : List Nat := [1, 2, 5, 2, 2, 1, 1, 7]
def baseStart_1308993 : Nat := 118140960795 + 1308993 * 2 ^ 59
def prefixEnd_1308993 : Nat := 4983230072969 + 3 ^ 40 * 1308993 * 2
def baseEnd_1308993 : Nat := 99576678869763302602601

theorem tailTrace_1308993 : CollatzResearch.WordTrace tailWord_1308993 prefixEnd_1308993 99576678869763302602601 := by
  unfold tailWord_1308993
  simp only [CollatzResearch.WordTrace]
  refine ⟨47742896946749394051131633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31828597964499596034087755 47742896946749394051131633)
  ·
    refine ⟨35807172710062045538348725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47742896946749394051131633 35807172710062045538348725)
    ·
      refine ⟨3356922441568316769220193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35807172710062045538348725 3356922441568316769220193)
      ·
        refine ⟨2517691831176237576915145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3356922441568316769220193 2517691831176237576915145)
        ·
          refine ⟨1888268873382178182686359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2517691831176237576915145 1888268873382178182686359)
          ·
            refine ⟨2832403310073267274029539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888268873382178182686359 2832403310073267274029539)
            ·
              refine ⟨4248604965109900911044309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832403310073267274029539 4248604965109900911044309)
              ·
                refine ⟨99576678869763302602601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4248604965109900911044309 99576678869763302602601)
                ·
                  rfl

theorem cell21_1308993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_1308993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1308993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1308993 prefixEnd_1308993 := by exact prefixLift 1308993
  have htrace : WordTrace (prefixWord ++ tailWord_1308993) baseStart_1308993 baseEnd_1308993 := by
    simpa [prefixWord, tailWord_1308993, baseEnd_1308993] using wordTrace_append hprefix tailTrace_1308993
  have hstable : (prefixWord ++ tailWord_1308993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308993).length < 2 ^ (prefixWord ++ tailWord_1308993).sum := by decide
  have hdescent : baseEnd_1308993 < baseStart_1308993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309007 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 3]
def baseStart_1309007 : Nat := 118140960795 + 1309007 * 2 ^ 59
def prefixEnd_1309007 : Nat := 4983230072969 + 3 ^ 40 * 1309007 * 2
def baseEnd_1309007 : Nat := 298733231600028994574441

theorem tailTrace_1309007 : CollatzResearch.WordTrace tailWord_1309007 prefixEnd_1309007 298733231600028994574441 := by
  unfold tailWord_1309007
  simp only [CollatzResearch.WordTrace]
  refine ⟨47743407568698674442141275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31828938379132449628094183 47743407568698674442141275)
  ·
    refine ⟨71615111353048011663211913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47743407568698674442141275 71615111353048011663211913)
    ·
      refine ⟨53711333514786008747408935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71615111353048011663211913 53711333514786008747408935)
      ·
        refine ⟨80567000272179013121113403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53711333514786008747408935 80567000272179013121113403)
        ·
          refine ⟨120850500408268519681670105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80567000272179013121113403 120850500408268519681670105)
          ·
            refine ⟨90637875306201389761252579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120850500408268519681670105 90637875306201389761252579)
            ·
              refine ⟨135956812959302084641878869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90637875306201389761252579 135956812959302084641878869)
              ·
                refine ⟨796621950933410652198509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 135956812959302084641878869 796621950933410652198509)
                ·
                  refine ⟨298733231600028994574441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796621950933410652198509 298733231600028994574441)
                  ·
                    rfl

theorem cell21_1309007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3].length) (baseStart_1309007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309007 prefixEnd_1309007 := by exact prefixLift 1309007
  have htrace : WordTrace (prefixWord ++ tailWord_1309007) baseStart_1309007 baseEnd_1309007 := by
    simpa [prefixWord, tailWord_1309007, baseEnd_1309007] using wordTrace_append hprefix tailTrace_1309007
  have hstable : (prefixWord ++ tailWord_1309007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309007).length < 2 ^ (prefixWord ++ tailWord_1309007).sum := by decide
  have hdescent : baseEnd_1309007 < baseStart_1309007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309024 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_1309024 : Nat := 118140960795 + 1309024 * 2 ^ 59
def prefixEnd_1309024 : Nat := 4983230072969 + 3 ^ 40 * 1309024 * 2
def baseEnd_1309024 : Nat := 298737111231640742791073

theorem tailTrace_1309024 : CollatzResearch.WordTrace tailWord_1309024 prefixEnd_1309024 298737111231640742791073 := by
  unfold tailWord_1309024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23872013804818543172755063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31829351739758057563673417 23872013804818543172755063)
  ·
    refine ⟨35808020707227814759132595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23872013804818543172755063 35808020707227814759132595)
    ·
      refine ⟨53712031060841722138698893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35808020707227814759132595 53712031060841722138698893)
      ·
        refine ⟨20142011647815645802012085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53712031060841722138698893 20142011647815645802012085)
        ·
          refine ⟨1888313591982716793938633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20142011647815645802012085 1888313591982716793938633)
          ·
            refine ⟨1416235193987037595453975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888313591982716793938633 1416235193987037595453975)
            ·
              refine ⟨2124352790980556393180963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416235193987037595453975 2124352790980556393180963)
              ·
                refine ⟨3186529186470834589771445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124352790980556393180963 3186529186470834589771445)
                ·
                  refine ⟨298737111231640742791073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3186529186470834589771445 298737111231640742791073)
                  ·
                    rfl

theorem cell21_1309024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_1309024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309024 prefixEnd_1309024 := by exact prefixLift 1309024
  have htrace : WordTrace (prefixWord ++ tailWord_1309024) baseStart_1309024 baseEnd_1309024 := by
    simpa [prefixWord, tailWord_1309024, baseEnd_1309024] using wordTrace_append hprefix tailTrace_1309024
  have hstable : (prefixWord ++ tailWord_1309024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309024).length < 2 ^ (prefixWord ++ tailWord_1309024).sum := by decide
  have hdescent : baseEnd_1309024 < baseStart_1309024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309086 : List Nat := [4, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1309086 : Nat := 118140960795 + 1309086 * 2 ^ 59
def prefixEnd_1309086 : Nat := 4983230072969 + 3 ^ 40 * 1309086 * 2
def baseEnd_1309086 : Nat := 99583753492114137585871

theorem tailTrace_1309086 : CollatzResearch.WordTrace tailWord_1309086 prefixEnd_1309086 99583753492114137585871 := by
  unfold tailWord_1309086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968286116926558866783389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31830859290274980622844741 5968286116926558866783389)
  ·
    refine ⟨2238107293847459575043771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5968286116926558866783389 2238107293847459575043771)
    ·
      refine ⟨3357160940771189362565657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238107293847459575043771 3357160940771189362565657)
      ·
        refine ⟨2517870705578392021924243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3357160940771189362565657 2517870705578392021924243)
        ·
          refine ⟨3776806058367588032886365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517870705578392021924243 3776806058367588032886365)
          ·
            refine ⟨1416302271887845512332387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3776806058367588032886365 1416302271887845512332387)
            ·
              refine ⟨2124453407831768268498581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416302271887845512332387 2124453407831768268498581)
              ·
                refine ⟨99583753492114137585871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2124453407831768268498581 99583753492114137585871)
                ·
                  rfl

theorem cell21_1309086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1309086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309086 prefixEnd_1309086 := by exact prefixLift 1309086
  have htrace : WordTrace (prefixWord ++ tailWord_1309086) baseStart_1309086 baseEnd_1309086 := by
    simpa [prefixWord, tailWord_1309086, baseEnd_1309086] using wordTrace_append hprefix tailTrace_1309086
  have hstable : (prefixWord ++ tailWord_1309086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309086).length < 2 ^ (prefixWord ++ tailWord_1309086).sum := by decide
  have hdescent : baseEnd_1309086 < baseStart_1309086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309207 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 4]
def baseStart_1309207 : Nat := 118140960795 + 1309207 * 2 ^ 59
def prefixEnd_1309207 : Nat := 4983230072969 + 3 ^ 40 * 1309207 * 2
def baseEnd_1309207 : Nat := 298778874324873091240699

theorem tailTrace_1309207 : CollatzResearch.WordTrace tailWord_1309207 prefixEnd_1309207 298778874324873091240699 := by
  unfold tailWord_1309207
  simp only [CollatzResearch.WordTrace]
  refine ⟨47750702167974108599421875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31833801445316072399614583 47750702167974108599421875)
  ·
    refine ⟨71626053251961162899132813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47750702167974108599421875 71626053251961162899132813)
    ·
      refine ⟨26859769969485436087174805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71626053251961162899132813 26859769969485436087174805)
      ·
        refine ⟨1259051717319629816586319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26859769969485436087174805 1259051717319629816586319)
        ·
          refine ⟨1888577575979444724879479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259051717319629816586319 1888577575979444724879479)
          ·
            refine ⟨2832866363969167087319219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888577575979444724879479 2832866363969167087319219)
            ·
              refine ⟨4249299545953750630978829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832866363969167087319219 4249299545953750630978829)
              ·
                refine ⟨1593487329732656486617061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249299545953750630978829 1593487329732656486617061)
                ·
                  refine ⟨298778874324873091240699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1593487329732656486617061 298778874324873091240699)
                  ·
                    rfl

theorem cell21_1309207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_1309207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309207 prefixEnd_1309207 := by exact prefixLift 1309207
  have htrace : WordTrace (prefixWord ++ tailWord_1309207) baseStart_1309207 baseEnd_1309207 := by
    simpa [prefixWord, tailWord_1309207, baseEnd_1309207] using wordTrace_append hprefix tailTrace_1309207
  have hstable : (prefixWord ++ tailWord_1309207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309207).length < 2 ^ (prefixWord ++ tailWord_1309207).sum := by decide
  have hdescent : baseEnd_1309207 < baseStart_1309207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309218 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1309218 : Nat := 118140960795 + 1309218 * 2 ^ 59
def prefixEnd_1309218 : Nat := 4983230072969 + 3 ^ 40 * 1309218 * 2
def baseEnd_1309218 : Nat := 298781384674739516557343

theorem tailTrace_1309218 : CollatzResearch.WordTrace tailWord_1309218 prefixEnd_1309218 298781384674739516557343 := by
  unfold tailWord_1309218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937775842733564369518077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31834068913956171652048205 11937775842733564369518077)
  ·
    refine ⟨4476665941025086638569279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11937775842733564369518077 4476665941025086638569279)
    ·
      refine ⟨6714998911537629957853919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4476665941025086638569279 6714998911537629957853919)
      ·
        refine ⟨10072498367306444936780879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714998911537629957853919 10072498367306444936780879)
        ·
          refine ⟨15108747550959667405171319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072498367306444936780879 15108747550959667405171319)
          ·
            refine ⟨22663121326439501107756979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15108747550959667405171319 22663121326439501107756979)
            ·
              refine ⟨33994681989659251661635469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22663121326439501107756979 33994681989659251661635469)
              ·
                refine ⟨12748005746122219373113301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33994681989659251661635469 12748005746122219373113301)
                ·
                  refine ⟨298781384674739516557343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12748005746122219373113301 298781384674739516557343)
                  ·
                    rfl

theorem cell21_1309218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1309218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309218 prefixEnd_1309218 := by exact prefixLift 1309218
  have htrace : WordTrace (prefixWord ++ tailWord_1309218) baseStart_1309218 baseEnd_1309218 := by
    simpa [prefixWord, tailWord_1309218, baseEnd_1309218] using wordTrace_append hprefix tailTrace_1309218
  have hstable : (prefixWord ++ tailWord_1309218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309218).length < 2 ^ (prefixWord ++ tailWord_1309218).sum := by decide
  have hdescent : baseEnd_1309218 < baseStart_1309218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309232 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_1309232 : Nat := 118140960795 + 1309232 * 2 ^ 59
def prefixEnd_1309232 : Nat := 4983230072969 + 3 ^ 40 * 1309232 * 2
def baseEnd_1309232 : Nat := 298784579665478603323981

theorem tailTrace_1309232 : CollatzResearch.WordTrace tailWord_1309232 prefixEnd_1309232 298784579665478603323981 := by
  unfold tailWord_1309232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23875806996441768934540975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31834409328589025246054633 23875806996441768934540975)
  ·
    refine ⟨35813710494662653401811463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23875806996441768934540975 35813710494662653401811463)
    ·
      refine ⟨53720565741993980102717195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35813710494662653401811463 53720565741993980102717195)
      ·
        refine ⟨80580848612990970154075793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53720565741993980102717195 80580848612990970154075793)
        ·
          refine ⟨60435636459743227615556845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80580848612990970154075793 60435636459743227615556845)
          ·
            refine ⟨22663363672403710355833817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60435636459743227615556845 22663363672403710355833817)
            ·
              refine ⟨16997522754302782766875363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22663363672403710355833817 16997522754302782766875363)
              ·
                refine ⟨25496284131454174150313045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16997522754302782766875363 25496284131454174150313045)
                ·
                  refine ⟨298784579665478603323981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25496284131454174150313045 298784579665478603323981)
                  ·
                    rfl

theorem cell21_1309232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_1309232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309232 prefixEnd_1309232 := by exact prefixLift 1309232
  have htrace : WordTrace (prefixWord ++ tailWord_1309232) baseStart_1309232 baseEnd_1309232 := by
    simpa [prefixWord, tailWord_1309232, baseEnd_1309232] using wordTrace_append hprefix tailTrace_1309232
  have hstable : (prefixWord ++ tailWord_1309232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309232).length < 2 ^ (prefixWord ++ tailWord_1309232).sum := by decide
  have hdescent : baseEnd_1309232 < baseStart_1309232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309235 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 3]
def baseStart_1309235 : Nat := 118140960795 + 1309235 * 2 ^ 59
def prefixEnd_1309235 : Nat := 4983230072969 + 3 ^ 40 * 1309235 * 2
def baseEnd_1309235 : Nat := 298785264306351264773975

theorem tailTrace_1309235 : CollatzResearch.WordTrace tailWord_1309235 prefixEnd_1309235 298785264306351264773975 := by
  unfold tailWord_1309235
  simp only [CollatzResearch.WordTrace]
  refine ⟨47751723411872669381441159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31834482274581779587627439 47751723411872669381441159)
  ·
    refine ⟨71627585117809004072161739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47751723411872669381441159 71627585117809004072161739)
    ·
      refine ⟨107441377676713506108242609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71627585117809004072161739 107441377676713506108242609)
      ·
        refine ⟨80581033257535129581181957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107441377676713506108242609 80581033257535129581181957)
        ·
          refine ⟨15108943735787836796471617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80581033257535129581181957 15108943735787836796471617)
          ·
            refine ⟨11331707801840877597353713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15108943735787836796471617 11331707801840877597353713)
            ·
              refine ⟨8498780851380658198015285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11331707801840877597353713 8498780851380658198015285)
              ·
                refine ⟨796760704816936706063933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8498780851380658198015285 796760704816936706063933)
                ·
                  refine ⟨298785264306351264773975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796760704816936706063933 298785264306351264773975)
                  ·
                    rfl

theorem cell21_1309235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 3].length) (baseStart_1309235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309235 prefixEnd_1309235 := by exact prefixLift 1309235
  have htrace : WordTrace (prefixWord ++ tailWord_1309235) baseStart_1309235 baseEnd_1309235 := by
    simpa [prefixWord, tailWord_1309235, baseEnd_1309235] using wordTrace_append hprefix tailTrace_1309235
  have hstable : (prefixWord ++ tailWord_1309235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309235).length < 2 ^ (prefixWord ++ tailWord_1309235).sum := by decide
  have hdescent : baseEnd_1309235 < baseStart_1309235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309263 : List Nat := [1, 1, 2, 1, 1, 2, 7, 6]
def baseStart_1309263 : Nat := 118140960795 + 1309263 * 2 ^ 59
def prefixEnd_1309263 : Nat := 4983230072969 + 3 ^ 40 * 1309263 * 2
def baseEnd_1309263 : Nat := 99597218095943146102417

theorem tailTrace_1309263 : CollatzResearch.WordTrace tailWord_1309263 prefixEnd_1309263 99597218095943146102417 := by
  unfold tailWord_1309263
  simp only [CollatzResearch.WordTrace]
  refine ⟨47752744655771230163460443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31835163103847486775640295 47752744655771230163460443)
  ·
    refine ⟨71629116983656845245190665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47752744655771230163460443 71629116983656845245190665)
    ·
      refine ⟨53721837737742633933892999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71629116983656845245190665 53721837737742633933892999)
      ·
        refine ⟨80582756606613950900839499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53721837737742633933892999 80582756606613950900839499)
        ·
          refine ⟨120874134909920926351259249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80582756606613950900839499 120874134909920926351259249)
          ·
            refine ⟨90655601182440694763444437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120874134909920926351259249 90655601182440694763444437)
            ·
              refine ⟨2124740652713453783518229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90655601182440694763444437 2124740652713453783518229)
              ·
                refine ⟨99597218095943146102417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2124740652713453783518229 99597218095943146102417)
                ·
                  rfl

theorem cell21_1309263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_1309263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309263 prefixEnd_1309263 := by exact prefixLift 1309263
  have htrace : WordTrace (prefixWord ++ tailWord_1309263) baseStart_1309263 baseEnd_1309263 := by
    simpa [prefixWord, tailWord_1309263, baseEnd_1309263] using wordTrace_append hprefix tailTrace_1309263
  have hstable : (prefixWord ++ tailWord_1309263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309263).length < 2 ^ (prefixWord ++ tailWord_1309263).sum := by decide
  have hdescent : baseEnd_1309263 < baseStart_1309263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309345 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 3]
def baseStart_1309345 : Nat := 118140960795 + 1309345 * 2 ^ 59
def prefixEnd_1309345 : Nat := 4983230072969 + 3 ^ 40 * 1309345 * 2
def baseEnd_1309345 : Nat := 298810367805015517940417

theorem tailTrace_1309345 : CollatzResearch.WordTrace tailWord_1309345 prefixEnd_1309345 298810367805015517940417 := by
  unfold tailWord_1309345
  simp only [CollatzResearch.WordTrace]
  refine ⟨47755735441474158167945489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31837156960982772111963659 47755735441474158167945489)
  ·
    refine ⟨35816801581105618625959117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47755735441474158167945489 35816801581105618625959117)
    ·
      refine ⟨13431300592914606984734669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35816801581105618625959117 13431300592914606984734669)
      ·
        refine ⟨5036737722342977619275501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13431300592914606984734669 5036737722342977619275501)
        ·
          refine ⟨1888776645878616607228313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5036737722342977619275501 1888776645878616607228313)
          ·
            refine ⟨1416582484408962455421235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888776645878616607228313 1416582484408962455421235)
            ·
              refine ⟨2124873726613443683131853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416582484408962455421235 2124873726613443683131853)
              ·
                refine ⟨796827647480041381174445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2124873726613443683131853 796827647480041381174445)
                ·
                  refine ⟨298810367805015517940417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796827647480041381174445 298810367805015517940417)
                  ·
                    rfl

theorem cell21_1309345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_1309345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309345 prefixEnd_1309345 := by exact prefixLift 1309345
  have htrace : WordTrace (prefixWord ++ tailWord_1309345) baseStart_1309345 baseEnd_1309345 := by
    simpa [prefixWord, tailWord_1309345, baseEnd_1309345] using wordTrace_append hprefix tailTrace_1309345
  have hstable : (prefixWord ++ tailWord_1309345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309345).length < 2 ^ (prefixWord ++ tailWord_1309345).sum := by decide
  have hdescent : baseEnd_1309345 < baseStart_1309345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309353 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1309353 : Nat := 118140960795 + 1309353 * 2 ^ 59
def prefixEnd_1309353 : Nat := 4983230072969 + 3 ^ 40 * 1309353 * 2
def baseEnd_1309353 : Nat := 298812193514009281807067

theorem tailTrace_1309353 : CollatzResearch.WordTrace tailWord_1309353 prefixEnd_1309353 298812193514009281807067 := by
  unfold tailWord_1309353
  simp only [CollatzResearch.WordTrace]
  refine ⟨47756027225445175534236713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31837351483630117022824475 47756027225445175534236713)
  ·
    refine ⟨35817020419083881650677535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47756027225445175534236713 35817020419083881650677535)
    ·
      refine ⟨53725530628625822476016303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35817020419083881650677535 53725530628625822476016303)
      ·
        refine ⟨80588295942938733714024455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53725530628625822476016303 80588295942938733714024455)
        ·
          refine ⟨120882443914408100571036683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80588295942938733714024455 120882443914408100571036683)
          ·
            refine ⟨181323665871612150856555025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120882443914408100571036683 181323665871612150856555025)
            ·
              refine ⟨135992749403709113142416269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181323665871612150856555025 135992749403709113142416269)
              ·
                refine ⟨50997281026390917428406101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135992749403709113142416269 50997281026390917428406101)
                ·
                  refine ⟨298812193514009281807067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50997281026390917428406101 298812193514009281807067)
                  ·
                    rfl

theorem cell21_1309353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1309353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309353 prefixEnd_1309353 := by exact prefixLift 1309353
  have htrace : WordTrace (prefixWord ++ tailWord_1309353) baseStart_1309353 baseEnd_1309353 := by
    simpa [prefixWord, tailWord_1309353, baseEnd_1309353] using wordTrace_append hprefix tailTrace_1309353
  have hstable : (prefixWord ++ tailWord_1309353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309353).length < 2 ^ (prefixWord ++ tailWord_1309353).sum := by decide
  have hdescent : baseEnd_1309353 < baseStart_1309353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309536 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_1309536 : Nat := 118140960795 + 1309536 * 2 ^ 59
def prefixEnd_1309536 : Nat := 4983230072969 + 3 ^ 40 * 1309536 * 2
def baseEnd_1309536 : Nat := 298853956607241630256693

theorem tailTrace_1309536 : CollatzResearch.WordTrace tailWord_1309536 prefixEnd_1309536 298853956607241630256693 := by
  unfold tailWord_1309536
  simp only [CollatzResearch.WordTrace]
  refine ⟨23881350891891098894074231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31841801189188131858765641 23881350891891098894074231)
  ·
    refine ⟨35822026337836648341111347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23881350891891098894074231 35822026337836648341111347)
    ·
      refine ⟨53733039506754972511667021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35822026337836648341111347 53733039506754972511667021)
      ·
        refine ⟨20149889815033114691875133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53733039506754972511667021 20149889815033114691875133)
        ·
          refine ⟨7556208680637418009453175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20149889815033114691875133 7556208680637418009453175)
          ·
            refine ⟨11334313020956127014179763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556208680637418009453175 11334313020956127014179763)
            ·
              refine ⟨17001469531434190521269645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11334313020956127014179763 17001469531434190521269645)
              ·
                refine ⟨6375551074287821445476117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17001469531434190521269645 6375551074287821445476117)
                ·
                  refine ⟨298853956607241630256693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6375551074287821445476117 298853956607241630256693)
                  ·
                    rfl

theorem cell21_1309536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_1309536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309536 prefixEnd_1309536 := by exact prefixLift 1309536
  have htrace : WordTrace (prefixWord ++ tailWord_1309536) baseStart_1309536 baseEnd_1309536 := by
    simpa [prefixWord, tailWord_1309536, baseEnd_1309536] using wordTrace_append hprefix tailTrace_1309536
  have hstable : (prefixWord ++ tailWord_1309536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309536).length < 2 ^ (prefixWord ++ tailWord_1309536).sum := by decide
  have hdescent : baseEnd_1309536 < baseStart_1309536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309539 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 5]
def baseStart_1309539 : Nat := 118140960795 + 1309539 * 2 ^ 59
def prefixEnd_1309539 : Nat := 4983230072969 + 3 ^ 40 * 1309539 * 2
def baseEnd_1309539 : Nat := 298854641248114291706687

theorem tailTrace_1309539 : CollatzResearch.WordTrace tailWord_1309539 prefixEnd_1309539 298854641248114291706687 := by
  unfold tailWord_1309539
  simp only [CollatzResearch.WordTrace]
  refine ⟨47762811202771329300507671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31841874135180886200338447 47762811202771329300507671)
  ·
    refine ⟨71644216804156993950761507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47762811202771329300507671 71644216804156993950761507)
    ·
      refine ⟨107466325206235490926142261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71644216804156993950761507 107466325206235490926142261)
      ·
        refine ⟨10074967988084577274325837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107466325206235490926142261 10074967988084577274325837)
        ·
          refine ⟨3778112995531716477872189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10074967988084577274325837 3778112995531716477872189)
          ·
            refine ⟨1416792373324393679202071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3778112995531716477872189 1416792373324393679202071)
            ·
              refine ⟨2125188559986590518803107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416792373324393679202071 2125188559986590518803107)
              ·
                refine ⟨3187782839979885778204661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125188559986590518803107 3187782839979885778204661)
                ·
                  refine ⟨298854641248114291706687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3187782839979885778204661 298854641248114291706687)
                  ·
                    rfl

theorem cell21_1309539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_1309539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309539 prefixEnd_1309539 := by exact prefixLift 1309539
  have htrace : WordTrace (prefixWord ++ tailWord_1309539) baseStart_1309539 baseEnd_1309539 := by
    simpa [prefixWord, tailWord_1309539, baseEnd_1309539] using wordTrace_append hprefix tailTrace_1309539
  have hstable : (prefixWord ++ tailWord_1309539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309539).length < 2 ^ (prefixWord ++ tailWord_1309539).sum := by decide
  have hdescent : baseEnd_1309539 < baseStart_1309539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309553 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_1309553 : Nat := 118140960795 + 1309553 * 2 ^ 59
def prefixEnd_1309553 : Nat := 4983230072969 + 3 ^ 40 * 1309553 * 2
def baseEnd_1309553 : Nat := 298857836238853378473325

theorem tailTrace_1309553 : CollatzResearch.WordTrace tailWord_1309553 prefixEnd_1309553 298857836238853378473325 := by
  unfold tailWord_1309553
  simp only [CollatzResearch.WordTrace]
  refine ⟨47763321824720609691517313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31842214549813739794344875 47763321824720609691517313)
  ·
    refine ⟨35822491368540457268637985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47763321824720609691517313 35822491368540457268637985)
    ·
      refine ⟨26866868526405342951478489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35822491368540457268637985 26866868526405342951478489)
      ·
        refine ⟨20150151394804007213608867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26866868526405342951478489 20150151394804007213608867)
        ·
          refine ⟨30225227092206010820413301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20150151394804007213608867 30225227092206010820413301)
          ·
            refine ⟨2833615039894313514413747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30225227092206010820413301 2833615039894313514413747)
            ·
              refine ⟨4250422559841470271620621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833615039894313514413747 4250422559841470271620621)
              ·
                refine ⟨1593908459940551351857733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250422559841470271620621 1593908459940551351857733)
                ·
                  refine ⟨298857836238853378473325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1593908459940551351857733 298857836238853378473325)
                  ·
                    rfl

theorem cell21_1309553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_1309553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309553 prefixEnd_1309553 := by exact prefixLift 1309553
  have htrace : WordTrace (prefixWord ++ tailWord_1309553) baseStart_1309553 baseEnd_1309553 := by
    simpa [prefixWord, tailWord_1309553, baseEnd_1309553] using wordTrace_append hprefix tailTrace_1309553
  have hstable : (prefixWord ++ tailWord_1309553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309553).length < 2 ^ (prefixWord ++ tailWord_1309553).sum := by decide
  have hdescent : baseEnd_1309553 < baseStart_1309553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309590 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1309590 : Nat := 118140960795 + 1309590 * 2 ^ 59
def prefixEnd_1309590 : Nat := 4983230072969 + 3 ^ 40 * 1309590 * 2
def baseEnd_1309590 : Nat := 298866280142949536356583

theorem tailTrace_1309590 : CollatzResearch.WordTrace tailWord_1309590 prefixEnd_1309590 298866280142949536356583 := by
  unfold tailWord_1309590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985291957849160313163389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31843114217057710007076149 2985291957849160313163389)
  ·
    refine ⟨1119484484193435117436271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2985291957849160313163389 1119484484193435117436271)
    ·
      refine ⟨1679226726290152676154407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119484484193435117436271 1679226726290152676154407)
      ·
        refine ⟨2518840089435229014231611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679226726290152676154407 2518840089435229014231611)
        ·
          refine ⟨3778260134152843521347417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518840089435229014231611 3778260134152843521347417)
          ·
            refine ⟨2833695100614632641010563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3778260134152843521347417 2833695100614632641010563)
            ·
              refine ⟨4250542650921948961515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833695100614632641010563 4250542650921948961515845)
              ·
                refine ⟨796976747047865430284221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4250542650921948961515845 796976747047865430284221)
                ·
                  refine ⟨298866280142949536356583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796976747047865430284221 298866280142949536356583)
                  ·
                    rfl

theorem cell21_1309590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1309590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309590 prefixEnd_1309590 := by exact prefixLift 1309590
  have htrace : WordTrace (prefixWord ++ tailWord_1309590) baseStart_1309590 baseEnd_1309590 := by
    simpa [prefixWord, tailWord_1309590, baseEnd_1309590] using wordTrace_append hprefix tailTrace_1309590
  have hstable : (prefixWord ++ tailWord_1309590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309590).length < 2 ^ (prefixWord ++ tailWord_1309590).sum := by decide
  have hdescent : baseEnd_1309590 < baseStart_1309590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309638 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1309638 : Nat := 118140960795 + 1309638 * 2 ^ 59
def prefixEnd_1309638 : Nat := 4983230072969 + 3 ^ 40 * 1309638 * 2
def baseEnd_1309638 : Nat := 298877234396912119556485

theorem tailTrace_1309638 : CollatzResearch.WordTrace tailWord_1309638 prefixEnd_1309638 298877234396912119556485 := by
  unfold tailWord_1309638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492700688419145912761299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31844281352941779472241045 1492700688419145912761299)
  ·
    refine ⟨2239051032628718869141949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492700688419145912761299 2239051032628718869141949)
    ·
      refine ⟨839644137235769575928231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2239051032628718869141949 839644137235769575928231)
      ·
        refine ⟨1259466205853654363892347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839644137235769575928231 1259466205853654363892347)
        ·
          refine ⟨1889199308780481545838521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259466205853654363892347 1889199308780481545838521)
          ·
            refine ⟨1416899481585361159378891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1889199308780481545838521 1416899481585361159378891)
            ·
              refine ⟨2125349222378041739068337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416899481585361159378891 2125349222378041739068337)
              ·
                refine ⟨1594011916783531304301253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125349222378041739068337 1594011916783531304301253)
                ·
                  refine ⟨298877234396912119556485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594011916783531304301253 298877234396912119556485)
                  ·
                    rfl

theorem cell21_1309638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1309638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309638 prefixEnd_1309638 := by exact prefixLift 1309638
  have htrace : WordTrace (prefixWord ++ tailWord_1309638) baseStart_1309638 baseEnd_1309638 := by
    simpa [prefixWord, tailWord_1309638, baseEnd_1309638] using wordTrace_append hprefix tailTrace_1309638
  have hstable : (prefixWord ++ tailWord_1309638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309638).length < 2 ^ (prefixWord ++ tailWord_1309638).sum := by decide
  have hdescent : baseEnd_1309638 < baseStart_1309638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309646 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_1309646 : Nat := 118140960795 + 1309646 * 2 ^ 59
def prefixEnd_1309646 : Nat := 4983230072969 + 3 ^ 40 * 1309646 * 2
def baseEnd_1309646 : Nat := 298879060105905883423135

theorem tailTrace_1309646 : CollatzResearch.WordTrace tailWord_1309646 prefixEnd_1309646 298879060105905883423135 := by
  unfold tailWord_1309646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970839226672960821831599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31844475875589124383101861 5970839226672960821831599)
  ·
    refine ⟨8956258840009441232747399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5970839226672960821831599 8956258840009441232747399)
    ·
      refine ⟨13434388260014161849121099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8956258840009441232747399 13434388260014161849121099)
      ·
        refine ⟨20151582390021242773681649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13434388260014161849121099 20151582390021242773681649)
        ·
          refine ⟨15113686792515932080261237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20151582390021242773681649 15113686792515932080261237)
          ·
            refine ⟨1416908136798368632524491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15113686792515932080261237 1416908136798368632524491)
            ·
              refine ⟨2125362205197552948786737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416908136798368632524491 2125362205197552948786737)
              ·
                refine ⟨1594021653898164711590053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125362205197552948786737 1594021653898164711590053)
                ·
                  refine ⟨298879060105905883423135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594021653898164711590053 298879060105905883423135)
                  ·
                    rfl

theorem cell21_1309646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_1309646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309646 prefixEnd_1309646 := by exact prefixLift 1309646
  have htrace : WordTrace (prefixWord ++ tailWord_1309646) baseStart_1309646 baseEnd_1309646 := by
    simpa [prefixWord, tailWord_1309646, baseEnd_1309646] using wordTrace_append hprefix tailTrace_1309646
  have hstable : (prefixWord ++ tailWord_1309646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309646).length < 2 ^ (prefixWord ++ tailWord_1309646).sum := by decide
  have hdescent : baseEnd_1309646 < baseStart_1309646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309674 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1309674 : Nat := 118140960795 + 1309674 * 2 ^ 59
def prefixEnd_1309674 : Nat := 4983230072969 + 3 ^ 40 * 1309674 * 2
def baseEnd_1309674 : Nat := 298885450087384056956411

theorem tailTrace_1309674 : CollatzResearch.WordTrace tailWord_1309674 prefixEnd_1309674 298885450087384056956411 := by
  unfold tailWord_1309674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941933764320561839168019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31845156704854831571114717 11941933764320561839168019)
  ·
    refine ⟨17912900646480842758752029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11941933764320561839168019 17912900646480842758752029)
    ·
      refine ⟨6717337742430316034532011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17912900646480842758752029 6717337742430316034532011)
      ·
        refine ⟨10076006613645474051798017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6717337742430316034532011 10076006613645474051798017)
        ·
          refine ⟨7557004960234105538848513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10076006613645474051798017 7557004960234105538848513)
          ·
            refine ⟨5667753720175579154136385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7557004960234105538848513 5667753720175579154136385)
            ·
              refine ⟨4250815290131684365602289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5667753720175579154136385 4250815290131684365602289)
              ·
                refine ⟨3188111467598763274201717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4250815290131684365602289 3188111467598763274201717)
                ·
                  refine ⟨298885450087384056956411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188111467598763274201717 298885450087384056956411)
                  ·
                    rfl

theorem cell21_1309674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1309674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309674 prefixEnd_1309674 := by exact prefixLift 1309674
  have htrace : WordTrace (prefixWord ++ tailWord_1309674) baseStart_1309674 baseEnd_1309674 := by
    simpa [prefixWord, tailWord_1309674, baseEnd_1309674] using wordTrace_append hprefix tailTrace_1309674
  have hstable : (prefixWord ++ tailWord_1309674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309674).length < 2 ^ (prefixWord ++ tailWord_1309674).sum := by decide
  have hdescent : baseEnd_1309674 < baseStart_1309674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309708 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1309708 : Nat := 118140960795 + 1309708 * 2 ^ 59
def prefixEnd_1309708 : Nat := 4983230072969 + 3 ^ 40 * 1309708 * 2
def baseEnd_1309708 : Nat := 298893209350607553389675

theorem tailTrace_1309708 : CollatzResearch.WordTrace tailWord_1309708 prefixEnd_1309708 298893209350607553389675 := by
  unfold tailWord_1309708
  simp only [CollatzResearch.WordTrace]
  refine ⟨23884487569579535581704889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31845983426106047442273185 23884487569579535581704889)
  ·
    refine ⟨17913365677184651686278667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23884487569579535581704889 17913365677184651686278667)
    ·
      refine ⟨26870048515776977529418001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17913365677184651686278667 26870048515776977529418001)
      ·
        refine ⟨20152536386832733147063501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26870048515776977529418001 20152536386832733147063501)
        ·
          refine ⟨7557201145062274930148813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20152536386832733147063501 7557201145062274930148813)
          ·
            refine ⟨2833950429398353098805805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7557201145062274930148813 2833950429398353098805805)
            ·
              refine ⟨1062731411024382412052177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2833950429398353098805805 1062731411024382412052177)
              ·
                refine ⟨797048558268286809039133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062731411024382412052177 797048558268286809039133)
                ·
                  refine ⟨298893209350607553389675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797048558268286809039133 298893209350607553389675)
                  ·
                    rfl

theorem cell21_1309708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1309708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309708 prefixEnd_1309708 := by exact prefixLift 1309708
  have htrace : WordTrace (prefixWord ++ tailWord_1309708) baseStart_1309708 baseEnd_1309708 := by
    simpa [prefixWord, tailWord_1309708, baseEnd_1309708] using wordTrace_append hprefix tailTrace_1309708
  have hstable : (prefixWord ++ tailWord_1309708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309708).length < 2 ^ (prefixWord ++ tailWord_1309708).sum := by decide
  have hdescent : baseEnd_1309708 < baseStart_1309708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309714 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_1309714 : Nat := 118140960795 + 1309714 * 2 ^ 59
def prefixEnd_1309714 : Nat := 4983230072969 + 3 ^ 40 * 1309714 * 2
def baseEnd_1309714 : Nat := 298894578632352876289663

theorem tailTrace_1309714 : CollatzResearch.WordTrace tailWord_1309714 prefixEnd_1309714 298894578632352876289663 := by
  unfold tailWord_1309714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942298494284333547032049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31846129318091556125418797 11942298494284333547032049)
  ·
    refine ⟨8956723870713250160274037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11942298494284333547032049 8956723870713250160274037)
    ·
      refine ⟨839692862879367202525691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8956723870713250160274037 839692862879367202525691)
      ·
        refine ⟨1259539294319050803788537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839692862879367202525691 1259539294319050803788537)
        ·
          refine ⟨944654470739288102841403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259539294319050803788537 944654470739288102841403)
          ·
            refine ⟨1416981706108932154262105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944654470739288102841403 1416981706108932154262105)
            ·
              refine ⟨1062736279581699115696579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416981706108932154262105 1062736279581699115696579)
              ·
                refine ⟨1594104419372548673544869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062736279581699115696579 1594104419372548673544869)
                ·
                  refine ⟨298894578632352876289663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594104419372548673544869 298894578632352876289663)
                  ·
                    rfl

theorem cell21_1309714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_1309714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309714 prefixEnd_1309714 := by exact prefixLift 1309714
  have htrace : WordTrace (prefixWord ++ tailWord_1309714) baseStart_1309714 baseEnd_1309714 := by
    simpa [prefixWord, tailWord_1309714, baseEnd_1309714] using wordTrace_append hprefix tailTrace_1309714
  have hstable : (prefixWord ++ tailWord_1309714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309714).length < 2 ^ (prefixWord ++ tailWord_1309714).sum := by decide
  have hdescent : baseEnd_1309714 < baseStart_1309714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309719 : List Nat := [1, 1, 3, 5, 1, 1, 1, 8]
def baseStart_1309719 : Nat := 118140960795 + 1309719 * 2 ^ 59
def prefixEnd_1309719 : Nat := 4983230072969 + 3 ^ 40 * 1309719 * 2
def baseEnd_1309719 : Nat := 99631906566824659568773

theorem tailTrace_1309719 : CollatzResearch.WordTrace tailWord_1309719 prefixEnd_1309719 99631906566824659568773 := by
  unfold tailWord_1309719
  simp only [CollatzResearch.WordTrace]
  refine ⟨47769376342119220042060211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31846250894746146694706807 47769376342119220042060211)
  ·
    refine ⟨71654064513178830063090317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47769376342119220042060211 71654064513178830063090317)
    ·
      refine ⟨26870274192442061273658869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71654064513178830063090317 26870274192442061273658869)
      ·
        refine ⟨2519088205541443244405519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26870274192442061273658869 2519088205541443244405519)
        ·
          refine ⟨3778632308312164866608279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519088205541443244405519 3778632308312164866608279)
          ·
            refine ⟨5667948462468247299912419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778632308312164866608279 5667948462468247299912419)
            ·
              refine ⟨8501922693702370949868629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667948462468247299912419 8501922693702370949868629)
              ·
                refine ⟨99631906566824659568773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8501922693702370949868629 99631906566824659568773)
                ·
                  rfl

theorem cell21_1309719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_1309719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309719 prefixEnd_1309719 := by exact prefixLift 1309719
  have htrace : WordTrace (prefixWord ++ tailWord_1309719) baseStart_1309719 baseEnd_1309719 := by
    simpa [prefixWord, tailWord_1309719, baseEnd_1309719] using wordTrace_append hprefix tailTrace_1309719
  have hstable : (prefixWord ++ tailWord_1309719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309719).length < 2 ^ (prefixWord ++ tailWord_1309719).sum := by decide
  have hdescent : baseEnd_1309719 < baseStart_1309719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309733 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_1309733 : Nat := 118140960795 + 1309733 * 2 ^ 59
def prefixEnd_1309733 : Nat := 4983230072969 + 3 ^ 40 * 1309733 * 2
def baseEnd_1309733 : Nat := 298898914691213065472957

theorem tailTrace_1309733 : CollatzResearch.WordTrace tailWord_1309733 prefixEnd_1309733 298898914691213065472957 := by
  unfold tailWord_1309733
  simp only [CollatzResearch.WordTrace]
  refine ⟨47769886964068500433069853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31846591309379000288713235 47769886964068500433069853)
  ·
    refine ⟨17913707611525687662401195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47769886964068500433069853 17913707611525687662401195)
    ·
      refine ⟨26870561417288531493601793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17913707611525687662401195 26870561417288531493601793)
      ·
        refine ⟨20152921062966398620201345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26870561417288531493601793 20152921062966398620201345)
        ·
          refine ⟨15114690797224798965151009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20152921062966398620201345 15114690797224798965151009)
          ·
            refine ⟨11336018097918599223863257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15114690797224798965151009 11336018097918599223863257)
            ·
              refine ⟨8502013573438949417897443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11336018097918599223863257 8502013573438949417897443)
              ·
                refine ⟨12753020360158424126846165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8502013573438949417897443 12753020360158424126846165)
                ·
                  refine ⟨298898914691213065472957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12753020360158424126846165 298898914691213065472957)
                  ·
                    rfl

theorem cell21_1309733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_1309733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309733 prefixEnd_1309733 := by exact prefixLift 1309733
  have htrace : WordTrace (prefixWord ++ tailWord_1309733) baseStart_1309733 baseEnd_1309733 := by
    simpa [prefixWord, tailWord_1309733, baseEnd_1309733] using wordTrace_append hprefix tailTrace_1309733
  have hstable : (prefixWord ++ tailWord_1309733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309733).length < 2 ^ (prefixWord ++ tailWord_1309733).sum := by decide
  have hdescent : baseEnd_1309733 < baseStart_1309733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309767 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 3]
def baseStart_1309767 : Nat := 118140960795 + 1309767 * 2 ^ 59
def prefixEnd_1309767 : Nat := 4983230072969 + 3 ^ 40 * 1309767 * 2
def baseEnd_1309767 : Nat := 298906673954436561906221

theorem tailTrace_1309767 : CollatzResearch.WordTrace tailWord_1309767 prefixEnd_1309767 298906673954436561906221 := by
  unfold tailWord_1309767
  simp only [CollatzResearch.WordTrace]
  refine ⟨47771127045945324239807555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31847418030630216159871703 47771127045945324239807555)
  ·
    refine ⟨71656690568917986359711333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47771127045945324239807555 71656690568917986359711333)
    ·
      refine ⟨13435629481672122442445875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71656690568917986359711333 13435629481672122442445875)
      ·
        refine ⟨20153444222508183663668813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13435629481672122442445875 20153444222508183663668813)
        ·
          refine ⟨7557541583440568873875805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20153444222508183663668813 7557541583440568873875805)
          ·
            refine ⟨2834078093790213327703427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7557541583440568873875805 2834078093790213327703427)
            ·
              refine ⟨4251117140685319991555141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834078093790213327703427 4251117140685319991555141)
              ·
                refine ⟨797084463878497498416589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4251117140685319991555141 797084463878497498416589)
                ·
                  refine ⟨298906673954436561906221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797084463878497498416589 298906673954436561906221)
                  ·
                    rfl

theorem cell21_1309767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3].length) (baseStart_1309767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309767 prefixEnd_1309767 := by exact prefixLift 1309767
  have htrace : WordTrace (prefixWord ++ tailWord_1309767) baseStart_1309767 baseEnd_1309767 := by
    simpa [prefixWord, tailWord_1309767, baseEnd_1309767] using wordTrace_append hprefix tailTrace_1309767
  have hstable : (prefixWord ++ tailWord_1309767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309767).length < 2 ^ (prefixWord ++ tailWord_1309767).sum := by decide
  have hdescent : baseEnd_1309767 < baseStart_1309767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309860 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1309860 : Nat := 118140960795 + 1309860 * 2 ^ 59
def prefixEnd_1309860 : Nat := 4983230072969 + 3 ^ 40 * 1309860 * 2
def baseEnd_1309860 : Nat := 298927897821489066856031

theorem tailTrace_1309860 : CollatzResearch.WordTrace tailWord_1309860 prefixEnd_1309860 298927897821489066856031 := by
  unfold tailWord_1309860
  simp only [CollatzResearch.WordTrace]
  refine ⟨23887259517304200561471517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31849679356405600748628689 23887259517304200561471517)
  ·
    refine ⟨8957722318989075210551819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23887259517304200561471517 8957722318989075210551819)
    ·
      refine ⟨13436583478483612815827729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8957722318989075210551819 13436583478483612815827729)
      ·
        refine ⟨10077437608862709611870797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13436583478483612815827729 10077437608862709611870797)
        ·
          refine ⟨3779039103323516104451549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10077437608862709611870797 3779039103323516104451549)
          ·
            refine ⟨1417139663746318539169331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3779039103323516104451549 1417139663746318539169331)
            ·
              refine ⟨2125709495619477808753997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417139663746318539169331 2125709495619477808753997)
              ·
                refine ⟨797141060857304178282749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2125709495619477808753997 797141060857304178282749)
                ·
                  refine ⟨298927897821489066856031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797141060857304178282749 298927897821489066856031)
                  ·
                    rfl

theorem cell21_1309860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1309860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309860 prefixEnd_1309860 := by exact prefixLift 1309860
  have htrace : WordTrace (prefixWord ++ tailWord_1309860) baseStart_1309860 baseEnd_1309860 := by
    simpa [prefixWord, tailWord_1309860, baseEnd_1309860] using wordTrace_append hprefix tailTrace_1309860
  have hstable : (prefixWord ++ tailWord_1309860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309860).length < 2 ^ (prefixWord ++ tailWord_1309860).sum := by decide
  have hdescent : baseEnd_1309860 < baseStart_1309860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309899 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_1309899 : Nat := 118140960795 + 1309899 * 2 ^ 59
def prefixEnd_1309899 : Nat := 4983230072969 + 3 ^ 40 * 1309899 * 2
def baseEnd_1309899 : Nat := 298936798152833665705951

theorem tailTrace_1309899 : CollatzResearch.WordTrace tailWord_1309899 prefixEnd_1309899 298936798152833665705951 := by
  unfold tailWord_1309899
  simp only [CollatzResearch.WordTrace]
  refine ⟨47775941481467110783612751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31850627654311407189075167 47775941481467110783612751)
  ·
    refine ⟨71663912222200666175419127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47775941481467110783612751 71663912222200666175419127)
    ·
      refine ⟨107495868333300999263128691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71663912222200666175419127 107495868333300999263128691)
      ·
        refine ⟨161243802499951498894693037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107495868333300999263128691 161243802499951498894693037)
        ·
          refine ⟨60466425937481812085509889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161243802499951498894693037 60466425937481812085509889)
          ·
            refine ⟨45349819453111359064132417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60466425937481812085509889 45349819453111359064132417)
            ·
              refine ⟨34012364589833519298099313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45349819453111359064132417 34012364589833519298099313)
              ·
                refine ⟨25509273442375139473574485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34012364589833519298099313 25509273442375139473574485)
                ·
                  refine ⟨298936798152833665705951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25509273442375139473574485 298936798152833665705951)
                  ·
                    rfl

theorem cell21_1309899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_1309899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309899 prefixEnd_1309899 := by exact prefixLift 1309899
  have htrace : WordTrace (prefixWord ++ tailWord_1309899) baseStart_1309899 baseEnd_1309899 := by
    simpa [prefixWord, tailWord_1309899, baseEnd_1309899] using wordTrace_append hprefix tailTrace_1309899
  have hstable : (prefixWord ++ tailWord_1309899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309899).length < 2 ^ (prefixWord ++ tailWord_1309899).sum := by decide
  have hdescent : baseEnd_1309899 < baseStart_1309899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309930 : List Nat := [3, 1, 3, 1, 1, 12]
def baseStart_1309930 : Nat := 118140960795 + 1309930 * 2 ^ 59
def prefixEnd_1309930 : Nat := 4983230072969 + 3 ^ 40 * 1309930 * 2
def baseEnd_1309930 : Nat := 11071995287969796321823

theorem tailTrace_1309930 : CollatzResearch.WordTrace tailWord_1309930 prefixEnd_1309930 11071995287969796321823 := by
  unfold tailWord_1309930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944268036088700769497811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31851381429569868718660829 11944268036088700769497811)
  ·
    refine ⟨17916402054133051154246717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11944268036088700769497811 17916402054133051154246717)
    ·
      refine ⟨6718650770299894182842519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17916402054133051154246717 6718650770299894182842519)
      ·
        refine ⟨10077976155449841274263779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6718650770299894182842519 10077976155449841274263779)
        ·
          refine ⟨15116964233174761911395669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10077976155449841274263779 15116964233174761911395669)
          ·
            refine ⟨11071995287969796321823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15116964233174761911395669 11071995287969796321823)
            ·
              rfl

theorem cell21_1309930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 12].length) (baseStart_1309930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309930 prefixEnd_1309930 := by exact prefixLift 1309930
  have htrace : WordTrace (prefixWord ++ tailWord_1309930) baseStart_1309930 baseEnd_1309930 := by
    simpa [prefixWord, tailWord_1309930, baseEnd_1309930] using wordTrace_append hprefix tailTrace_1309930
  have hstable : (prefixWord ++ tailWord_1309930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309930).length < 2 ^ (prefixWord ++ tailWord_1309930).sum := by decide
  have hdescent : baseEnd_1309930 < baseStart_1309930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309933 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1309933 : Nat := 118140960795 + 1309933 * 2 ^ 59
def prefixEnd_1309933 : Nat := 4983230072969 + 3 ^ 40 * 1309933 * 2
def baseEnd_1309933 : Nat := 298944557416057162139215

theorem tailTrace_1309933 : CollatzResearch.WordTrace tailWord_1309933 prefixEnd_1309933 298944557416057162139215 := by
  unfold tailWord_1309933
  simp only [CollatzResearch.WordTrace]
  refine ⟨47777181563343934590350453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31851454375562623060233635 47777181563343934590350453)
  ·
    refine ⟨4479110771563493867845355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47777181563343934590350453 4479110771563493867845355)
    ·
      refine ⟨6718666157345240801768033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4479110771563493867845355 6718666157345240801768033)
      ·
        refine ⟨5038999618008930601326025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6718666157345240801768033 5038999618008930601326025)
        ·
          refine ⟨3779249713506697950994519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5038999618008930601326025 3779249713506697950994519)
          ·
            refine ⟨5668874570260046926491779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779249713506697950994519 5668874570260046926491779)
            ·
              refine ⟨8503311855390070389737669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668874570260046926491779 8503311855390070389737669)
              ·
                refine ⟨1594370972885638198075813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8503311855390070389737669 1594370972885638198075813)
                ·
                  refine ⟨298944557416057162139215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594370972885638198075813 298944557416057162139215)
                  ·
                    rfl

theorem cell21_1309933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1309933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309933 prefixEnd_1309933 := by exact prefixLift 1309933
  have htrace : WordTrace (prefixWord ++ tailWord_1309933) baseStart_1309933 baseEnd_1309933 := by
    simpa [prefixWord, tailWord_1309933, baseEnd_1309933] using wordTrace_append hprefix tailTrace_1309933
  have hstable : (prefixWord ++ tailWord_1309933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309933).length < 2 ^ (prefixWord ++ tailWord_1309933).sum := by decide
  have hdescent : baseEnd_1309933 < baseStart_1309933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309961 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_1309961 : Nat := 118140960795 + 1309961 * 2 ^ 59
def prefixEnd_1309961 : Nat := 4983230072969 + 3 ^ 40 * 1309961 * 2
def baseEnd_1309961 : Nat := 298950947397535335672491

theorem tailTrace_1309961 : CollatzResearch.WordTrace tailWord_1309961 prefixEnd_1309961 298950947397535335672491 := by
  unfold tailWord_1309961
  simp only [CollatzResearch.WordTrace]
  refine ⟨47778202807242495372369737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31852135204828330248246491 47778202807242495372369737)
  ·
    refine ⟨35833652105431871529277303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47778202807242495372369737 35833652105431871529277303)
    ·
      refine ⟨53750478158147807293915955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35833652105431871529277303 53750478158147807293915955)
      ·
        refine ⟨80625717237221710940873933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53750478158147807293915955 80625717237221710940873933)
        ·
          refine ⟨30234643963958141602827725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80625717237221710940873933 30234643963958141602827725)
          ·
            refine ⟨11337991486484303101060397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30234643963958141602827725 11337991486484303101060397)
            ·
              refine ⟨4251746807431613662897649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11337991486484303101060397 4251746807431613662897649)
              ·
                refine ⟨3188810105573710247173237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4251746807431613662897649 3188810105573710247173237)
                ·
                  refine ⟨298950947397535335672491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188810105573710247173237 298950947397535335672491)
                  ·
                    rfl

theorem cell21_1309961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_1309961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1309961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1309961 prefixEnd_1309961 := by exact prefixLift 1309961
  have htrace : WordTrace (prefixWord ++ tailWord_1309961) baseStart_1309961 baseEnd_1309961 := by
    simpa [prefixWord, tailWord_1309961, baseEnd_1309961] using wordTrace_append hprefix tailTrace_1309961
  have hstable : (prefixWord ++ tailWord_1309961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309961).length < 2 ^ (prefixWord ++ tailWord_1309961).sum := by decide
  have hdescent : baseEnd_1309961 < baseStart_1309961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310023 : List Nat := [1, 1, 4, 1, 2, 3, 4, 5]
def baseStart_1310023 : Nat := 118140960795 + 1310023 * 2 ^ 59
def prefixEnd_1310023 : Nat := 4983230072969 + 3 ^ 40 * 1310023 * 2
def baseEnd_1310023 : Nat := 99655032214079001879677

theorem tailTrace_1310023 : CollatzResearch.WordTrace tailWord_1310023 prefixEnd_1310023 99655032214079001879677 := by
  unfold tailWord_1310023
  simp only [CollatzResearch.WordTrace]
  refine ⟨47780464133017879961126723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31853642755345253307417815 47780464133017879961126723)
  ·
    refine ⟨71670696199526819941690085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47780464133017879961126723 71670696199526819941690085)
    ·
      refine ⟨13438255537411278739066891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71670696199526819941690085 13438255537411278739066891)
      ·
        refine ⟨20157383306116918108600337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438255537411278739066891 20157383306116918108600337)
        ·
          refine ⟨15118037479587688581450253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20157383306116918108600337 15118037479587688581450253)
          ·
            refine ⟨5669264054845383218043845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15118037479587688581450253 5669264054845383218043845)
            ·
              refine ⟨1062987010283509353383221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5669264054845383218043845 1062987010283509353383221)
              ·
                refine ⟨99655032214079001879677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1062987010283509353383221 99655032214079001879677)
                ·
                  rfl

theorem cell21_1310023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 5].length) (baseStart_1310023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310023 prefixEnd_1310023 := by exact prefixLift 1310023
  have htrace : WordTrace (prefixWord ++ tailWord_1310023) baseStart_1310023 baseEnd_1310023 := by
    simpa [prefixWord, tailWord_1310023, baseEnd_1310023] using wordTrace_append hprefix tailTrace_1310023
  have hstable : (prefixWord ++ tailWord_1310023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310023).length < 2 ^ (prefixWord ++ tailWord_1310023).sum := by decide
  have hdescent : baseEnd_1310023 < baseStart_1310023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310282 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_1310282 : Nat := 118140960795 + 1310282 * 2 ^ 59
def prefixEnd_1310282 : Nat := 4983230072969 + 3 ^ 40 * 1310282 * 2
def baseEnd_1310282 : Nat := 299024203970910110821835

theorem tailTrace_1310282 : CollatzResearch.WordTrace tailWord_1310282 prefixEnd_1310282 299024203970910110821835 := by
  unfold tailWord_1310282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11947477659769891798701275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31859940426053044796536733 11947477659769891798701275)
  ·
    refine ⟨17921216489654837698051913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11947477659769891798701275 17921216489654837698051913)
    ·
      refine ⟨13440912367241128273538935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17921216489654837698051913 13440912367241128273538935)
      ·
        refine ⟨20161368550861692410308403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13440912367241128273538935 20161368550861692410308403)
        ·
          refine ⟨30242052826292538615462605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20161368550861692410308403 30242052826292538615462605)
          ·
            refine ⟨11340769809859701980798477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30242052826292538615462605 11340769809859701980798477)
            ·
              refine ⟨4252788678697388242799429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11340769809859701980798477 4252788678697388242799429)
              ·
                refine ⟨797397877255760295524893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4252788678697388242799429 797397877255760295524893)
                ·
                  refine ⟨299024203970910110821835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797397877255760295524893 299024203970910110821835)
                  ·
                    rfl

theorem cell21_1310282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_1310282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310282 prefixEnd_1310282 := by exact prefixLift 1310282
  have htrace : WordTrace (prefixWord ++ tailWord_1310282) baseStart_1310282 baseEnd_1310282 := by
    simpa [prefixWord, tailWord_1310282, baseEnd_1310282] using wordTrace_append hprefix tailTrace_1310282
  have hstable : (prefixWord ++ tailWord_1310282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310282).length < 2 ^ (prefixWord ++ tailWord_1310282).sum := by decide
  have hdescent : baseEnd_1310282 < baseStart_1310282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310285 : List Nat := [1, 6, 1, 1, 4, 1, 1, 6]
def baseStart_1310285 : Nat := 118140960795 + 1310285 * 2 ^ 59
def prefixEnd_1310285 : Nat := 4983230072969 + 3 ^ 40 * 1310285 * 2
def baseEnd_1310285 : Nat := 99674962870594257423943

theorem tailTrace_1310285 : CollatzResearch.WordTrace tailWord_1310285 prefixEnd_1310285 99674962870594257423943 := by
  unfold tailWord_1310285
  simp only [CollatzResearch.WordTrace]
  refine ⟨47790020058068698707164309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31860013372045799138109539 47790020058068698707164309)
  ·
    refine ⟨2240157190221970251898327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47790020058068698707164309 2240157190221970251898327)
    ·
      refine ⟨3360235785332955377847491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240157190221970251898327 3360235785332955377847491)
      ·
        refine ⟨5040353677999433066771237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360235785332955377847491 5040353677999433066771237)
        ·
          refine ⟨945066314624893700019607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5040353677999433066771237 945066314624893700019607)
          ·
            refine ⟨1417599471937340550029411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945066314624893700019607 1417599471937340550029411)
            ·
              refine ⟨2126399207906010825044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417599471937340550029411 2126399207906010825044117)
              ·
                refine ⟨99674962870594257423943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2126399207906010825044117 99674962870594257423943)
                ·
                  rfl

theorem cell21_1310285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 6].length) (baseStart_1310285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310285 prefixEnd_1310285 := by exact prefixLift 1310285
  have htrace : WordTrace (prefixWord ++ tailWord_1310285) baseStart_1310285 baseEnd_1310285 := by
    simpa [prefixWord, tailWord_1310285, baseEnd_1310285] using wordTrace_append hprefix tailTrace_1310285
  have hstable : (prefixWord ++ tailWord_1310285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310285).length < 2 ^ (prefixWord ++ tailWord_1310285).sum := by decide
  have hdescent : baseEnd_1310285 < baseStart_1310285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310341 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1310341 : Nat := 118140960795 + 1310341 * 2 ^ 59
def prefixEnd_1310341 : Nat := 4983230072969 + 3 ^ 40 * 1310341 * 2
def baseEnd_1310341 : Nat := 299037668574739119338381

theorem tailTrace_1310341 : CollatzResearch.WordTrace tailWord_1310341 prefixEnd_1310341 299037668574739119338381 := by
  unfold tailWord_1310341
  simp only [CollatzResearch.WordTrace]
  refine ⟨47792062545865820271202877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31861375030577213514135251 47792062545865820271202877)
  ·
    refine ⟨17922023454699682601701079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47792062545865820271202877 17922023454699682601701079)
    ·
      refine ⟨26883035182049523902551619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17922023454699682601701079 26883035182049523902551619)
      ·
        refine ⟨40324552773074285853827429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26883035182049523902551619 40324552773074285853827429)
        ·
          refine ⟨7560853644951428597592643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40324552773074285853827429 7560853644951428597592643)
          ·
            refine ⟨11341280467427142896388965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560853644951428597592643 11341280467427142896388965)
            ·
              refine ⟨2126490087642589293072931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11341280467427142896388965 2126490087642589293072931)
              ·
                refine ⟨3189735131463883939609397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126490087642589293072931 3189735131463883939609397)
                ·
                  refine ⟨299037668574739119338381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3189735131463883939609397 299037668574739119338381)
                  ·
                    rfl

theorem cell21_1310341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1310341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310341 prefixEnd_1310341 := by exact prefixLift 1310341
  have htrace : WordTrace (prefixWord ++ tailWord_1310341) baseStart_1310341 baseEnd_1310341 := by
    simpa [prefixWord, tailWord_1310341, baseEnd_1310341] using wordTrace_append hprefix tailTrace_1310341
  have hstable : (prefixWord ++ tailWord_1310341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310341).length < 2 ^ (prefixWord ++ tailWord_1310341).sum := by decide
  have hdescent : baseEnd_1310341 < baseStart_1310341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310476 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1310476 : Nat := 118140960795 + 1310476 * 2 ^ 59
def prefixEnd_1310476 : Nat := 4983230072969 + 3 ^ 40 * 1310476 * 2
def baseEnd_1310476 : Nat := 299068477414008884588105

theorem tailTrace_1310476 : CollatzResearch.WordTrace tailWord_1310476 prefixEnd_1310476 299068477414008884588105 := by
  unfold tailWord_1310476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23898493200188369163683641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31864657600251158884911521 23898493200188369163683641)
  ·
    refine ⟨17923869900141276872762731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23898493200188369163683641 17923869900141276872762731)
    ·
      refine ⟨26885804850211915309144097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17923869900141276872762731 26885804850211915309144097)
      ·
        refine ⟨20164353637658936481858073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26885804850211915309144097 20164353637658936481858073)
        ·
          refine ⟨15123265228244202361393555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20164353637658936481858073 15123265228244202361393555)
          ·
            refine ⟨22684897842366303542090333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15123265228244202361393555 22684897842366303542090333)
            ·
              refine ⟨8506836690887363828283875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22684897842366303542090333 8506836690887363828283875)
              ·
                refine ⟨12760255036331045742425813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506836690887363828283875 12760255036331045742425813)
                ·
                  refine ⟨299068477414008884588105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12760255036331045742425813 299068477414008884588105)
                  ·
                    rfl

theorem cell21_1310476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1310476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310476 prefixEnd_1310476 := by exact prefixLift 1310476
  have htrace : WordTrace (prefixWord ++ tailWord_1310476) baseStart_1310476 baseEnd_1310476 := by
    simpa [prefixWord, tailWord_1310476, baseEnd_1310476] using wordTrace_append hprefix tailTrace_1310476
  have hstable : (prefixWord ++ tailWord_1310476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310476).length < 2 ^ (prefixWord ++ tailWord_1310476).sum := by decide
  have hdescent : baseEnd_1310476 < baseStart_1310476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310569 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 3]
def baseStart_1310569 : Nat := 118140960795 + 1310569 * 2 ^ 59
def prefixEnd_1310569 : Nat := 4983230072969 + 3 ^ 40 * 1310569 * 2
def baseEnd_1310569 : Nat := 299089701281061389537915

theorem tailTrace_1310569 : CollatzResearch.WordTrace tailWord_1310569 prefixEnd_1310569 299089701281061389537915 := by
  unfold tailWord_1310569
  simp only [CollatzResearch.WordTrace]
  refine ⟨47800378389039815210502761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31866918926026543473668507 47800378389039815210502761)
  ·
    refine ⟨35850283791779861407877071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47800378389039815210502761 35850283791779861407877071)
    ·
      refine ⟨53775425687669792111815607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35850283791779861407877071 53775425687669792111815607)
      ·
        refine ⟨80663138531504688167723411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53775425687669792111815607 80663138531504688167723411)
        ·
          refine ⟨120994707797257032251585117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80663138531504688167723411 120994707797257032251585117)
          ·
            refine ⟨45373015423971387094344419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120994707797257032251585117 45373015423971387094344419)
            ·
              refine ⟨68059523135957080641516629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45373015423971387094344419 68059523135957080641516629)
              ·
                refine ⟨797572536749497038767773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 68059523135957080641516629 797572536749497038767773)
                ·
                  refine ⟨299089701281061389537915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797572536749497038767773 299089701281061389537915)
                  ·
                    rfl

theorem cell21_1310569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_1310569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310569 prefixEnd_1310569 := by exact prefixLift 1310569
  have htrace : WordTrace (prefixWord ++ tailWord_1310569) baseStart_1310569 baseEnd_1310569 := by
    simpa [prefixWord, tailWord_1310569, baseEnd_1310569] using wordTrace_append hprefix tailTrace_1310569
  have hstable : (prefixWord ++ tailWord_1310569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310569).length < 2 ^ (prefixWord ++ tailWord_1310569).sum := by decide
  have hdescent : baseEnd_1310569 < baseStart_1310569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310597 : List Nat := [1, 3, 1, 1, 3, 2, 1, 9]
def baseStart_1310597 : Nat := 118140960795 + 1310597 * 2 ^ 59
def prefixEnd_1310597 : Nat := 4983230072969 + 3 ^ 40 * 1310597 * 2
def baseEnd_1310597 : Nat := 99698697087513187690397

theorem tailTrace_1310597 : CollatzResearch.WordTrace tailWord_1310597 prefixEnd_1310597 99698697087513187690397 := by
  unfold tailWord_1310597
  simp only [CollatzResearch.WordTrace]
  refine ⟨47801399632938375992522045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31867599755292250661681363 47801399632938375992522045)
  ·
    refine ⟨17925524862351890997195767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47801399632938375992522045 17925524862351890997195767)
    ·
      refine ⟨26888287293527836495793651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17925524862351890997195767 26888287293527836495793651)
      ·
        refine ⟨40332430940291754743690477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26888287293527836495793651 40332430940291754743690477)
        ·
          refine ⟨15124661602609408028883929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40332430940291754743690477 15124661602609408028883929)
          ·
            refine ⟨11343496201957056021662947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15124661602609408028883929 11343496201957056021662947)
            ·
              refine ⟨17015244302935584032494421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11343496201957056021662947 17015244302935584032494421)
              ·
                refine ⟨99698697087513187690397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17015244302935584032494421 99698697087513187690397)
                ·
                  rfl

theorem cell21_1310597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_1310597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310597 prefixEnd_1310597 := by exact prefixLift 1310597
  have htrace : WordTrace (prefixWord ++ tailWord_1310597) baseStart_1310597 baseEnd_1310597 := by
    simpa [prefixWord, tailWord_1310597, baseEnd_1310597] using wordTrace_append hprefix tailTrace_1310597
  have hstable : (prefixWord ++ tailWord_1310597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310597).length < 2 ^ (prefixWord ++ tailWord_1310597).sum := by decide
  have hdescent : baseEnd_1310597 < baseStart_1310597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310620 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1310620 : Nat := 118140960795 + 1310620 * 2 ^ 59
def prefixEnd_1310620 : Nat := 4983230072969 + 3 ^ 40 * 1310620 * 2
def baseEnd_1310620 : Nat := 299101340175896634187811

theorem tailTrace_1310620 : CollatzResearch.WordTrace tailWord_1310620 prefixEnd_1310620 299101340175896634187811 := by
  unfold tailWord_1310620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23901119255927525460304657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31868159007903367280406209 23901119255927525460304657)
  ·
    refine ⟨17925839441945644095228493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23901119255927525460304657 17925839441945644095228493)
    ·
      refine ⟨6722189790729616535710685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17925839441945644095228493 6722189790729616535710685)
      ·
        refine ⟨2520821171523606200891507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6722189790729616535710685 2520821171523606200891507)
        ·
          refine ⟨3781231757285409301337261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520821171523606200891507 3781231757285409301337261)
          ·
            refine ⟨1417961908982028488001473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3781231757285409301337261 1417961908982028488001473)
            ·
              refine ⟨1063471431736521366001105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1417961908982028488001473 1063471431736521366001105)
              ·
                refine ⟨797603573802391024500829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063471431736521366001105 797603573802391024500829)
                ·
                  refine ⟨299101340175896634187811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 797603573802391024500829 299101340175896634187811)
                  ·
                    rfl

theorem cell21_1310620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1310620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310620 prefixEnd_1310620 := by exact prefixLift 1310620
  have htrace : WordTrace (prefixWord ++ tailWord_1310620) baseStart_1310620 baseEnd_1310620 := by
    simpa [prefixWord, tailWord_1310620, baseEnd_1310620] using wordTrace_append hprefix tailTrace_1310620
  have hstable : (prefixWord ++ tailWord_1310620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310620).length < 2 ^ (prefixWord ++ tailWord_1310620).sum := by decide
  have hdescent : baseEnd_1310620 < baseStart_1310620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310631 : List Nat := [1, 1, 6, 1, 2, 3, 1, 6]
def baseStart_1310631 : Nat := 118140960795 + 1310631 * 2 ^ 59
def prefixEnd_1310631 : Nat := 4983230072969 + 3 ^ 40 * 1310631 * 2
def baseEnd_1310631 : Nat := 99701283508587686501485

theorem tailTrace_1310631 : CollatzResearch.WordTrace tailWord_1310631 prefixEnd_1310631 99701283508587686501485 := by
  unfold tailWord_1310631
  simp only [CollatzResearch.WordTrace]
  refine ⟨47802639714815199799259747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31868426476543466532839831 47802639714815199799259747)
  ·
    refine ⟨71703959572222799698889621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47802639714815199799259747 71703959572222799698889621)
    ·
      refine ⟨3361123104947943735885451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71703959572222799698889621 3361123104947943735885451)
      ·
        refine ⟨5041684657421915603828177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361123104947943735885451 5041684657421915603828177)
        ·
          refine ⟨3781263493066436702871133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5041684657421915603828177 3781263493066436702871133)
          ·
            refine ⟨1417973809899913763576675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3781263493066436702871133 1417973809899913763576675)
            ·
              refine ⟨2126960714849870645365013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417973809899913763576675 2126960714849870645365013)
              ·
                refine ⟨99701283508587686501485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2126960714849870645365013 99701283508587686501485)
                ·
                  rfl

theorem cell21_1310631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 6].length) (baseStart_1310631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310631 prefixEnd_1310631 := by exact prefixLift 1310631
  have htrace : WordTrace (prefixWord ++ tailWord_1310631) baseStart_1310631 baseEnd_1310631 := by
    simpa [prefixWord, tailWord_1310631, baseEnd_1310631] using wordTrace_append hprefix tailTrace_1310631
  have hstable : (prefixWord ++ tailWord_1310631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310631).length < 2 ^ (prefixWord ++ tailWord_1310631).sum := by decide
  have hdescent : baseEnd_1310631 < baseStart_1310631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310645 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_1310645 : Nat := 118140960795 + 1310645 * 2 ^ 59
def prefixEnd_1310645 : Nat := 4983230072969 + 3 ^ 40 * 1310645 * 2
def baseEnd_1310645 : Nat := 299107045516502146271093

theorem tailTrace_1310645 : CollatzResearch.WordTrace tailWord_1310645 prefixEnd_1310645 299107045516502146271093 := by
  unfold tailWord_1310645
  simp only [CollatzResearch.WordTrace]
  refine ⟨47803150336764480190269389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31868766891176320126846259 47803150336764480190269389)
  ·
    refine ⟨17926181376286680071351021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47803150336764480190269389 17926181376286680071351021)
    ·
      refine ⟨6722318016107505026756633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17926181376286680071351021 6722318016107505026756633)
      ·
        refine ⟨5041738512080628770067475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6722318016107505026756633 5041738512080628770067475)
        ·
          refine ⟨7562607768120943155101213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5041738512080628770067475 7562607768120943155101213)
          ·
            refine ⟨2835977913045353683162955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7562607768120943155101213 2835977913045353683162955)
            ·
              refine ⟨4253966869568030524744433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835977913045353683162955 4253966869568030524744433)
              ·
                refine ⟨3190475152176022893558325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253966869568030524744433 3190475152176022893558325)
                ·
                  refine ⟨299107045516502146271093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3190475152176022893558325 299107045516502146271093)
                  ·
                    rfl

theorem cell21_1310645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_1310645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310645 prefixEnd_1310645 := by exact prefixLift 1310645
  have htrace : WordTrace (prefixWord ++ tailWord_1310645) baseStart_1310645 baseEnd_1310645 := by
    simpa [prefixWord, tailWord_1310645, baseEnd_1310645] using wordTrace_append hprefix tailTrace_1310645
  have hstable : (prefixWord ++ tailWord_1310645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310645).length < 2 ^ (prefixWord ++ tailWord_1310645).sum := by decide
  have hdescent : baseEnd_1310645 < baseStart_1310645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310704 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_1310704 : Nat := 118140960795 + 1310704 * 2 ^ 59
def prefixEnd_1310704 : Nat := 4983230072969 + 3 ^ 40 * 1310704 * 2
def baseEnd_1310704 : Nat := 299120510120331154787639

theorem tailTrace_1310704 : CollatzResearch.WordTrace tailWord_1310704 prefixEnd_1310704 299120510120331154787639 := by
  unfold tailWord_1310704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23902651121775366633333583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31870201495700488844444777 23902651121775366633333583)
  ·
    refine ⟨35853976682663049950000375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23902651121775366633333583 35853976682663049950000375)
    ·
      refine ⟨53780965023994574925000563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35853976682663049950000375 53780965023994574925000563)
      ·
        refine ⟨80671447535991862387500845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53780965023994574925000563 80671447535991862387500845)
        ·
          refine ⟨30251792825996948395312817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80671447535991862387500845 30251792825996948395312817)
          ·
            refine ⟨22688844619497711296484613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30251792825996948395312817 22688844619497711296484613)
            ·
              refine ⟨4254158366155820868090865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22688844619497711296484613 4254158366155820868090865)
              ·
                refine ⟨3190618774616865651068149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254158366155820868090865 3190618774616865651068149)
                ·
                  refine ⟨299120510120331154787639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3190618774616865651068149 299120510120331154787639)
                  ·
                    rfl

theorem cell21_1310704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_1310704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310704 prefixEnd_1310704 := by exact prefixLift 1310704
  have htrace : WordTrace (prefixWord ++ tailWord_1310704) baseStart_1310704 baseEnd_1310704 := by
    simpa [prefixWord, tailWord_1310704, baseEnd_1310704] using wordTrace_append hprefix tailTrace_1310704
  have hstable : (prefixWord ++ tailWord_1310704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310704).length < 2 ^ (prefixWord ++ tailWord_1310704).sum := by decide
  have hdescent : baseEnd_1310704 < baseStart_1310704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310724 : List Nat := [2, 3, 2, 4, 2, 1, 7]
def baseStart_1310724 : Nat := 118140960795 + 1310724 * 2 ^ 59
def prefixEnd_1310724 : Nat := 4983230072969 + 3 ^ 40 * 1310724 * 2
def baseEnd_1310724 : Nat := 33236119376979507161585

theorem tailTrace_1310724 : CollatzResearch.WordTrace tailWord_1310724 prefixEnd_1310724 33236119376979507161585 := by
  unfold tailWord_1310724
  simp only [CollatzResearch.WordTrace]
  refine ⟨23903015851739138341197613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31870687802318851121596817 23903015851739138341197613)
  ·
    refine ⟨8963630944402176877949105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23903015851739138341197613 8963630944402176877949105)
    ·
      refine ⟨6722723208301632658461829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8963630944402176877949105 6722723208301632658461829)
      ·
        refine ⟨1260510601556556123461593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6722723208301632658461829 1260510601556556123461593)
        ·
          refine ⟨945382951167417092596195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260510601556556123461593 945382951167417092596195)
          ·
            refine ⟨1418074426751125638894293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945382951167417092596195 1418074426751125638894293)
            ·
              refine ⟨33236119376979507161585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1418074426751125638894293 33236119376979507161585)
              ·
                rfl

theorem cell21_1310724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 7].length) (baseStart_1310724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310724 prefixEnd_1310724 := by exact prefixLift 1310724
  have htrace : WordTrace (prefixWord ++ tailWord_1310724) baseStart_1310724 baseEnd_1310724 := by
    simpa [prefixWord, tailWord_1310724, baseEnd_1310724] using wordTrace_append hprefix tailTrace_1310724
  have hstable : (prefixWord ++ tailWord_1310724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310724).length < 2 ^ (prefixWord ++ tailWord_1310724).sum := by decide
  have hdescent : baseEnd_1310724 < baseStart_1310724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310766 : List Nat := [4, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1310766 : Nat := 118140960795 + 1310766 * 2 ^ 59
def prefixEnd_1310766 : Nat := 4983230072969 + 3 ^ 40 * 1310766 * 2
def baseEnd_1310766 : Nat := 99711553121677608251393

theorem tailTrace_1310766 : CollatzResearch.WordTrace tailWord_1310766 prefixEnd_1310766 99711553121677608251393 := by
  unfold tailWord_1310766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975945446165764731928019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31871709046217411903616101 5975945446165764731928019)
  ·
    refine ⟨8963918169248647097892029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5975945446165764731928019 8963918169248647097892029)
    ·
      refine ⟨3361469313468242661709511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8963918169248647097892029 3361469313468242661709511)
      ·
        refine ⟨5042203970202363992564267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361469313468242661709511 5042203970202363992564267)
        ·
          refine ⟨7563305955303545988846401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042203970202363992564267 7563305955303545988846401)
          ·
            refine ⟨5672479466477659491634801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7563305955303545988846401 5672479466477659491634801)
            ·
              refine ⟨4254359599858244618726101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5672479466477659491634801 4254359599858244618726101)
              ·
                refine ⟨99711553121677608251393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4254359599858244618726101 99711553121677608251393)
                ·
                  rfl

theorem cell21_1310766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1310766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310766 prefixEnd_1310766 := by exact prefixLift 1310766
  have htrace : WordTrace (prefixWord ++ tailWord_1310766) baseStart_1310766 baseEnd_1310766 := by
    simpa [prefixWord, tailWord_1310766, baseEnd_1310766] using wordTrace_append hprefix tailTrace_1310766
  have hstable : (prefixWord ++ tailWord_1310766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310766).length < 2 ^ (prefixWord ++ tailWord_1310766).sum := by decide
  have hdescent : baseEnd_1310766 < baseStart_1310766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310797 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1310797 : Nat := 118140960795 + 1310797 * 2 ^ 59
def prefixEnd_1310797 : Nat := 4983230072969 + 3 ^ 40 * 1310797 * 2
def baseEnd_1310797 : Nat := 299141733987383659737449

theorem tailTrace_1310797 : CollatzResearch.WordTrace tailWord_1310797 prefixEnd_1310797 299141733987383659737449 := by
  unfold tailWord_1310797
  simp only [CollatzResearch.WordTrace]
  refine ⟨47808694232213810149802645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31872462821475873433201763 47808694232213810149802645)
  ·
    refine ⟨2241032542135022350771999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47808694232213810149802645 2241032542135022350771999)
    ·
      refine ⟨3361548813202533526157999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2241032542135022350771999 3361548813202533526157999)
      ·
        refine ⟨5042323219803800289236999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361548813202533526157999 5042323219803800289236999)
        ·
          refine ⟨7563484829705700433855499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042323219803800289236999 7563484829705700433855499)
          ·
            refine ⟨11345227244558550650783249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7563484829705700433855499 11345227244558550650783249)
            ·
              refine ⟨8508920433418912988087437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11345227244558550650783249 8508920433418912988087437)
              ·
                refine ⟨3190845162532092370532789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8508920433418912988087437 3190845162532092370532789)
                ·
                  refine ⟨299141733987383659737449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3190845162532092370532789 299141733987383659737449)
                  ·
                    rfl

theorem cell21_1310797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1310797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310797 prefixEnd_1310797 := by exact prefixLift 1310797
  have htrace : WordTrace (prefixWord ++ tailWord_1310797) baseStart_1310797 baseEnd_1310797 := by
    simpa [prefixWord, tailWord_1310797, baseEnd_1310797] using wordTrace_append hprefix tailTrace_1310797
  have hstable : (prefixWord ++ tailWord_1310797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310797).length < 2 ^ (prefixWord ++ tailWord_1310797).sum := by decide
  have hdescent : baseEnd_1310797 < baseStart_1310797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310963 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_1310963 : Nat := 118140960795 + 1310963 * 2 ^ 59
def prefixEnd_1310963 : Nat := 4983230072969 + 3 ^ 40 * 1310963 * 2
def baseEnd_1310963 : Nat := 299179617449004259970443

theorem tailTrace_1310963 : CollatzResearch.WordTrace tailWord_1310963 prefixEnd_1310963 299179617449004259970443 := by
  unfold tailWord_1310963
  simp only [CollatzResearch.WordTrace]
  refine ⟨47814748749612420500345543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31876499166408280333563695 47814748749612420500345543)
  ·
    refine ⟨71722123124418630750518315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47814748749612420500345543 71722123124418630750518315)
    ·
      refine ⟨107583184686627946125777473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71722123124418630750518315 107583184686627946125777473)
      ·
        refine ⟨80687388514970959594333105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107583184686627946125777473 80687388514970959594333105)
        ·
          refine ⟨60515541386228219695749829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80687388514970959594333105 60515541386228219695749829)
          ·
            refine ⟨11346664009917791192953093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60515541386228219695749829 11346664009917791192953093)
            ·
              refine ⟨2127499501859585848678705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11346664009917791192953093 2127499501859585848678705)
              ·
                refine ⟨1595624626394689386509029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127499501859585848678705 1595624626394689386509029)
                ·
                  refine ⟨299179617449004259970443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595624626394689386509029 299179617449004259970443)
                  ·
                    rfl

theorem cell21_1310963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_1310963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1310963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1310963 prefixEnd_1310963 := by exact prefixLift 1310963
  have htrace : WordTrace (prefixWord ++ tailWord_1310963) baseStart_1310963 baseEnd_1310963 := by
    simpa [prefixWord, tailWord_1310963, baseEnd_1310963] using wordTrace_append hprefix tailTrace_1310963
  have hstable : (prefixWord ++ tailWord_1310963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310963).length < 2 ^ (prefixWord ++ tailWord_1310963).sum := by decide
  have hdescent : baseEnd_1310963 < baseStart_1310963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311025 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_1311025 : Nat := 118140960795 + 1311025 * 2 ^ 59
def prefixEnd_1311025 : Nat := 4983230072969 + 3 ^ 40 * 1311025 * 2
def baseEnd_1311025 : Nat := 299193766693705929936983

theorem tailTrace_1311025 : CollatzResearch.WordTrace tailWord_1311025 prefixEnd_1311025 299193766693705929936983 := by
  unfold tailWord_1311025
  simp only [CollatzResearch.WordTrace]
  refine ⟨47817010075387805089102529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31878006716925203392735019 47817010075387805089102529)
  ·
    refine ⟨35862757556540853816826897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47817010075387805089102529 35862757556540853816826897)
    ·
      refine ⟨26897068167405640362620173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35862757556540853816826897 26897068167405640362620173)
      ·
        refine ⟨10086400562777115135982565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26897068167405640362620173 10086400562777115135982565)
        ·
          refine ⟨1891200105520709087996731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10086400562777115135982565 1891200105520709087996731)
          ·
            refine ⟨2836800158281063631995097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891200105520709087996731 2836800158281063631995097)
            ·
              refine ⟨2127600118710797723996323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836800158281063631995097 2127600118710797723996323)
              ·
                refine ⟨3191400178066196585994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127600118710797723996323 3191400178066196585994485)
                ·
                  refine ⟨299193766693705929936983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191400178066196585994485 299193766693705929936983)
                  ·
                    rfl

theorem cell21_1311025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_1311025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311025 prefixEnd_1311025 := by exact prefixLift 1311025
  have htrace : WordTrace (prefixWord ++ tailWord_1311025) baseStart_1311025 baseEnd_1311025 := by
    simpa [prefixWord, tailWord_1311025, baseEnd_1311025] using wordTrace_append hprefix tailTrace_1311025
  have hstable : (prefixWord ++ tailWord_1311025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311025).length < 2 ^ (prefixWord ++ tailWord_1311025).sum := by decide
  have hdescent : baseEnd_1311025 < baseStart_1311025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311208 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_1311208 : Nat := 118140960795 + 1311208 * 2 ^ 59
def prefixEnd_1311208 : Nat := 4983230072969 + 3 ^ 40 * 1311208 * 2
def baseEnd_1311208 : Nat := 299235529786938278386609

theorem tailTrace_1311208 : CollatzResearch.WordTrace tailWord_1311208 prefixEnd_1311208 299235529786938278386609 := by
  unfold tailWord_1311208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23911842316862413671507139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31882456422483218228676185 23911842316862413671507139)
  ·
    refine ⟨35867763475293620507260709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23911842316862413671507139 35867763475293620507260709)
    ·
      refine ⟨6725205651617553845111383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35867763475293620507260709 6725205651617553845111383)
      ·
        refine ⟨10087808477426330767667075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725205651617553845111383 10087808477426330767667075)
        ·
          refine ⟨15131712716139496151500613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10087808477426330767667075 15131712716139496151500613)
          ·
            refine ⟨2837196134276155528406365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15131712716139496151500613 2837196134276155528406365)
            ·
              refine ⟨1063948550353558323152387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2837196134276155528406365 1063948550353558323152387)
              ·
                refine ⟨1595922825530337484728581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063948550353558323152387 1595922825530337484728581)
                ·
                  refine ⟨299235529786938278386609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595922825530337484728581 299235529786938278386609)
                  ·
                    rfl

theorem cell21_1311208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_1311208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311208 prefixEnd_1311208 := by exact prefixLift 1311208
  have htrace : WordTrace (prefixWord ++ tailWord_1311208) baseStart_1311208 baseEnd_1311208 := by
    simpa [prefixWord, tailWord_1311208, baseEnd_1311208] using wordTrace_append hprefix tailTrace_1311208
  have hstable : (prefixWord ++ tailWord_1311208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311208).length < 2 ^ (prefixWord ++ tailWord_1311208).sum := by decide
  have hdescent : baseEnd_1311208 < baseStart_1311208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311219 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_1311219 : Nat := 118140960795 + 1311219 * 2 ^ 59
def prefixEnd_1311219 : Nat := 4983230072969 + 3 ^ 40 * 1311219 * 2
def baseEnd_1311219 : Nat := 299238040136804703703253

theorem tailTrace_1311219 : CollatzResearch.WordTrace tailWord_1311219 prefixEnd_1311219 299238040136804703703253 := by
  unfold tailWord_1311219
  simp only [CollatzResearch.WordTrace]
  refine ⟨47824085836684976221664711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31882723891123317481109807 47824085836684976221664711)
  ·
    refine ⟨71736128755027464332497067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47824085836684976221664711 71736128755027464332497067)
    ·
      refine ⟨107604193132541196498745601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71736128755027464332497067 107604193132541196498745601)
      ·
        refine ⟨80703144849405897374059201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107604193132541196498745601 80703144849405897374059201)
        ·
          refine ⟨60527358637054423030544401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80703144849405897374059201 60527358637054423030544401)
          ·
            refine ⟨45395518977790817272908301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60527358637054423030544401 45395518977790817272908301)
            ·
              refine ⟨17023319616671556477340613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45395518977790817272908301 17023319616671556477340613)
              ·
                refine ⟨3191872428125916839501365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17023319616671556477340613 3191872428125916839501365)
                ·
                  refine ⟨299238040136804703703253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191872428125916839501365 299238040136804703703253)
                  ·
                    rfl

theorem cell21_1311219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_1311219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311219 prefixEnd_1311219 := by exact prefixLift 1311219
  have htrace : WordTrace (prefixWord ++ tailWord_1311219) baseStart_1311219 baseEnd_1311219 := by
    simpa [prefixWord, tailWord_1311219, baseEnd_1311219] using wordTrace_append hprefix tailTrace_1311219
  have hstable : (prefixWord ++ tailWord_1311219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311219).length < 2 ^ (prefixWord ++ tailWord_1311219).sum := by decide
  have hdescent : baseEnd_1311219 < baseStart_1311219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311267 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_1311267 : Nat := 118140960795 + 1311267 * 2 ^ 59
def prefixEnd_1311267 : Nat := 4983230072969 + 3 ^ 40 * 1311267 * 2
def baseEnd_1311267 : Nat := 299248994390767286903155

theorem tailTrace_1311267 : CollatzResearch.WordTrace tailWord_1311267 prefixEnd_1311267 299248994390767286903155 := by
  unfold tailWord_1311267
  simp only [CollatzResearch.WordTrace]
  refine ⟨47825836540511080419412055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31883891027007386946274703 47825836540511080419412055)
  ·
    refine ⟨71738754810766620629118083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47825836540511080419412055 71738754810766620629118083)
    ·
      refine ⟨107608132216149930943677125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71738754810766620629118083 107608132216149930943677125)
      ·
        refine ⟨20176524790528112051939461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107608132216149930943677125 20176524790528112051939461)
        ·
          refine ⟨3783098398224021009738649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20176524790528112051939461 3783098398224021009738649)
          ·
            refine ⟨2837323798668015757303987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783098398224021009738649 2837323798668015757303987)
            ·
              refine ⟨4255985698002023635955981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837323798668015757303987 4255985698002023635955981)
              ·
                refine ⟨1595994636750758863483493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4255985698002023635955981 1595994636750758863483493)
                ·
                  refine ⟨299248994390767286903155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595994636750758863483493 299248994390767286903155)
                  ·
                    rfl

theorem cell21_1311267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_1311267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311267 prefixEnd_1311267 := by exact prefixLift 1311267
  have htrace : WordTrace (prefixWord ++ tailWord_1311267) baseStart_1311267 baseEnd_1311267 := by
    simpa [prefixWord, tailWord_1311267, baseEnd_1311267] using wordTrace_append hprefix tailTrace_1311267
  have hstable : (prefixWord ++ tailWord_1311267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311267).length < 2 ^ (prefixWord ++ tailWord_1311267).sum := by decide
  have hdescent : baseEnd_1311267 < baseStart_1311267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311340 : List Nat := [2, 2, 1, 1, 3, 1, 2, 9]
def baseStart_1311340 : Nat := 118140960795 + 1311340 * 2 ^ 59
def prefixEnd_1311340 : Nat := 4983230072969 + 3 ^ 40 * 1311340 * 2
def baseEnd_1311340 : Nat := 99755217995111794062113

theorem tailTrace_1311340 : CollatzResearch.WordTrace tailWord_1311340 prefixEnd_1311340 99755217995111794062113 := by
  unfold tailWord_1311340
  simp only [CollatzResearch.WordTrace]
  refine ⟨23914249534623306943409737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31885666046164409257879649 23914249534623306943409737)
  ·
    refine ⟨17935687150967480207557303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23914249534623306943409737 17935687150967480207557303)
    ·
      refine ⟨26903530726451220311335955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17935687150967480207557303 26903530726451220311335955)
      ·
        refine ⟨40355296089676830467003933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26903530726451220311335955 40355296089676830467003933)
        ·
          refine ⟨15133236033628811425126475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40355296089676830467003933 15133236033628811425126475)
          ·
            refine ⟨22699854050443217137689713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15133236033628811425126475 22699854050443217137689713)
            ·
              refine ⟨17024890537832412853267285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22699854050443217137689713 17024890537832412853267285)
              ·
                refine ⟨99755217995111794062113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17024890537832412853267285 99755217995111794062113)
                ·
                  rfl

theorem cell21_1311340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_1311340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311340 prefixEnd_1311340 := by exact prefixLift 1311340
  have htrace : WordTrace (prefixWord ++ tailWord_1311340) baseStart_1311340 baseEnd_1311340 := by
    simpa [prefixWord, tailWord_1311340, baseEnd_1311340] using wordTrace_append hprefix tailTrace_1311340
  have hstable : (prefixWord ++ tailWord_1311340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311340).length < 2 ^ (prefixWord ++ tailWord_1311340).sum := by decide
  have hdescent : baseEnd_1311340 < baseStart_1311340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311346 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1311346 : Nat := 118140960795 + 1311346 * 2 ^ 59
def prefixEnd_1311346 : Nat := 4983230072969 + 3 ^ 40 * 1311346 * 2
def baseEnd_1311346 : Nat := 299267023267080705086327

theorem tailTrace_1311346 : CollatzResearch.WordTrace tailWord_1311346 prefixEnd_1311346 299267023267080705086327 := by
  unfold tailWord_1311346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957179476806219227884473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31885811938149917941025261 11957179476806219227884473)
  ·
    refine ⟨8967884607604664420913355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11957179476806219227884473 8967884607604664420913355)
    ·
      refine ⟨13451826911406996631370033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967884607604664420913355 13451826911406996631370033)
      ·
        refine ⟨10088870183555247473527525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13451826911406996631370033 10088870183555247473527525)
        ·
          refine ⟨1891663159416608901286411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10088870183555247473527525 1891663159416608901286411)
          ·
            refine ⟨2837494739124913351929617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891663159416608901286411 2837494739124913351929617)
            ·
              refine ⟨2128121054343685013947213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2837494739124913351929617 2128121054343685013947213)
              ·
                refine ⟨798045395378881880230205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128121054343685013947213 798045395378881880230205)
                ·
                  refine ⟨299267023267080705086327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798045395378881880230205 299267023267080705086327)
                  ·
                    rfl

theorem cell21_1311346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1311346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311346 prefixEnd_1311346 := by exact prefixLift 1311346
  have htrace : WordTrace (prefixWord ++ tailWord_1311346) baseStart_1311346 baseEnd_1311346 := by
    simpa [prefixWord, tailWord_1311346, baseEnd_1311346] using wordTrace_append hprefix tailTrace_1311346
  have hstable : (prefixWord ++ tailWord_1311346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311346).length < 2 ^ (prefixWord ++ tailWord_1311346).sum := by decide
  have hdescent : baseEnd_1311346 < baseStart_1311346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311357 : List Nat := [1, 4, 1, 1, 5, 1, 8]
def baseStart_1311357 : Nat := 118140960795 + 1311357 * 2 ^ 59
def prefixEnd_1311357 : Nat := 4983230072969 + 3 ^ 40 * 1311357 * 2
def baseEnd_1311357 : Nat := 33252170401883014489219

theorem tailTrace_1311357 : CollatzResearch.WordTrace tailWord_1311357 prefixEnd_1311357 33252170401883014489219 := by
  unfold tailWord_1311357
  simp only [CollatzResearch.WordTrace]
  refine ⟨47829119110185025790188325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31886079406790017193458883 47829119110185025790188325)
  ·
    refine ⟨8967959833159692335660311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47829119110185025790188325 8967959833159692335660311)
    ·
      refine ⟨13451939749739538503490467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967959833159692335660311 13451939749739538503490467)
      ·
        refine ⟨20177909624609307755235701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451939749739538503490467 20177909624609307755235701)
        ·
          refine ⟨1891679027307122602053347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20177909624609307755235701 1891679027307122602053347)
          ·
            refine ⟨2837518540960683903080021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891679027307122602053347 2837518540960683903080021)
            ·
              refine ⟨33252170401883014489219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2837518540960683903080021 33252170401883014489219)
              ·
                rfl

theorem cell21_1311357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 8].length) (baseStart_1311357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311357 prefixEnd_1311357 := by exact prefixLift 1311357
  have htrace : WordTrace (prefixWord ++ tailWord_1311357) baseStart_1311357 baseEnd_1311357 := by
    simpa [prefixWord, tailWord_1311357, baseEnd_1311357] using wordTrace_append hprefix tailTrace_1311357
  have hstable : (prefixWord ++ tailWord_1311357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311357).length < 2 ^ (prefixWord ++ tailWord_1311357).sum := by decide
  have hdescent : baseEnd_1311357 < baseStart_1311357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311388 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1311388 : Nat := 118140960795 + 1311388 * 2 ^ 59
def prefixEnd_1311388 : Nat := 4983230072969 + 3 ^ 40 * 1311388 * 2
def baseEnd_1311388 : Nat := 299276608239297965386241

theorem tailTrace_1311388 : CollatzResearch.WordTrace tailWord_1311388 prefixEnd_1311388 299276608239297965386241 := by
  unfold tailWord_1311388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23915124886536359042283409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31886833182048478723044545 23915124886536359042283409)
  ·
    refine ⟨17936343664902269281712557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23915124886536359042283409 17936343664902269281712557)
    ·
      refine ⟨6726128874338350980642209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17936343664902269281712557 6726128874338350980642209)
      ·
        refine ⟨5044596655753763235481657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6726128874338350980642209 5044596655753763235481657)
        ·
          refine ⟨3783447491815322426611243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5044596655753763235481657 3783447491815322426611243)
          ·
            refine ⟨5675171237722983639916865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783447491815322426611243 5675171237722983639916865)
            ·
              refine ⟨4256378428292237729937649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675171237722983639916865 4256378428292237729937649)
              ·
                refine ⟨3192283821219178297453237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256378428292237729937649 3192283821219178297453237)
                ·
                  refine ⟨299276608239297965386241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192283821219178297453237 299276608239297965386241)
                  ·
                    rfl

theorem cell21_1311388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1311388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311388 prefixEnd_1311388 := by exact prefixLift 1311388
  have htrace : WordTrace (prefixWord ++ tailWord_1311388) baseStart_1311388 baseEnd_1311388 := by
    simpa [prefixWord, tailWord_1311388, baseEnd_1311388] using wordTrace_append hprefix tailTrace_1311388
  have hstable : (prefixWord ++ tailWord_1311388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311388).length < 2 ^ (prefixWord ++ tailWord_1311388).sum := by decide
  have hdescent : baseEnd_1311388 < baseStart_1311388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311422 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_1311422 : Nat := 118140960795 + 1311422 * 2 ^ 59
def prefixEnd_1311422 : Nat := 4983230072969 + 3 ^ 40 * 1311422 * 2
def baseEnd_1311422 : Nat := 299284367502521461819505

theorem tailTrace_1311422 : CollatzResearch.WordTrace tailWord_1311422 prefixEnd_1311422 299284367502521461819505 := by
  unfold tailWord_1311422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978936231868692736413065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31887659903299694594203013 5978936231868692736413065)
  ·
    refine ⟨4484202173901519552309799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5978936231868692736413065 4484202173901519552309799)
    ·
      refine ⟨6726303260852279328464699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484202173901519552309799 6726303260852279328464699)
      ·
        refine ⟨10089454891278418992697049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6726303260852279328464699 10089454891278418992697049)
        ·
          refine ⟨7567091168458814244522787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10089454891278418992697049 7567091168458814244522787)
          ·
            refine ⟨11350636752688221366784181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567091168458814244522787 11350636752688221366784181)
            ·
              refine ⟨1064122195564520753136017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11350636752688221366784181 1064122195564520753136017)
              ·
                refine ⟨798091646673390564852013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064122195564520753136017 798091646673390564852013)
                ·
                  refine ⟨299284367502521461819505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798091646673390564852013 299284367502521461819505)
                  ·
                    rfl

theorem cell21_1311422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_1311422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311422 prefixEnd_1311422 := by exact prefixLift 1311422
  have htrace : WordTrace (prefixWord ++ tailWord_1311422) baseStart_1311422 baseEnd_1311422 := by
    simpa [prefixWord, tailWord_1311422, baseEnd_1311422] using wordTrace_append hprefix tailTrace_1311422
  have hstable : (prefixWord ++ tailWord_1311422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311422).length < 2 ^ (prefixWord ++ tailWord_1311422).sum := by decide
  have hdescent : baseEnd_1311422 < baseStart_1311422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311436 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1311436 : Nat := 118140960795 + 1311436 * 2 ^ 59
def prefixEnd_1311436 : Nat := 4983230072969 + 3 ^ 40 * 1311436 * 2
def baseEnd_1311436 : Nat := 299287562493260548586143

theorem tailTrace_1311436 : CollatzResearch.WordTrace tailWord_1311436 prefixEnd_1311436 299287562493260548586143 := by
  unfold tailWord_1311436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23916000238449411141157081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31888000317932548188209441 23916000238449411141157081)
  ·
    refine ⟨17937000178837058355867811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23916000238449411141157081 17937000178837058355867811)
    ·
      refine ⟨26905500268255587533801717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17937000178837058355867811 26905500268255587533801717)
      ·
        refine ⟨2522390650148961331293911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26905500268255587533801717 2522390650148961331293911)
        ·
          refine ⟨3783585975223441996940867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522390650148961331293911 3783585975223441996940867)
          ·
            refine ⟨5675378962835162995411301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783585975223441996940867 5675378962835162995411301)
            ·
              refine ⟨1064133555531593061639619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5675378962835162995411301 1064133555531593061639619)
              ·
                refine ⟨1596200333297389592459429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064133555531593061639619 1596200333297389592459429)
                ·
                  refine ⟨299287562493260548586143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596200333297389592459429 299287562493260548586143)
                  ·
                    rfl

theorem cell21_1311436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1311436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311436 prefixEnd_1311436 := by exact prefixLift 1311436
  have htrace : WordTrace (prefixWord ++ tailWord_1311436) baseStart_1311436 baseEnd_1311436 := by
    simpa [prefixWord, tailWord_1311436, baseEnd_1311436] using wordTrace_append hprefix tailTrace_1311436
  have hstable : (prefixWord ++ tailWord_1311436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311436).length < 2 ^ (prefixWord ++ tailWord_1311436).sum := by decide
  have hdescent : baseEnd_1311436 < baseStart_1311436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311495 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_1311495 : Nat := 118140960795 + 1311495 * 2 ^ 59
def prefixEnd_1311495 : Nat := 4983230072969 + 3 ^ 40 * 1311495 * 2
def baseEnd_1311495 : Nat := 299301027097089557102689

theorem tailTrace_1311495 : CollatzResearch.WordTrace tailWord_1311495 prefixEnd_1311495 299301027097089557102689 := by
  unfold tailWord_1311495
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834152383685075358711939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31889434922456716905807959 47834152383685075358711939)
  ·
    refine ⟨71751228575527613038067909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47834152383685075358711939 71751228575527613038067909)
    ·
      refine ⟨13453355357911427444637733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71751228575527613038067909 13453355357911427444637733)
      ·
        refine ⟨2522504129608392645869575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13453355357911427444637733 2522504129608392645869575)
        ·
          refine ⟨3783756194412588968804363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522504129608392645869575 3783756194412588968804363)
          ·
            refine ⟨5675634291618883453206545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783756194412588968804363 5675634291618883453206545)
            ·
              refine ⟨4256725718714162589904909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675634291618883453206545 4256725718714162589904909)
              ·
                refine ⟨1596272144517810971214341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256725718714162589904909 1596272144517810971214341)
                ·
                  refine ⟨299301027097089557102689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596272144517810971214341 299301027097089557102689)
                  ·
                    rfl

theorem cell21_1311495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_1311495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311495 prefixEnd_1311495 := by exact prefixLift 1311495
  have htrace : WordTrace (prefixWord ++ tailWord_1311495) baseStart_1311495 baseEnd_1311495 := by
    simpa [prefixWord, tailWord_1311495, baseEnd_1311495] using wordTrace_append hprefix tailTrace_1311495
  have hstable : (prefixWord ++ tailWord_1311495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311495).length < 2 ^ (prefixWord ++ tailWord_1311495).sum := by decide
  have hdescent : baseEnd_1311495 < baseStart_1311495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311509 : List Nat := [1, 3, 2, 1, 2, 2, 5, 5]
def baseStart_1311509 : Nat := 118140960795 + 1311509 * 2 ^ 59
def prefixEnd_1311509 : Nat := 4983230072969 + 3 ^ 40 * 1311509 * 2
def baseEnd_1311509 : Nat := 99768074029276214623109

theorem tailTrace_1311509 : CollatzResearch.WordTrace tailWord_1311509 prefixEnd_1311509 99768074029276214623109 := by
  unfold tailWord_1311509
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834663005634355749721581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31889775337089570499814387 47834663005634355749721581)
  ·
    refine ⟨17937998627112883406145593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47834663005634355749721581 17937998627112883406145593)
    ·
      refine ⟨13453498970334662554609195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17937998627112883406145593 13453498970334662554609195)
      ·
        refine ⟨20180248455501993831913793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13453498970334662554609195 20180248455501993831913793)
        ·
          refine ⟨15135186341626495373935345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20180248455501993831913793 15135186341626495373935345)
          ·
            refine ⟨11351389756219871530451509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15135186341626495373935345 11351389756219871530451509)
            ·
              refine ⟨1064192789645612955979829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11351389756219871530451509 1064192789645612955979829)
              ·
                refine ⟨99768074029276214623109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1064192789645612955979829 99768074029276214623109)
                ·
                  rfl

theorem cell21_1311509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 5].length) (baseStart_1311509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311509 prefixEnd_1311509 := by exact prefixLift 1311509
  have htrace : WordTrace (prefixWord ++ tailWord_1311509) baseStart_1311509 baseEnd_1311509 := by
    simpa [prefixWord, tailWord_1311509, baseEnd_1311509] using wordTrace_append hprefix tailTrace_1311509
  have hstable : (prefixWord ++ tailWord_1311509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311509).length < 2 ^ (prefixWord ++ tailWord_1311509).sum := by decide
  have hdescent : baseEnd_1311509 < baseStart_1311509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311644 : List Nat := [2, 2, 3, 3, 11]
def baseStart_1311644 : Nat := 118140960795 + 1311644 * 2 ^ 59
def prefixEnd_1311644 : Nat := 4983230072969 + 3 ^ 40 * 1311644 * 2
def baseEnd_1311644 : Nat := 3695494208976523569371

theorem tailTrace_1311644 : CollatzResearch.WordTrace tailWord_1311644 prefixEnd_1311644 3695494208976523569371 := by
  unfold tailWord_1311644
  simp only [CollatzResearch.WordTrace]
  refine ⟨23919793430072636902942993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31893057906763515870590657 23919793430072636902942993)
  ·
    refine ⟨17939845072554477677207245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23919793430072636902942993 17939845072554477677207245)
    ·
      refine ⟨6727441902207929128952717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17939845072554477677207245 6727441902207929128952717)
      ·
        refine ⟨2522790713327973423357269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6727441902207929128952717 2522790713327973423357269)
        ·
          refine ⟨3695494208976523569371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2522790713327973423357269 3695494208976523569371)
          ·
            rfl

theorem cell21_1311644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 11].length) (baseStart_1311644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311644 prefixEnd_1311644 := by exact prefixLift 1311644
  have htrace : WordTrace (prefixWord ++ tailWord_1311644) baseStart_1311644 baseEnd_1311644 := by
    simpa [prefixWord, tailWord_1311644, baseEnd_1311644] using wordTrace_append hprefix tailTrace_1311644
  have hstable : (prefixWord ++ tailWord_1311644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311644).length < 2 ^ (prefixWord ++ tailWord_1311644).sum := by decide
  have hdescent : baseEnd_1311644 < baseStart_1311644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311647 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_1311647 : Nat := 118140960795 + 1311647 * 2 ^ 59
def prefixEnd_1311647 : Nat := 4983230072969 + 3 ^ 40 * 1311647 * 2
def baseEnd_1311647 : Nat := 299335715567971070569045

theorem tailTrace_1311647 : CollatzResearch.WordTrace tailWord_1311647 prefixEnd_1311647 299335715567971070569045 := by
  unfold tailWord_1311647
  simp only [CollatzResearch.WordTrace]
  refine ⟨47839696279134405318245195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31893130852756270212163463 47839696279134405318245195)
  ·
    refine ⟨71759544418701607977367793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47839696279134405318245195 71759544418701607977367793)
    ·
      refine ⟨53819658314026205983025845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71759544418701607977367793 53819658314026205983025845)
      ·
        refine ⟨5045592966939956810908673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53819658314026205983025845 5045592966939956810908673)
        ·
          refine ⟨3784194725204967608181505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5045592966939956810908673 3784194725204967608181505)
          ·
            refine ⟨2838146043903725706136129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3784194725204967608181505 2838146043903725706136129)
            ·
              refine ⟨2128609532927794279602097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2838146043903725706136129 2128609532927794279602097)
              ·
                refine ⟨1596457149695845709701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128609532927794279602097 1596457149695845709701573)
                ·
                  refine ⟨299335715567971070569045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596457149695845709701573 299335715567971070569045)
                  ·
                    rfl

theorem cell21_1311647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_1311647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311647 prefixEnd_1311647 := by exact prefixLift 1311647
  have htrace : WordTrace (prefixWord ++ tailWord_1311647) baseStart_1311647 baseEnd_1311647 := by
    simpa [prefixWord, tailWord_1311647, baseEnd_1311647] using wordTrace_append hprefix tailTrace_1311647
  have hstable : (prefixWord ++ tailWord_1311647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311647).length < 2 ^ (prefixWord ++ tailWord_1311647).sum := by decide
  have hdescent : baseEnd_1311647 < baseStart_1311647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311650 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1311650 : Nat := 118140960795 + 1311650 * 2 ^ 59
def prefixEnd_1311650 : Nat := 4983230072969 + 3 ^ 40 * 1311650 * 2
def baseEnd_1311650 : Nat := 299336400208843732019039

theorem tailTrace_1311650 : CollatzResearch.WordTrace tailWord_1311650 prefixEnd_1311650 299336400208843732019039 := by
  unfold tailWord_1311650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11959951424530884207651101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31893203798749024553736269 11959951424530884207651101)
  ·
    refine ⟨4484981784199081577869163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11959951424530884207651101 4484981784199081577869163)
    ·
      refine ⟨6727472676298622366803745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484981784199081577869163 6727472676298622366803745)
      ·
        refine ⟨5045604507223966775102809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6727472676298622366803745 5045604507223966775102809)
        ·
          refine ⟨3784203380417975081327107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5045604507223966775102809 3784203380417975081327107)
          ·
            refine ⟨5676305070626962621990661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784203380417975081327107 5676305070626962621990661)
            ·
              refine ⟨1064307200742555491623249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5676305070626962621990661 1064307200742555491623249)
              ·
                refine ⟨798230400556916618717437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064307200742555491623249 798230400556916618717437)
                ·
                  refine ⟨299336400208843732019039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798230400556916618717437 299336400208843732019039)
                  ·
                    rfl

theorem cell21_1311650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1311650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311650 prefixEnd_1311650 := by exact prefixLift 1311650
  have htrace : WordTrace (prefixWord ++ tailWord_1311650) baseStart_1311650 baseEnd_1311650 := by
    simpa [prefixWord, tailWord_1311650, baseEnd_1311650] using wordTrace_append hprefix tailTrace_1311650
  have hstable : (prefixWord ++ tailWord_1311650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311650).length < 2 ^ (prefixWord ++ tailWord_1311650).sum := by decide
  have hdescent : baseEnd_1311650 < baseStart_1311650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311706 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1311706 : Nat := 118140960795 + 1311706 * 2 ^ 59
def prefixEnd_1311706 : Nat := 4983230072969 + 3 ^ 40 * 1311706 * 2
def baseEnd_1311706 : Nat := 299349180171800079085591

theorem tailTrace_1311706 : CollatzResearch.WordTrace tailWord_1311706 prefixEnd_1311706 299349180171800079085591 := by
  unfold tailWord_1311706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11960462046480164598660743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31894565457280438929761981 11960462046480164598660743)
  ·
    refine ⟨17940693069720246897991115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11960462046480164598660743 17940693069720246897991115)
    ·
      refine ⟨26911039604580370346986673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17940693069720246897991115 26911039604580370346986673)
      ·
        refine ⟨20183279703435277760240005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26911039604580370346986673 20183279703435277760240005)
        ·
          refine ⟨3784364944394114580045001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20183279703435277760240005 3784364944394114580045001)
          ·
            refine ⟨2838273708295585935033751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3784364944394114580045001 2838273708295585935033751)
            ·
              refine ⟨4257410562443378902550627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838273708295585935033751 4257410562443378902550627)
              ·
                refine ⟨6386115843665068353825941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257410562443378902550627 6386115843665068353825941)
                ·
                  refine ⟨299349180171800079085591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6386115843665068353825941 299349180171800079085591)
                  ·
                    rfl

theorem cell21_1311706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1311706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311706 prefixEnd_1311706 := by exact prefixLift 1311706
  have htrace : WordTrace (prefixWord ++ tailWord_1311706) baseStart_1311706 baseEnd_1311706 := by
    simpa [prefixWord, tailWord_1311706, baseEnd_1311706] using wordTrace_append hprefix tailTrace_1311706
  have hstable : (prefixWord ++ tailWord_1311706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311706).length < 2 ^ (prefixWord ++ tailWord_1311706).sum := by decide
  have hdescent : baseEnd_1311706 < baseStart_1311706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311709 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1311709 : Nat := 118140960795 + 1311709 * 2 ^ 59
def prefixEnd_1311709 : Nat := 4983230072969 + 3 ^ 40 * 1311709 * 2
def baseEnd_1311709 : Nat := 299349864812672740535585

theorem tailTrace_1311709 : CollatzResearch.WordTrace tailWord_1311709 prefixEnd_1311709 299349864812672740535585 := by
  unfold tailWord_1311709
  simp only [CollatzResearch.WordTrace]
  refine ⟨47841957604909789907002181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31894638403273193271334787 47841957604909789907002181)
  ·
    refine ⟨8970367050920585607562909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47841957604909789907002181 8970367050920585607562909)
    ·
      refine ⟨3363887644095219602836091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8970367050920585607562909 3363887644095219602836091)
      ·
        refine ⟨5045831466142829404254137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363887644095219602836091 5045831466142829404254137)
        ·
          refine ⟨3784373599607122053190603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5045831466142829404254137 3784373599607122053190603)
          ·
            refine ⟨5676560399410683079785905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784373599607122053190603 5676560399410683079785905)
            ·
              refine ⟨4257420299558012309839429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5676560399410683079785905 4257420299558012309839429)
              ·
                refine ⟨798266306167127308094893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4257420299558012309839429 798266306167127308094893)
                ·
                  refine ⟨299349864812672740535585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798266306167127308094893 299349864812672740535585)
                  ·
                    rfl

theorem cell21_1311709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1311709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311709 prefixEnd_1311709 := by exact prefixLift 1311709
  have htrace : WordTrace (prefixWord ++ tailWord_1311709) baseStart_1311709 baseEnd_1311709 := by
    simpa [prefixWord, tailWord_1311709, baseEnd_1311709] using wordTrace_append hprefix tailTrace_1311709
  have hstable : (prefixWord ++ tailWord_1311709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311709).length < 2 ^ (prefixWord ++ tailWord_1311709).sum := by decide
  have hdescent : baseEnd_1311709 < baseStart_1311709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311768 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_1311768 : Nat := 118140960795 + 1311768 * 2 ^ 59
def prefixEnd_1311768 : Nat := 4983230072969 + 3 ^ 40 * 1311768 * 2
def baseEnd_1311768 : Nat := 299363329416501749052131

theorem tailTrace_1311768 : CollatzResearch.WordTrace tailWord_1311768 prefixEnd_1311768 299363329416501749052131 := by
  unfold tailWord_1311768
  simp only [CollatzResearch.WordTrace]
  refine ⟨23922054755848021491699979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31896073007797361988933305 23922054755848021491699979)
  ·
    refine ⟨35883082133772032237549969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23922054755848021491699979 35883082133772032237549969)
    ·
      refine ⟨26912311600329024178162477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35883082133772032237549969 26912311600329024178162477)
      ·
        refine ⟨10092116850123384066810929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26912311600329024178162477 10092116850123384066810929)
        ·
          refine ⟨7569087637592538050108197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10092116850123384066810929 7569087637592538050108197)
          ·
            refine ⟨1419203932048600884395287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7569087637592538050108197 1419203932048600884395287)
            ·
              refine ⟨2128805898072901326592931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419203932048600884395287 2128805898072901326592931)
              ·
                refine ⟨3193208847109351989889397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128805898072901326592931 3193208847109351989889397)
                ·
                  refine ⟨299363329416501749052131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3193208847109351989889397 299363329416501749052131)
                  ·
                    rfl

theorem cell21_1311768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_1311768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311768 prefixEnd_1311768 := by exact prefixLift 1311768
  have htrace : WordTrace (prefixWord ++ tailWord_1311768) baseStart_1311768 baseEnd_1311768 := by
    simpa [prefixWord, tailWord_1311768, baseEnd_1311768] using wordTrace_append hprefix tailTrace_1311768
  have hstable : (prefixWord ++ tailWord_1311768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311768).length < 2 ^ (prefixWord ++ tailWord_1311768).sum := by decide
  have hdescent : baseEnd_1311768 < baseStart_1311768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311934 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1311934 : Nat := 118140960795 + 1311934 * 2 ^ 59
def prefixEnd_1311934 : Nat := 4983230072969 + 3 ^ 40 * 1311934 * 2
def baseEnd_1311934 : Nat := 299401212878122349285125

theorem tailTrace_1311934 : CollatzResearch.WordTrace tailWord_1311934 prefixEnd_1311934 299401212878122349285125 := by
  unfold tailWord_1311934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981270503636831666742857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31900109352729768889295237 5981270503636831666742857)
  ·
    refine ⟨4485952877727623750057143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5981270503636831666742857 4485952877727623750057143)
    ·
      refine ⟨6728929316591435625085715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485952877727623750057143 6728929316591435625085715)
      ·
        refine ⟨10093393974887153437628573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728929316591435625085715 10093393974887153437628573)
        ·
          refine ⟨3785022740582682539110715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10093393974887153437628573 3785022740582682539110715)
          ·
            refine ⟨5677534110874023808666073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785022740582682539110715 5677534110874023808666073)
            ·
              refine ⟨4258150583155517856499555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677534110874023808666073 4258150583155517856499555)
              ·
                refine ⟨6387225874733276784749333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258150583155517856499555 6387225874733276784749333)
                ·
                  refine ⟨299401212878122349285125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6387225874733276784749333 299401212878122349285125)
                  ·
                    rfl

theorem cell21_1311934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1311934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311934 prefixEnd_1311934 := by exact prefixLift 1311934
  have htrace : WordTrace (prefixWord ++ tailWord_1311934) baseStart_1311934 baseEnd_1311934 := by
    simpa [prefixWord, tailWord_1311934, baseEnd_1311934] using wordTrace_append hprefix tailTrace_1311934
  have hstable : (prefixWord ++ tailWord_1311934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311934).length < 2 ^ (prefixWord ++ tailWord_1311934).sum := by decide
  have hdescent : baseEnd_1311934 < baseStart_1311934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311937 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 5]
def baseStart_1311937 : Nat := 118140960795 + 1311937 * 2 ^ 59
def prefixEnd_1311937 : Nat := 4983230072969 + 3 ^ 40 * 1311937 * 2
def baseEnd_1311937 : Nat := 299401897518995010735119

theorem tailTrace_1311937 : CollatzResearch.WordTrace tailWord_1311937 prefixEnd_1311937 299401897518995010735119 := by
  unfold tailWord_1311937
  simp only [CollatzResearch.WordTrace]
  refine ⟨47850273448083784846302065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31900182298722523230868043 47850273448083784846302065)
  ·
    refine ⟨35887705086062838634726549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47850273448083784846302065 35887705086062838634726549)
    ·
      refine ⟨1682236175909195561002807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35887705086062838634726549 1682236175909195561002807)
      ·
        refine ⟨2523354263863793341504211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682236175909195561002807 2523354263863793341504211)
        ·
          refine ⟨3785031395795690012256317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523354263863793341504211 3785031395795690012256317)
          ·
            refine ⟨1419386773423383754596119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3785031395795690012256317 1419386773423383754596119)
            ·
              refine ⟨2129080160135075631894179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419386773423383754596119 2129080160135075631894179)
              ·
                refine ⟨3193620240202613447841269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129080160135075631894179 3193620240202613447841269)
                ·
                  refine ⟨299401897518995010735119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3193620240202613447841269 299401897518995010735119)
                  ·
                    rfl

theorem cell21_1311937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_1311937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311937 prefixEnd_1311937 := by exact prefixLift 1311937
  have htrace : WordTrace (prefixWord ++ tailWord_1311937) baseStart_1311937 baseEnd_1311937 := by
    simpa [prefixWord, tailWord_1311937, baseEnd_1311937] using wordTrace_append hprefix tailTrace_1311937
  have hstable : (prefixWord ++ tailWord_1311937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311937).length < 2 ^ (prefixWord ++ tailWord_1311937).sum := by decide
  have hdescent : baseEnd_1311937 < baseStart_1311937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311962 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1311962 : Nat := 118140960795 + 1311962 * 2 ^ 59
def prefixEnd_1311962 : Nat := 4983230072969 + 3 ^ 40 * 1311962 * 2
def baseEnd_1311962 : Nat := 299407602859600522818401

theorem tailTrace_1311962 : CollatzResearch.WordTrace tailWord_1311962 prefixEnd_1311962 299407602859600522818401 := by
  unfold tailWord_1311962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962796318248303528990535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31900790181995476077308093 11962796318248303528990535)
  ·
    refine ⟨17944194477372455293485803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11962796318248303528990535 17944194477372455293485803)
    ·
      refine ⟨26916291716058682940228705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17944194477372455293485803 26916291716058682940228705)
      ·
        refine ⟨20187218787044012205171529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26916291716058682940228705 20187218787044012205171529)
        ·
          refine ⟨15140414090283009153878647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20187218787044012205171529 15140414090283009153878647)
          ·
            refine ⟨22710621135424513730817971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15140414090283009153878647 22710621135424513730817971)
            ·
              refine ⟨34065931703136770596226957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22710621135424513730817971 34065931703136770596226957)
              ·
                refine ⟨12774724388676288973585109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34065931703136770596226957 12774724388676288973585109)
                ·
                  refine ⟨299407602859600522818401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12774724388676288973585109 299407602859600522818401)
                  ·
                    rfl

theorem cell21_1311962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1311962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1311962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1311962 prefixEnd_1311962 := by exact prefixLift 1311962
  have htrace : WordTrace (prefixWord ++ tailWord_1311962) baseStart_1311962 baseEnd_1311962 := by
    simpa [prefixWord, tailWord_1311962, baseEnd_1311962] using wordTrace_append hprefix tailTrace_1311962
  have hstable : (prefixWord ++ tailWord_1311962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311962).length < 2 ^ (prefixWord ++ tailWord_1311962).sum := by decide
  have hdescent : baseEnd_1311962 < baseStart_1311962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312069 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1312069 : Nat := 118140960795 + 1312069 * 2 ^ 59
def prefixEnd_1312069 : Nat := 4983230072969 + 3 ^ 40 * 1312069 * 2
def baseEnd_1312069 : Nat := 299432021717392114534849

theorem tailTrace_1312069 : CollatzResearch.WordTrace tailWord_1312069 prefixEnd_1312069 299432021717392114534849 := by
  unfold tailWord_1312069
  simp only [CollatzResearch.WordTrace]
  refine ⟨47855087883605571390107261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31903391922403714260071507 47855087883605571390107261)
  ·
    refine ⟨17945657956352089271290223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47855087883605571390107261 17945657956352089271290223)
    ·
      refine ⟨26918486934528133906935335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17945657956352089271290223 26918486934528133906935335)
      ·
        refine ⟨40377730401792200860403003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26918486934528133906935335 40377730401792200860403003)
        ·
          refine ⟨60566595602688301290604505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40377730401792200860403003 60566595602688301290604505)
          ·
            refine ⟨45424946702016225967953379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60566595602688301290604505 45424946702016225967953379)
            ·
              refine ⟨68137420053024338951930069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45424946702016225967953379 68137420053024338951930069)
              ·
                refine ⟨1596970782492757944185861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68137420053024338951930069 1596970782492757944185861)
                ·
                  refine ⟨299432021717392114534849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596970782492757944185861 299432021717392114534849)
                  ·
                    rfl

theorem cell21_1312069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1312069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312069 prefixEnd_1312069 := by exact prefixLift 1312069
  have htrace : WordTrace (prefixWord ++ tailWord_1312069) baseStart_1312069 baseEnd_1312069 := by
    simpa [prefixWord, tailWord_1312069, baseEnd_1312069] using wordTrace_append hprefix tailTrace_1312069
  have hstable : (prefixWord ++ tailWord_1312069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312069).length < 2 ^ (prefixWord ++ tailWord_1312069).sum := by decide
  have hdescent : baseEnd_1312069 < baseStart_1312069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312083 : List Nat := [1, 1, 1, 2, 1, 1, 7, 7]
def baseStart_1312083 : Nat := 118140960795 + 1312083 * 2 ^ 59
def prefixEnd_1312083 : Nat := 4983230072969 + 3 ^ 40 * 1312083 * 2
def baseEnd_1312083 : Nat := 99811738902710400433829

theorem tailTrace_1312083 : CollatzResearch.WordTrace tailWord_1312083 prefixEnd_1312083 99811738902710400433829 := by
  unfold tailWord_1312083
  simp only [CollatzResearch.WordTrace]
  refine ⟨47855598505554851781116903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31903732337036567854077935 47855598505554851781116903)
  ·
    refine ⟨71783397758332277671675355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47855598505554851781116903 71783397758332277671675355)
    ·
      refine ⟨107675096637498416507513033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71783397758332277671675355 107675096637498416507513033)
      ·
        refine ⟨80756322478123812380634775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107675096637498416507513033 80756322478123812380634775)
        ·
          refine ⟨121134483717185718570952163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80756322478123812380634775 121134483717185718570952163)
          ·
            refine ⟨181701725575778577856428245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121134483717185718570952163 181701725575778577856428245)
            ·
              refine ⟨4258634193182310418510037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 181701725575778577856428245 4258634193182310418510037)
              ·
                refine ⟨99811738902710400433829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4258634193182310418510037 99811738902710400433829)
                ·
                  rfl

theorem cell21_1312083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_1312083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312083 prefixEnd_1312083 := by exact prefixLift 1312083
  have htrace : WordTrace (prefixWord ++ tailWord_1312083) baseStart_1312083 baseEnd_1312083 := by
    simpa [prefixWord, tailWord_1312083, baseEnd_1312083] using wordTrace_append hprefix tailTrace_1312083
  have hstable : (prefixWord ++ tailWord_1312083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312083).length < 2 ^ (prefixWord ++ tailWord_1312083).sum := by decide
  have hdescent : baseEnd_1312083 < baseStart_1312083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312100 : List Nat := [2, 3, 1, 1, 3, 4, 7]
def baseStart_1312100 : Nat := 118140960795 + 1312100 * 2 ^ 59
def prefixEnd_1312100 : Nat := 4983230072969 + 3 ^ 40 * 1312100 * 2
def baseEnd_1312100 : Nat := 33271010704415883279791

theorem tailTrace_1312100 : CollatzResearch.WordTrace tailWord_1312100 prefixEnd_1312100 33271010704415883279791 := by
  unfold tailWord_1312100
  simp only [CollatzResearch.WordTrace]
  refine ⟨23928109273246631842242877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31904145697662175789657169 23928109273246631842242877)
  ·
    refine ⟨8973040977467486940841079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23928109273246631842242877 8973040977467486940841079)
    ·
      refine ⟨13459561466201230411261619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8973040977467486940841079 13459561466201230411261619)
      ·
        refine ⟨20189342199301845616892429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13459561466201230411261619 20189342199301845616892429)
        ·
          refine ⟨7571003324738192106334661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20189342199301845616892429 7571003324738192106334661)
          ·
            refine ⟨1419563123388411019937749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7571003324738192106334661 1419563123388411019937749)
            ·
              refine ⟨33271010704415883279791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1419563123388411019937749 33271010704415883279791)
              ·
                rfl

theorem cell21_1312100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 7].length) (baseStart_1312100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312100 prefixEnd_1312100 := by exact prefixLift 1312100
  have htrace : WordTrace (prefixWord ++ tailWord_1312100) baseStart_1312100 baseEnd_1312100 := by
    simpa [prefixWord, tailWord_1312100, baseEnd_1312100] using wordTrace_append hprefix tailTrace_1312100
  have hstable : (prefixWord ++ tailWord_1312100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312100).length < 2 ^ (prefixWord ++ tailWord_1312100).sum := by decide
  have hdescent : baseEnd_1312100 < baseStart_1312100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312106 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_1312106 : Nat := 118140960795 + 1312106 * 2 ^ 59
def prefixEnd_1312106 : Nat := 4983230072969 + 3 ^ 40 * 1312106 * 2
def baseEnd_1312106 : Nat := 299440465621488272418107

theorem tailTrace_1312106 : CollatzResearch.WordTrace tailWord_1312106 prefixEnd_1312106 299440465621488272418107 := by
  unfold tailWord_1312106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964109346117881677301043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31904291589647684472802781 11964109346117881677301043)
  ·
    refine ⟨17946164019176822515951565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11964109346117881677301043 17946164019176822515951565)
    ·
      refine ⟨6729811507191308443481837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17946164019176822515951565 6729811507191308443481837)
      ·
        refine ⟨2523679315196740666305689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6729811507191308443481837 2523679315196740666305689)
        ·
          refine ⟨1892759486397555499729267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523679315196740666305689 1892759486397555499729267)
          ·
            refine ⟨2839139229596333249593901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892759486397555499729267 2839139229596333249593901)
            ·
              refine ⟨1064677211098624968597713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2839139229596333249593901 1064677211098624968597713)
              ·
                refine ⟨798507908323968726448285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064677211098624968597713 798507908323968726448285)
                ·
                  refine ⟨299440465621488272418107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798507908323968726448285 299440465621488272418107)
                  ·
                    rfl

theorem cell21_1312106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_1312106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312106 prefixEnd_1312106 := by exact prefixLift 1312106
  have htrace : WordTrace (prefixWord ++ tailWord_1312106) baseStart_1312106 baseEnd_1312106 := by
    simpa [prefixWord, tailWord_1312106, baseEnd_1312106] using wordTrace_append hprefix tailTrace_1312106
  have hstable : (prefixWord ++ tailWord_1312106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312106).length < 2 ^ (prefixWord ++ tailWord_1312106).sum := by decide
  have hdescent : baseEnd_1312106 < baseStart_1312106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
