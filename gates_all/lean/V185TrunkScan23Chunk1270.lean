import V185TrunkScan23Chunk1269

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7524108 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7524108 : Nat := 118140960795 + 7524108 * 2 ^ 59
def prefixEnd_7524108 : Nat := 4983230072969 + 3 ^ 40 * 7524108 * 2
def baseEnd_7524108 : Nat := 3863483900339353126547263

theorem tailTrace_7524108 : CollatzResearch.WordTrace tailWord_7524108 prefixEnd_7524108 3863483900339353126547263 := by
  unfold tailWord_7524108
  simp only [CollatzResearch.WordTrace]
  refine ⟨137213381912724603093106489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182951175883632804124141985 137213381912724603093106489)
  ·
    refine ⟨102910036434543452319829867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137213381912724603093106489 102910036434543452319829867)
    ·
      refine ⟨154365054651815178479744801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102910036434543452319829867 154365054651815178479744801)
      ·
        refine ⟨115773790988861383859808601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154365054651815178479744801 115773790988861383859808601)
        ·
          refine ⟨86830343241646037894856451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115773790988861383859808601 86830343241646037894856451)
          ·
            refine ⟨130245514862469056842284677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86830343241646037894856451 130245514862469056842284677)
            ·
              refine ⟨24421034036712948157928377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130245514862469056842284677 24421034036712948157928377)
              ·
                refine ⟨18315775527534711118446283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24421034036712948157928377 18315775527534711118446283)
                ·
                  refine ⟨27473663291302066677669425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18315775527534711118446283 27473663291302066677669425)
                  ·
                    refine ⟨20605247468476550008252069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27473663291302066677669425 20605247468476550008252069)
                    ·
                      refine ⟨3863483900339353126547263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20605247468476550008252069 3863483900339353126547263)
                      ·
                        rfl

theorem cell23_7524108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7524108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524108 prefixEnd_7524108 := by exact prefixLift 7524108
  have htrace : WordTrace (prefixWord ++ tailWord_7524108) baseStart_7524108 baseEnd_7524108 := by
    simpa [prefixWord, tailWord_7524108, baseEnd_7524108] using wordTrace_append hprefix tailTrace_7524108
  have hstable : (prefixWord ++ tailWord_7524108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524108).length < 2 ^ (prefixWord ++ tailWord_7524108).sum := by decide
  have hdescent : baseEnd_7524108 < baseStart_7524108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524122 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_7524122 : Nat := 118140960795 + 7524122 * 2 ^ 59
def prefixEnd_7524122 : Nat := 4983230072969 + 3 ^ 40 * 7524122 * 2
def baseEnd_7524122 : Nat := 1287830363022838690590733

theorem tailTrace_7524122 : CollatzResearch.WordTrace tailWord_7524122 prefixEnd_7524122 1287830363022838690590733 := by
  unfold tailWord_7524122
  simp only [CollatzResearch.WordTrace]
  refine ⟨68606818611849621644305655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182951516298265657718148413 68606818611849621644305655)
  ·
    refine ⟨102910227917774432466458483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68606818611849621644305655 102910227917774432466458483)
    ·
      refine ⟨154365341876661648699687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102910227917774432466458483 154365341876661648699687725)
      ·
        refine ⟨57887003203748118262382897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154365341876661648699687725 57887003203748118262382897)
        ·
          refine ⟨43415252402811088696787173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57887003203748118262382897 43415252402811088696787173)
          ·
            refine ⟨8140359825527079130647595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43415252402811088696787173 8140359825527079130647595)
            ·
              refine ⟨12210539738290618695971393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140359825527079130647595 12210539738290618695971393)
              ·
                refine ⟨9157904803717964021978545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210539738290618695971393 9157904803717964021978545)
                ·
                  refine ⟨6868428602788473016483909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9157904803717964021978545 6868428602788473016483909)
                  ·
                    refine ⟨1287830363022838690590733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868428602788473016483909 1287830363022838690590733)
                    ·
                      rfl

theorem cell23_7524122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_7524122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524122 prefixEnd_7524122 := by exact prefixLift 7524122
  have htrace : WordTrace (prefixWord ++ tailWord_7524122) baseStart_7524122 baseEnd_7524122 := by
    simpa [prefixWord, tailWord_7524122, baseEnd_7524122] using wordTrace_append hprefix tailTrace_7524122
  have hstable : (prefixWord ++ tailWord_7524122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524122).length < 2 ^ (prefixWord ++ tailWord_7524122).sum := by decide
  have hdescent : baseEnd_7524122 < baseStart_7524122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524129 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7524129 : Nat := 118140960795 + 7524129 * 2 ^ 59
def prefixEnd_7524129 : Nat := 4983230072969 + 3 ^ 40 * 7524129 * 2
def baseEnd_7524129 : Nat := 3863494683433097544384667

theorem tailTrace_7524129 : CollatzResearch.WordTrace tailWord_7524129 prefixEnd_7524129 3863494683433097544384667 := by
  unfold tailWord_7524129
  simp only [CollatzResearch.WordTrace]
  refine ⟨274427529758373126772727441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182951686505582084515151627 274427529758373126772727441)
  ·
    refine ⟨205820647318779845079545581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274427529758373126772727441 205820647318779845079545581)
    ·
      refine ⟨77182742744542441904829593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205820647318779845079545581 77182742744542441904829593)
      ·
        refine ⟨57887057058406831428622195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77182742744542441904829593 57887057058406831428622195)
        ·
          refine ⟨86830585587610247142933293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57887057058406831428622195 86830585587610247142933293)
          ·
            refine ⟨32561469595353842678599985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86830585587610247142933293 32561469595353842678599985)
            ·
              refine ⟨24421102196515382008949989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32561469595353842678599985 24421102196515382008949989)
              ·
                refine ⟨4578956661846634126678123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24421102196515382008949989 4578956661846634126678123)
                ·
                  refine ⟨6868434992769951190017185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578956661846634126678123 6868434992769951190017185)
                  ·
                    refine ⟨5151326244577463392512889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868434992769951190017185 5151326244577463392512889)
                    ·
                      refine ⟨3863494683433097544384667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151326244577463392512889 3863494683433097544384667)
                      ·
                        rfl

theorem cell23_7524129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7524129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524129 prefixEnd_7524129 := by exact prefixLift 7524129
  have htrace : WordTrace (prefixWord ++ tailWord_7524129) baseStart_7524129 baseEnd_7524129 := by
    simpa [prefixWord, tailWord_7524129, baseEnd_7524129] using wordTrace_append hprefix tailTrace_7524129
  have hstable : (prefixWord ++ tailWord_7524129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524129).length < 2 ^ (prefixWord ++ tailWord_7524129).sum := by decide
  have hdescent : baseEnd_7524129 < baseStart_7524129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524131 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 9]
def baseStart_7524131 : Nat := 118140960795 + 7524131 * 2 ^ 59
def prefixEnd_7524131 : Nat := 4983230072969 + 3 ^ 40 * 7524131 * 2
def baseEnd_7524131 : Nat := 1287831903464802178853219

theorem tailTrace_7524131 : CollatzResearch.WordTrace tailWord_7524131 prefixEnd_7524131 1287831903464802178853219 := by
  unfold tailWord_7524131
  simp only [CollatzResearch.WordTrace]
  refine ⟨274427602704365881114300247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182951735136243920742866831 274427602704365881114300247)
  ·
    refine ⟨411641404056548821671450371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274427602704365881114300247 411641404056548821671450371)
    ·
      refine ⟨617462106084823232507175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411641404056548821671450371 617462106084823232507175557)
      ·
        refine ⟨115774144890904356095095417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617462106084823232507175557 115774144890904356095095417)
        ·
          refine ⟨86830608668178267071321563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115774144890904356095095417 86830608668178267071321563)
          ·
            refine ⟨130245913002267400606982345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86830608668178267071321563 130245913002267400606982345)
            ·
              refine ⟨97684434751700550455236759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130245913002267400606982345 97684434751700550455236759)
              ·
                refine ⟨146526652127550825682855139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97684434751700550455236759 146526652127550825682855139)
                ·
                  refine ⟨219789978191326238524282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146526652127550825682855139 219789978191326238524282709)
                  ·
                    refine ⟨1287831903464802178853219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219789978191326238524282709 1287831903464802178853219)
                    ·
                      rfl

theorem cell23_7524131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_7524131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524131 prefixEnd_7524131 := by exact prefixLift 7524131
  have htrace : WordTrace (prefixWord ++ tailWord_7524131) baseStart_7524131 baseEnd_7524131 := by
    simpa [prefixWord, tailWord_7524131, baseEnd_7524131] using wordTrace_append hprefix tailTrace_7524131
  have hstable : (prefixWord ++ tailWord_7524131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524131).length < 2 ^ (prefixWord ++ tailWord_7524131).sum := by decide
  have hdescent : baseEnd_7524131 < baseStart_7524131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524145 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_7524145 : Nat := 118140960795 + 7524145 * 2 ^ 59
def prefixEnd_7524145 : Nat := 4983230072969 + 3 ^ 40 * 7524145 * 2
def baseEnd_7524145 : Nat := 3863502899123569481784593

theorem tailTrace_7524145 : CollatzResearch.WordTrace tailWord_7524145 prefixEnd_7524145 3863502899123569481784593 := by
  unfold tailWord_7524145
  simp only [CollatzResearch.WordTrace]
  refine ⟨274428113326315161505309889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182952075550876774336873259 274428113326315161505309889)
  ·
    refine ⟨205821084994736371128982417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274428113326315161505309889 205821084994736371128982417)
    ·
      refine ⟨154365813746052278346736813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205821084994736371128982417 154365813746052278346736813)
      ·
        refine ⟨57887180154769604380026305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154365813746052278346736813 57887180154769604380026305)
        ·
          refine ⟨43415385116077203285019729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57887180154769604380026305 43415385116077203285019729)
          ·
            refine ⟨32561538837057902463764797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43415385116077203285019729 32561538837057902463764797)
            ·
              refine ⟨12210577063896713423911799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32561538837057902463764797 12210577063896713423911799)
              ·
                refine ⟨18315865595845070135867699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210577063896713423911799 18315865595845070135867699)
                ·
                  refine ⟨27473798393767605203801549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18315865595845070135867699 27473798393767605203801549)
                  ·
                    refine ⟨10302674397662851951425581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27473798393767605203801549 10302674397662851951425581)
                    ·
                      refine ⟨3863502899123569481784593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10302674397662851951425581 3863502899123569481784593)
                      ·
                        rfl

theorem cell23_7524145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_7524145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524145 prefixEnd_7524145 := by exact prefixLift 7524145
  have htrace : WordTrace (prefixWord ++ tailWord_7524145) baseStart_7524145 baseEnd_7524145 := by
    simpa [prefixWord, tailWord_7524145, baseEnd_7524145] using wordTrace_append hprefix tailTrace_7524145
  have hstable : (prefixWord ++ tailWord_7524145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524145).length < 2 ^ (prefixWord ++ tailWord_7524145).sum := by decide
  have hdescent : baseEnd_7524145 < baseStart_7524145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524151 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_7524151 : Nat := 118140960795 + 7524151 * 2 ^ 59
def prefixEnd_7524151 : Nat := 4983230072969 + 3 ^ 40 * 7524151 * 2
def baseEnd_7524151 : Nat := 3863505980007496458309565

theorem tailTrace_7524151 : CollatzResearch.WordTrace tailWord_7524151 prefixEnd_7524151 3863505980007496458309565 := by
  unfold tailWord_7524151
  simp only [CollatzResearch.WordTrace]
  refine ⟨274428332164293424530028307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182952221442862283020018871 274428332164293424530028307)
  ·
    refine ⟨411642498246440136795042461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274428332164293424530028307 411642498246440136795042461)
    ·
      refine ⟨154365936842415051298140923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411642498246440136795042461 154365936842415051298140923)
      ·
        refine ⟨231548905263622576947211385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154365936842415051298140923 231548905263622576947211385)
        ·
          refine ⟨173661678947716932710408539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231548905263622576947211385 173661678947716932710408539)
          ·
            refine ⟨260492518421575399065612809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173661678947716932710408539 260492518421575399065612809)
            ·
              refine ⟨195369388816181549299209607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260492518421575399065612809 195369388816181549299209607)
              ·
                refine ⟨293054083224272323948814411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195369388816181549299209607 293054083224272323948814411)
                ·
                  refine ⟨439581124836408485923221617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293054083224272323948814411 439581124836408485923221617)
                  ·
                    refine ⟨329685843627306364442416213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439581124836408485923221617 329685843627306364442416213)
                    ·
                      refine ⟨3863505980007496458309565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 329685843627306364442416213 3863505980007496458309565)
                      ·
                        rfl

theorem cell23_7524151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_7524151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524151 prefixEnd_7524151 := by exact prefixLift 7524151
  have htrace : WordTrace (prefixWord ++ tailWord_7524151) baseStart_7524151 baseEnd_7524151 := by
    simpa [prefixWord, tailWord_7524151, baseEnd_7524151] using wordTrace_append hprefix tailTrace_7524151
  have hstable : (prefixWord ++ tailWord_7524151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524151).length < 2 ^ (prefixWord ++ tailWord_7524151).sum := by decide
  have hdescent : baseEnd_7524151 < baseStart_7524151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524196 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_7524196 : Nat := 118140960795 + 7524196 * 2 ^ 59
def prefixEnd_7524196 : Nat := 4983230072969 + 3 ^ 40 * 7524196 * 2
def baseEnd_7524196 : Nat := 3863529086636948782246859

theorem tailTrace_7524196 : CollatzResearch.WordTrace tailWord_7524196 prefixEnd_7524196 3863529086636948782246859 := by
  unfold tailWord_7524196
  simp only [CollatzResearch.WordTrace]
  refine ⟨137214986724565198607708221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182953315632753598143610961 137214986724565198607708221)
  ·
    refine ⟨51455620021711949477890583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137214986724565198607708221 51455620021711949477890583)
    ·
      refine ⟨77183430032567924216835875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51455620021711949477890583 77183430032567924216835875)
      ·
        refine ⟨115775145048851886325253813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77183430032567924216835875 115775145048851886325253813)
        ·
          refine ⟨10853919848329864342992545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115775145048851886325253813 10853919848329864342992545)
          ·
            refine ⟨8140439886247398257244409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10853919848329864342992545 8140439886247398257244409)
            ·
              refine ⟨6105329914685548692933307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140439886247398257244409 6105329914685548692933307)
              ·
                refine ⟨9157994872028323039399961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105329914685548692933307 9157994872028323039399961)
                ·
                  refine ⟨6868496154021242279549971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9157994872028323039399961 6868496154021242279549971)
                  ·
                    refine ⟨10302744231031863419324957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868496154021242279549971 10302744231031863419324957)
                    ·
                      refine ⟨3863529086636948782246859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10302744231031863419324957 3863529086636948782246859)
                      ·
                        rfl

theorem cell23_7524196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_7524196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524196 prefixEnd_7524196 := by exact prefixLift 7524196
  have htrace : WordTrace (prefixWord ++ tailWord_7524196) baseStart_7524196 baseEnd_7524196 := by
    simpa [prefixWord, tailWord_7524196, baseEnd_7524196] using wordTrace_append hprefix tailTrace_7524196
  have hstable : (prefixWord ++ tailWord_7524196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524196).length < 2 ^ (prefixWord ++ tailWord_7524196).sum := by decide
  have hdescent : baseEnd_7524196 < baseStart_7524196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524206 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7524206 : Nat := 118140960795 + 7524206 * 2 ^ 59
def prefixEnd_7524206 : Nat := 4983230072969 + 3 ^ 40 * 7524206 * 2
def baseEnd_7524206 : Nat := 3863534221443493743121813

theorem tailTrace_7524206 : CollatzResearch.WordTrace tailWord_7524206 prefixEnd_7524206 3863534221443493743121813 := by
  unfold tailWord_7524206
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303792272386771115410059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182953558786062779282186981 34303792272386771115410059)
  ·
    refine ⟨51455688408580156673115089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34303792272386771115410059 51455688408580156673115089)
    ·
      refine ⟨38591766306435117504836317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51455688408580156673115089 38591766306435117504836317)
      ·
        refine ⟨14471912364913169064313619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38591766306435117504836317 14471912364913169064313619)
        ·
          refine ⟨21707868547369753596470429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14471912364913169064313619 21707868547369753596470429)
          ·
            refine ⟨8140450705263657598676411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21707868547369753596470429 8140450705263657598676411)
            ·
              refine ⟨12210676057895486398014617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140450705263657598676411 12210676057895486398014617)
              ·
                refine ⟨9158007043421614798510963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210676057895486398014617 9158007043421614798510963)
                ·
                  refine ⟨13737010565132422197766445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158007043421614798510963 13737010565132422197766445)
                  ·
                    refine ⟨5151378961924658324162417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13737010565132422197766445 5151378961924658324162417)
                    ·
                      refine ⟨3863534221443493743121813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151378961924658324162417 3863534221443493743121813)
                      ·
                        rfl

theorem cell23_7524206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7524206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524206 prefixEnd_7524206 := by exact prefixLift 7524206
  have htrace : WordTrace (prefixWord ++ tailWord_7524206) baseStart_7524206 baseEnd_7524206 := by
    simpa [prefixWord, tailWord_7524206, baseEnd_7524206] using wordTrace_append hprefix tailTrace_7524206
  have hstable : (prefixWord ++ tailWord_7524206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524206).length < 2 ^ (prefixWord ++ tailWord_7524206).sum := by decide
  have hdescent : baseEnd_7524206 < baseStart_7524206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524222 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7524222 : Nat := 118140960795 + 7524222 * 2 ^ 59
def prefixEnd_7524222 : Nat := 4983230072969 + 3 ^ 40 * 7524222 * 2
def baseEnd_7524222 : Nat := 3863542437133965680521739

theorem tailTrace_7524222 : CollatzResearch.WordTrace tailWord_7524222 prefixEnd_7524222 3863542437133965680521739 := by
  unfold tailWord_7524222
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303865218379525456982865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182953947831357469103908613 34303865218379525456982865)
  ·
    refine ⟨25727898913784644092737149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34303865218379525456982865 25727898913784644092737149)
    ·
      refine ⟨9647962092669241534776431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25727898913784644092737149 9647962092669241534776431)
      ·
        refine ⟨14471943139003862302164647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647962092669241534776431 14471943139003862302164647)
        ·
          refine ⟨21707914708505793453246971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14471943139003862302164647 21707914708505793453246971)
          ·
            refine ⟨32561872062758690179870457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21707914708505793453246971 32561872062758690179870457)
            ·
              refine ⟨24421404047069017634902843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32561872062758690179870457 24421404047069017634902843)
              ·
                refine ⟨36632106070603526452354265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24421404047069017634902843 36632106070603526452354265)
                ·
                  refine ⟨27474079552952644839265699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36632106070603526452354265 27474079552952644839265699)
                  ·
                    refine ⟨41211119329428967258898549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27474079552952644839265699 41211119329428967258898549)
                    ·
                      refine ⟨3863542437133965680521739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41211119329428967258898549 3863542437133965680521739)
                      ·
                        rfl

theorem cell23_7524222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7524222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524222 prefixEnd_7524222 := by exact prefixLift 7524222
  have htrace : WordTrace (prefixWord ++ tailWord_7524222) baseStart_7524222 baseEnd_7524222 := by
    simpa [prefixWord, tailWord_7524222, baseEnd_7524222] using wordTrace_append hprefix tailTrace_7524222
  have hstable : (prefixWord ++ tailWord_7524222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524222).length < 2 ^ (prefixWord ++ tailWord_7524222).sum := by decide
  have hdescent : baseEnd_7524222 < baseStart_7524222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524245 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_7524245 : Nat := 118140960795 + 7524245 * 2 ^ 59
def prefixEnd_7524245 : Nat := 4983230072969 + 3 ^ 40 * 7524245 * 2
def baseEnd_7524245 : Nat := 3863554247189019090534133

theorem tailTrace_7524245 : CollatzResearch.WordTrace tailWord_7524245 prefixEnd_7524245 3863554247189019090534133 := by
  unfold tailWord_7524245
  simp only [CollatzResearch.WordTrace]
  refine ⟨274431760625952878583950189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182954507083968585722633459 274431760625952878583950189)
  ·
    refine ⟨102911910234732329468981321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274431760625952878583950189 102911910234732329468981321)
    ·
      refine ⟨77183932676049247101735991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102911910234732329468981321 77183932676049247101735991)
      ·
        refine ⟨115775899014073870652603987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77183932676049247101735991 115775899014073870652603987)
        ·
          refine ⟨173663848521110805978905981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115775899014073870652603987 173663848521110805978905981)
          ·
            refine ⟨65123943195416552242089743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173663848521110805978905981 65123943195416552242089743)
            ·
              refine ⟨97685914793124828363134615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65123943195416552242089743 97685914793124828363134615)
              ·
                refine ⟨146528872189687242544701923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97685914793124828363134615 146528872189687242544701923)
                ·
                  refine ⟨219793308284530863817052885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146528872189687242544701923 219793308284530863817052885)
                  ·
                    refine ⟨5151405662918692120712177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 219793308284530863817052885 5151405662918692120712177)
                    ·
                      refine ⟨3863554247189019090534133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151405662918692120712177 3863554247189019090534133)
                      ·
                        rfl

theorem cell23_7524245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_7524245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524245 prefixEnd_7524245 := by exact prefixLift 7524245
  have htrace : WordTrace (prefixWord ++ tailWord_7524245) baseStart_7524245 baseEnd_7524245 := by
    simpa [prefixWord, tailWord_7524245, baseEnd_7524245] using wordTrace_append hprefix tailTrace_7524245
  have hstable : (prefixWord ++ tailWord_7524245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524245).length < 2 ^ (prefixWord ++ tailWord_7524245).sum := by decide
  have hdescent : baseEnd_7524245 < baseStart_7524245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524252 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7524252 : Nat := 118140960795 + 7524252 * 2 ^ 59
def prefixEnd_7524252 : Nat := 4983230072969 + 3 ^ 40 * 7524252 * 2
def baseEnd_7524252 : Nat := 3863557841553600563146601

theorem tailTrace_7524252 : CollatzResearch.WordTrace tailWord_7524252 prefixEnd_7524252 3863557841553600563146601 := by
  unfold tailWord_7524252
  simp only [CollatzResearch.WordTrace]
  refine ⟨137216007968463759389727505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182954677291285012519636673 137216007968463759389727505)
  ·
    refine ⟨102912005976347819542295629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137216007968463759389727505 102912005976347819542295629)
    ·
      refine ⟨38592002241130432328360861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102912005976347819542295629 38592002241130432328360861)
      ·
        refine ⟨14472000840423912123135323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38592002241130432328360861 14472000840423912123135323)
        ·
          refine ⟨21708001260635868184702985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14472000840423912123135323 21708001260635868184702985)
          ·
            refine ⟨16281000945476901138527239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21708001260635868184702985 16281000945476901138527239)
            ·
              refine ⟨24421501418215351707790859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16281000945476901138527239 24421501418215351707790859)
              ·
                refine ⟨36632252127323027561686289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24421501418215351707790859 36632252127323027561686289)
                ·
                  refine ⟨27474189095492270671264717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36632252127323027561686289 27474189095492270671264717)
                  ·
                    refine ⟨10302820910809601501724269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27474189095492270671264717 10302820910809601501724269)
                    ·
                      refine ⟨3863557841553600563146601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10302820910809601501724269 3863557841553600563146601)
                      ·
                        rfl

theorem cell23_7524252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7524252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524252 prefixEnd_7524252 := by exact prefixLift 7524252
  have htrace : WordTrace (prefixWord ++ tailWord_7524252) baseStart_7524252 baseEnd_7524252 := by
    simpa [prefixWord, tailWord_7524252, baseEnd_7524252] using wordTrace_append hprefix tailTrace_7524252
  have hstable : (prefixWord ++ tailWord_7524252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524252).length < 2 ^ (prefixWord ++ tailWord_7524252).sum := by decide
  have hdescent : baseEnd_7524252 < baseStart_7524252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524275 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 6, 2]
def baseStart_7524275 : Nat := 118140960795 + 7524275 * 2 ^ 59
def prefixEnd_7524275 : Nat := 4983230072969 + 3 ^ 40 * 7524275 * 2
def baseEnd_7524275 : Nat := 3863569651608653973158995

theorem tailTrace_7524275 : CollatzResearch.WordTrace tailWord_7524275 prefixEnd_7524275 3863569651608653973158995 := by
  unfold tailWord_7524275
  simp only [CollatzResearch.WordTrace]
  refine ⟨274432854815844193707542279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182955236543896129138361519 274432854815844193707542279)
  ·
    refine ⟨411649282223766290561313419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274432854815844193707542279 411649282223766290561313419)
    ·
      refine ⟨617473923335649435841970129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411649282223766290561313419 617473923335649435841970129)
      ·
        refine ⟨463105442501737076881477597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617473923335649435841970129 463105442501737076881477597)
        ·
          refine ⟨173664540938151403830554099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463105442501737076881477597 173664540938151403830554099)
          ·
            refine ⟨260496811407227105745831149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173664540938151403830554099 260496811407227105745831149)
            ·
              refine ⟨97686304277710164654686681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260496811407227105745831149 97686304277710164654686681)
              ·
                refine ⟨73264728208282623491015011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97686304277710164654686681 73264728208282623491015011)
                ·
                  refine ⟨109897092312423935236522517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73264728208282623491015011 109897092312423935236522517)
                  ·
                    refine ⟨5151426202144871964211993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109897092312423935236522517 5151426202144871964211993)
                    ·
                      refine ⟨3863569651608653973158995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151426202144871964211993 3863569651608653973158995)
                      ·
                        rfl

theorem cell23_7524275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6, 2].length) (baseStart_7524275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524275 prefixEnd_7524275 := by exact prefixLift 7524275
  have htrace : WordTrace (prefixWord ++ tailWord_7524275) baseStart_7524275 baseEnd_7524275 := by
    simpa [prefixWord, tailWord_7524275, baseEnd_7524275] using wordTrace_append hprefix tailTrace_7524275
  have hstable : (prefixWord ++ tailWord_7524275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524275).length < 2 ^ (prefixWord ++ tailWord_7524275).sum := by decide
  have hdescent : baseEnd_7524275 < baseStart_7524275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524276 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7524276 : Nat := 118140960795 + 7524276 * 2 ^ 59
def prefixEnd_7524276 : Nat := 4983230072969 + 3 ^ 40 * 7524276 * 2
def baseEnd_7524276 : Nat := 429285573898812052138499

theorem tailTrace_7524276 : CollatzResearch.WordTrace tailWord_7524276 prefixEnd_7524276 429285573898812052138499 := by
  unfold tailWord_7524276
  simp only [CollatzResearch.WordTrace]
  refine ⟨137216445644420285439164341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182955260859227047252219121 137216445644420285439164341)
  ·
    refine ⟨12864041779164401759921657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137216445644420285439164341 12864041779164401759921657)
    ·
      refine ⟨9648031334373301319941243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12864041779164401759921657 9648031334373301319941243)
      ·
        refine ⟨14472047001559951979911865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9648031334373301319941243 14472047001559951979911865)
        ·
          refine ⟨10854035251169963984933899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14472047001559951979911865 10854035251169963984933899)
          ·
            refine ⟨16281052876754945977400849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10854035251169963984933899 16281052876754945977400849)
            ·
              refine ⟨12210789657566209483050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16281052876754945977400849 12210789657566209483050637)
              ·
                refine ⟨4579046121587328556143989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12210789657566209483050637 4579046121587328556143989)
                ·
                  refine ⟨429285573898812052138499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4579046121587328556143989 429285573898812052138499)
                  ·
                    rfl

theorem cell23_7524276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7524276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524276 prefixEnd_7524276 := by exact prefixLift 7524276
  have htrace : WordTrace (prefixWord ++ tailWord_7524276) baseStart_7524276 baseEnd_7524276 := by
    simpa [prefixWord, tailWord_7524276, baseEnd_7524276] using wordTrace_append hprefix tailTrace_7524276
  have hstable : (prefixWord ++ tailWord_7524276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524276).length < 2 ^ (prefixWord ++ tailWord_7524276).sum := by decide
  have hdescent : baseEnd_7524276 < baseStart_7524276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524288 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_7524288 : Nat := 118140960795 + 7524288 * 2 ^ 59
def prefixEnd_7524288 : Nat := 4983230072969 + 3 ^ 40 * 7524288 * 2
def baseEnd_7524288 : Nat := 3863576326857162422296435

theorem tailTrace_7524288 : CollatzResearch.WordTrace tailWord_7524288 prefixEnd_7524288 3863576326857162422296435 := by
  unfold tailWord_7524288
  simp only [CollatzResearch.WordTrace]
  refine ⟨137216664482398548463882759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182955552643198064618510345 137216664482398548463882759)
  ·
    refine ⟨205824996723597822695824139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137216664482398548463882759 205824996723597822695824139)
    ·
      refine ⟨308737495085396734043736209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205824996723597822695824139 308737495085396734043736209)
      ·
        refine ⟨231553121314047550532802157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308737495085396734043736209 231553121314047550532802157)
        ·
          refine ⟨86832420492767831449800809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231553121314047550532802157 86832420492767831449800809)
          ·
            refine ⟨65124315369575873587350607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86832420492767831449800809 65124315369575873587350607)
            ·
              refine ⟨97686473054363810381025911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65124315369575873587350607 97686473054363810381025911)
              ·
                refine ⟨146529709581545715571538867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97686473054363810381025911 146529709581545715571538867)
                ·
                  refine ⟨219794564372318573357308301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146529709581545715571538867 219794564372318573357308301)
                  ·
                    refine ⟨82422961639619465008990613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219794564372318573357308301 82422961639619465008990613)
                    ·
                      refine ⟨3863576326857162422296435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82422961639619465008990613 3863576326857162422296435)
                      ·
                        rfl

theorem cell23_7524288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_7524288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524288 prefixEnd_7524288 := by exact prefixLift 7524288
  have htrace : WordTrace (prefixWord ++ tailWord_7524288) baseStart_7524288 baseEnd_7524288 := by
    simpa [prefixWord, tailWord_7524288, baseEnd_7524288] using wordTrace_append hprefix tailTrace_7524288
  have hstable : (prefixWord ++ tailWord_7524288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524288).length < 2 ^ (prefixWord ++ tailWord_7524288).sum := by decide
  have hdescent : baseEnd_7524288 < baseStart_7524288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524295 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_7524295 : Nat := 118140960795 + 7524295 * 2 ^ 59
def prefixEnd_7524295 : Nat := 4983230072969 + 3 ^ 40 * 7524295 * 2
def baseEnd_7524295 : Nat := 3863579921221743894908903

theorem tailTrace_7524295 : CollatzResearch.WordTrace tailWord_7524295 prefixEnd_7524295 3863579921221743894908903 := by
  unfold tailWord_7524295
  simp only [CollatzResearch.WordTrace]
  refine ⟨274433584275771737123270339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182955722850514491415513559 274433584275771737123270339)
  ·
    refine ⟨411650376413657605684905509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274433584275771737123270339 411650376413657605684905509)
    ·
      refine ⟨77184445577560801065919783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411650376413657605684905509 77184445577560801065919783)
      ·
        refine ⟨115776668366341201598879675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77184445577560801065919783 115776668366341201598879675)
        ·
          refine ⟨173665002549511802398319513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115776668366341201598879675 173665002549511802398319513)
          ·
            refine ⟨130248751912133851798739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173665002549511802398319513 130248751912133851798739635)
            ·
              refine ⟨195373127868200777698109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130248751912133851798739635 195373127868200777698109453)
              ·
                refine ⟨73264922950575291636791045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195373127868200777698109453 73264922950575291636791045)
                ·
                  refine ⟨13737173053232867181898321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73264922950575291636791045 13737173053232867181898321)
                  ·
                    refine ⟨10302879789924650386423741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13737173053232867181898321 10302879789924650386423741)
                    ·
                      refine ⟨3863579921221743894908903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10302879789924650386423741 3863579921221743894908903)
                      ·
                        rfl

theorem cell23_7524295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_7524295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524295 prefixEnd_7524295 := by exact prefixLift 7524295
  have htrace : WordTrace (prefixWord ++ tailWord_7524295) baseStart_7524295 baseEnd_7524295 := by
    simpa [prefixWord, tailWord_7524295, baseEnd_7524295] using wordTrace_append hprefix tailTrace_7524295
  have hstable : (prefixWord ++ tailWord_7524295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524295).length < 2 ^ (prefixWord ++ tailWord_7524295).sum := by decide
  have hdescent : baseEnd_7524295 < baseStart_7524295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524302 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_7524302 : Nat := 118140960795 + 7524302 * 2 ^ 59
def prefixEnd_7524302 : Nat := 4983230072969 + 3 ^ 40 * 7524302 * 2
def baseEnd_7524302 : Nat := 1287861171862108455840457

theorem tailTrace_7524302 : CollatzResearch.WordTrace tailWord_7524302 prefixEnd_7524302 1287861171862108455840457 := by
  unfold tailWord_7524302
  simp only [CollatzResearch.WordTrace]
  refine ⟨34304229948343297164846895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182955893057830918212516773 34304229948343297164846895)
  ·
    refine ⟨51456344922514945747270343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34304229948343297164846895 51456344922514945747270343)
    ·
      refine ⟨77184517383772418620905515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51456344922514945747270343 77184517383772418620905515)
      ·
        refine ⟨115776776075658627931358273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77184517383772418620905515 115776776075658627931358273)
        ·
          refine ⟨86832582056743970948518705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115776776075658627931358273 86832582056743970948518705)
          ·
            refine ⟨65124436542557978211389029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86832582056743970948518705 65124436542557978211389029)
            ·
              refine ⟨12210831851729620914635443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65124436542557978211389029 12210831851729620914635443)
              ·
                refine ⟨18316247777594431371953165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210831851729620914635443 18316247777594431371953165)
                ·
                  refine ⟨6868592916597911764482437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18316247777594431371953165 6868592916597911764482437)
                  ·
                    refine ⟨1287861171862108455840457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868592916597911764482437 1287861171862108455840457)
                    ·
                      rfl

theorem cell23_7524302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_7524302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524302 prefixEnd_7524302 := by exact prefixLift 7524302
  have htrace : WordTrace (prefixWord ++ tailWord_7524302) baseStart_7524302 baseEnd_7524302 := by
    simpa [prefixWord, tailWord_7524302, baseEnd_7524302] using wordTrace_append hprefix tailTrace_7524302
  have hstable : (prefixWord ++ tailWord_7524302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524302).length < 2 ^ (prefixWord ++ tailWord_7524302).sum := by decide
  have hdescent : baseEnd_7524302 < baseStart_7524302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524359 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7524359 : Nat := 118140960795 + 7524359 * 2 ^ 59
def prefixEnd_7524359 : Nat := 4983230072969 + 3 ^ 40 * 7524359 * 2
def baseEnd_7524359 : Nat := 3863612783983631644508609

theorem tailTrace_7524359 : CollatzResearch.WordTrace tailWord_7524359 prefixEnd_7524359 3863612783983631644508609 := by
  unfold tailWord_7524359
  simp only [CollatzResearch.WordTrace]
  refine ⟨274435918547539876053600131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182957279031693250702400087 274435918547539876053600131)
  ·
    refine ⟨411653877821309814080400197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274435918547539876053600131 411653877821309814080400197)
    ·
      refine ⟨77185102091495590140075037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411653877821309814080400197 77185102091495590140075037)
      ·
        refine ⟨28944413284310846302528139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77185102091495590140075037 28944413284310846302528139)
        ·
          refine ⟨43416619926466269453792209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28944413284310846302528139 43416619926466269453792209)
          ·
            refine ⟨32562464944849702090344157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43416619926466269453792209 32562464944849702090344157)
            ·
              refine ⟨12210924354318638283879059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32562464944849702090344157 12210924354318638283879059)
              ·
                refine ⟨18316386531477957425818589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210924354318638283879059 18316386531477957425818589)
                ·
                  refine ⟨6868644949304234034681971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18316386531477957425818589 6868644949304234034681971)
                  ·
                    refine ⟨10302967423956351052022957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868644949304234034681971 10302967423956351052022957)
                    ·
                      refine ⟨3863612783983631644508609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10302967423956351052022957 3863612783983631644508609)
                      ·
                        rfl

theorem cell23_7524359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7524359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524359 prefixEnd_7524359 := by exact prefixLift 7524359
  have htrace : WordTrace (prefixWord ++ tailWord_7524359) baseStart_7524359 baseEnd_7524359 := by
    simpa [prefixWord, tailWord_7524359, baseEnd_7524359] using wordTrace_append hprefix tailTrace_7524359
  have hstable : (prefixWord ++ tailWord_7524359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524359).length < 2 ^ (prefixWord ++ tailWord_7524359).sum := by decide
  have hdescent : baseEnd_7524359 < baseStart_7524359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524402 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_7524402 : Nat := 118140960795 + 7524402 * 2 ^ 59
def prefixEnd_7524402 : Nat := 4983230072969 + 3 ^ 40 * 7524402 * 2
def baseEnd_7524402 : Nat := 3863634863651774976270911

theorem tailTrace_7524402 : CollatzResearch.WordTrace tailWord_7524402 prefixEnd_7524402 3863634863651774976270911 := by
  unfold tailWord_7524402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68609371721596023599353865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182958324590922729598276973 68609371721596023599353865)
  ·
    refine ⟨51457028791197017699515399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68609371721596023599353865 51457028791197017699515399)
    ·
      refine ⟨77185543186795526549273099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51457028791197017699515399 77185543186795526549273099)
      ·
        refine ⟨115778314780193289823909649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77185543186795526549273099 115778314780193289823909649)
        ·
          refine ⟨86833736085144967367932237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115778314780193289823909649 86833736085144967367932237)
          ·
            refine ⟨32562651031929362762974589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86833736085144967367932237 32562651031929362762974589)
            ·
              refine ⟨12210994136973511036115471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32562651031929362762974589 12210994136973511036115471)
              ·
                refine ⟨18316491205460266554173207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12210994136973511036115471 18316491205460266554173207)
                ·
                  refine ⟨27474736808190399831259811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18316491205460266554173207 27474736808190399831259811)
                  ·
                    refine ⟨41212105212285599746889717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27474736808190399831259811 41212105212285599746889717)
                    ·
                      refine ⟨3863634863651774976270911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41212105212285599746889717 3863634863651774976270911)
                      ·
                        rfl

theorem cell23_7524402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_7524402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524402 prefixEnd_7524402 := by exact prefixLift 7524402
  have htrace : WordTrace (prefixWord ++ tailWord_7524402) baseStart_7524402 baseEnd_7524402 := by
    simpa [prefixWord, tailWord_7524402, baseEnd_7524402] using wordTrace_append hprefix tailTrace_7524402
  have hstable : (prefixWord ++ tailWord_7524402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524402).length < 2 ^ (prefixWord ++ tailWord_7524402).sum := by decide
  have hdescent : baseEnd_7524402 < baseStart_7524402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524429 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_7524429 : Nat := 118140960795 + 7524429 * 2 ^ 59
def prefixEnd_7524429 : Nat := 4983230072969 + 3 ^ 40 * 7524429 * 2
def baseEnd_7524429 : Nat := 3863648727629446370633287

theorem tailTrace_7524429 : CollatzResearch.WordTrace tailWord_7524429 prefixEnd_7524429 3863648727629446370633287 := by
  unfold tailWord_7524429
  simp only [CollatzResearch.WordTrace]
  refine ⟨274438471657286278008648341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182958981104857518672432227 274438471657286278008648341)
  ·
    refine ⟨12864303358935294281655391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274438471657286278008648341 12864303358935294281655391)
    ·
      refine ⟨19296455038402941422483087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12864303358935294281655391 19296455038402941422483087)
      ·
        refine ⟨28944682557604412133724631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19296455038402941422483087 28944682557604412133724631)
        ·
          refine ⟨43417023836406618200586947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28944682557604412133724631 43417023836406618200586947)
          ·
            refine ⟨65125535754609927300880421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43417023836406618200586947 65125535754609927300880421)
            ·
              refine ⟨12211037953989361368915079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65125535754609927300880421 12211037953989361368915079)
              ·
                refine ⟨18316556930984042053372619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12211037953989361368915079 18316556930984042053372619)
                ·
                  refine ⟨27474835396476063080058929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18316556930984042053372619 27474835396476063080058929)
                  ·
                    refine ⟨20606126547357047310044197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27474835396476063080058929 20606126547357047310044197)
                    ·
                      refine ⟨3863648727629446370633287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20606126547357047310044197 3863648727629446370633287)
                      ·
                        rfl

theorem cell23_7524429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_7524429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524429 prefixEnd_7524429 := by exact prefixLift 7524429
  have htrace : WordTrace (prefixWord ++ tailWord_7524429) baseStart_7524429 baseEnd_7524429 := by
    simpa [prefixWord, tailWord_7524429, baseEnd_7524429] using wordTrace_append hprefix tailTrace_7524429
  have hstable : (prefixWord ++ tailWord_7524429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524429).length < 2 ^ (prefixWord ++ tailWord_7524429).sum := by decide
  have hdescent : baseEnd_7524429 < baseStart_7524429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524432 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3]
def baseStart_7524432 : Nat := 118140960795 + 7524432 * 2 ^ 59
def prefixEnd_7524432 : Nat := 4983230072969 + 3 ^ 40 * 7524432 * 2
def baseEnd_7524432 : Nat := 3863650268071409858895773

theorem tailTrace_7524432 : CollatzResearch.WordTrace tailWord_7524432 prefixEnd_7524432 3863650268071409858895773 := by
  unfold tailWord_7524432
  simp only [CollatzResearch.WordTrace]
  refine ⟨137219290538137704760503775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182959054050850273014005033 137219290538137704760503775)
  ·
    refine ⟨205828935807206557140755663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137219290538137704760503775 205828935807206557140755663)
    ·
      refine ⟨308743403710809835711133495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205828935807206557140755663 308743403710809835711133495)
      ·
        refine ⟨463115105566214753566700243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308743403710809835711133495 463115105566214753566700243)
        ·
          refine ⟨694672658349322130350050365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463115105566214753566700243 694672658349322130350050365)
          ·
            refine ⟨260502246880995798881268887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694672658349322130350050365 260502246880995798881268887)
            ·
              refine ⟨390753370321493698321903331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260502246880995798881268887 390753370321493698321903331)
              ·
                refine ⟨586130055482240547482854997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390753370321493698321903331 586130055482240547482854997)
                ·
                  refine ⟨6868711587682506415814707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 586130055482240547482854997 6868711587682506415814707)
                  ·
                    refine ⟨10303067381523759623722061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868711587682506415814707 10303067381523759623722061)
                    ·
                      refine ⟨3863650268071409858895773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303067381523759623722061 3863650268071409858895773)
                      ·
                        rfl

theorem cell23_7524432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_7524432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524432 prefixEnd_7524432 := by exact prefixLift 7524432
  have htrace : WordTrace (prefixWord ++ tailWord_7524432) baseStart_7524432 baseEnd_7524432 := by
    simpa [prefixWord, tailWord_7524432, baseEnd_7524432] using wordTrace_append hprefix tailTrace_7524432
  have hstable : (prefixWord ++ tailWord_7524432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524432).length < 2 ^ (prefixWord ++ tailWord_7524432).sum := by decide
  have hdescent : baseEnd_7524432 < baseStart_7524432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524450 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7524450 : Nat := 118140960795 + 7524450 * 2 ^ 59
def prefixEnd_7524450 : Nat := 4983230072969 + 3 ^ 40 * 7524450 * 2
def baseEnd_7524450 : Nat := 3863659510723190788470691

theorem tailTrace_7524450 : CollatzResearch.WordTrace tailWord_7524450 prefixEnd_7524450 3863659510723190788470691 := by
  unfold tailWord_7524450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68609809397552549648790701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182959491726806799063441869 68609809397552549648790701)
  ·
    refine ⟨25728678524082206118296513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68609809397552549648790701 25728678524082206118296513)
    ·
      refine ⟨19296508893061654588722385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25728678524082206118296513 19296508893061654588722385)
      ·
        refine ⟨14472381669796240941541789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19296508893061654588722385 14472381669796240941541789)
        ·
          refine ⟨5427143126173590353078171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14472381669796240941541789 5427143126173590353078171)
          ·
            refine ⟨8140714689260385529617257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427143126173590353078171 8140714689260385529617257)
            ·
              refine ⟨6105536016945289147212943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140714689260385529617257 6105536016945289147212943)
              ·
                refine ⟨9158304025417933720819415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105536016945289147212943 9158304025417933720819415)
                ·
                  refine ⟨13737456038126900581229123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158304025417933720819415 13737456038126900581229123)
                  ·
                    refine ⟨20606184057190350871843685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13737456038126900581229123 20606184057190350871843685)
                    ·
                      refine ⟨3863659510723190788470691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20606184057190350871843685 3863659510723190788470691)
                      ·
                        rfl

theorem cell23_7524450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7524450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524450 prefixEnd_7524450 := by exact prefixLift 7524450
  have htrace : WordTrace (prefixWord ++ tailWord_7524450) baseStart_7524450 baseEnd_7524450 := by
    simpa [prefixWord, tailWord_7524450, baseEnd_7524450] using wordTrace_append hprefix tailTrace_7524450
  have hstable : (prefixWord ++ tailWord_7524450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524450).length < 2 ^ (prefixWord ++ tailWord_7524450).sum := by decide
  have hdescent : baseEnd_7524450 < baseStart_7524450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524465 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_7524465 : Nat := 118140960795 + 7524465 * 2 ^ 59
def prefixEnd_7524465 : Nat := 4983230072969 + 3 ^ 40 * 7524465 * 2
def baseEnd_7524465 : Nat := 1287889070977669409927707

theorem tailTrace_7524465 : CollatzResearch.WordTrace tailWord_7524465 prefixEnd_7524465 1287889070977669409927707 := by
  unfold tailWord_7524465
  simp only [CollatzResearch.WordTrace]
  refine ⟨274439784685155856156958849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182959856456770570771305899 274439784685155856156958849)
  ·
    refine ⟨205829838513866892117719137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274439784685155856156958849 205829838513866892117719137)
    ·
      refine ⟨154372378885400169088289353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205829838513866892117719137 154372378885400169088289353)
      ·
        refine ⟨115779284164050126816217015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154372378885400169088289353 115779284164050126816217015)
        ·
          refine ⟨173668926246075190224325523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115779284164050126816217015 173668926246075190224325523)
          ·
            refine ⟨260503389369112785336488285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173668926246075190224325523 260503389369112785336488285)
            ·
              refine ⟨97688771013417294501183107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260503389369112785336488285 97688771013417294501183107)
              ·
                refine ⟨146533156520125941751774661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97688771013417294501183107 146533156520125941751774661)
                ·
                  refine ⟨27474966847523614078457749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146533156520125941751774661 27474966847523614078457749)
                  ·
                    refine ⟨1287889070977669409927707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27474966847523614078457749 1287889070977669409927707)
                    ·
                      rfl

theorem cell23_7524465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_7524465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524465 prefixEnd_7524465 := by exact prefixLift 7524465
  have htrace : WordTrace (prefixWord ++ tailWord_7524465) baseStart_7524465 baseEnd_7524465 := by
    simpa [prefixWord, tailWord_7524465, baseEnd_7524465] using wordTrace_append hprefix tailTrace_7524465
  have hstable : (prefixWord ++ tailWord_7524465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524465).length < 2 ^ (prefixWord ++ tailWord_7524465).sum := by decide
  have hdescent : baseEnd_7524465 < baseStart_7524465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524466 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_7524466 : Nat := 118140960795 + 7524466 * 2 ^ 59
def prefixEnd_7524466 : Nat := 4983230072969 + 3 ^ 40 * 7524466 * 2
def baseEnd_7524466 : Nat := 3863667726413662725870617

theorem tailTrace_7524466 : CollatzResearch.WordTrace tailWord_7524466 prefixEnd_7524466 3863667726413662725870617 := by
  unfold tailWord_7524466
  simp only [CollatzResearch.WordTrace]
  refine ⟨68609955289538058331936313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182959880772101488885163501 68609955289538058331936313)
  ·
    refine ⟨51457466467153543748952235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68609955289538058331936313 51457466467153543748952235)
    ·
      refine ⟨77186199700730315623428353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51457466467153543748952235 77186199700730315623428353)
      ·
        refine ⟨57889649775547736717571265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77186199700730315623428353 57889649775547736717571265)
        ·
          refine ⟨43417237331660802538178449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57889649775547736717571265 43417237331660802538178449)
          ·
            refine ⟨32562927998745601903633837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43417237331660802538178449 32562927998745601903633837)
            ·
              refine ⟨12211097999529600713862689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32562927998745601903633837 12211097999529600713862689)
              ·
                refine ⟨9158323499647200535397017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12211097999529600713862689 9158323499647200535397017)
                ·
                  refine ⟨6868742624735400401547763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9158323499647200535397017 6868742624735400401547763)
                  ·
                    refine ⟨10303113937103100602321645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868742624735400401547763 10303113937103100602321645)
                    ·
                      refine ⟨3863667726413662725870617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303113937103100602321645 3863667726413662725870617)
                      ·
                        rfl

theorem cell23_7524466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_7524466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524466 prefixEnd_7524466 := by exact prefixLift 7524466
  have htrace : WordTrace (prefixWord ++ tailWord_7524466) baseStart_7524466 baseEnd_7524466 := by
    simpa [prefixWord, tailWord_7524466, baseEnd_7524466] using wordTrace_append hprefix tailTrace_7524466
  have hstable : (prefixWord ++ tailWord_7524466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524466).length < 2 ^ (prefixWord ++ tailWord_7524466).sum := by decide
  have hdescent : baseEnd_7524466 < baseStart_7524466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524475 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_7524475 : Nat := 118140960795 + 7524475 * 2 ^ 59
def prefixEnd_7524475 : Nat := 4983230072969 + 3 ^ 40 * 7524475 * 2
def baseEnd_7524475 : Nat := 3863672347739553190658075

theorem tailTrace_7524475 : CollatzResearch.WordTrace tailWord_7524475 prefixEnd_7524475 3863672347739553190658075 := by
  unfold tailWord_7524475
  simp only [CollatzResearch.WordTrace]
  refine ⟨274440149415119627864822879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182960099610079751909881919 274440149415119627864822879)
  ·
    refine ⟨411660224122679441797234319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274440149415119627864822879 411660224122679441797234319)
    ·
      refine ⟨617490336184019162695851479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411660224122679441797234319 617490336184019162695851479)
      ·
        refine ⟨926235504276028744043777219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617490336184019162695851479 926235504276028744043777219)
        ·
          refine ⟨1389353256414043116065665829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926235504276028744043777219 1389353256414043116065665829)
          ·
            refine ⟨260503735577633084262312343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1389353256414043116065665829 260503735577633084262312343)
            ·
              refine ⟨390755603366449626393468515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260503735577633084262312343 390755603366449626393468515)
              ·
                refine ⟨586133405049674439590202773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390755603366449626393468515 586133405049674439590202773)
                ·
                  refine ⟨27475003361703489355790755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 586133405049674439590202773 27475003361703489355790755)
                  ·
                    refine ⟨41212505042555234033686133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27475003361703489355790755 41212505042555234033686133)
                    ·
                      refine ⟨3863672347739553190658075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41212505042555234033686133 3863672347739553190658075)
                      ·
                        rfl

theorem cell23_7524475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_7524475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524475 prefixEnd_7524475 := by exact prefixLift 7524475
  have htrace : WordTrace (prefixWord ++ tailWord_7524475) baseStart_7524475 baseEnd_7524475 := by
    simpa [prefixWord, tailWord_7524475, baseEnd_7524475] using wordTrace_append hprefix tailTrace_7524475
  have hstable : (prefixWord ++ tailWord_7524475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524475).length < 2 ^ (prefixWord ++ tailWord_7524475).sum := by decide
  have hdescent : baseEnd_7524475 < baseStart_7524475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524515 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_7524515 : Nat := 118140960795 + 7524515 * 2 ^ 59
def prefixEnd_7524515 : Nat := 4983230072969 + 3 ^ 40 * 7524515 * 2
def baseEnd_7524515 : Nat := 3863692886965733034157891

theorem tailTrace_7524515 : CollatzResearch.WordTrace tailWord_7524515 prefixEnd_7524515 3863692886965733034157891 := by
  unfold tailWord_7524515
  simp only [CollatzResearch.WordTrace]
  refine ⟨274441608334974714696278999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182961072223316476464185999 274441608334974714696278999)
  ·
    refine ⟨411662412502462072044418499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274441608334974714696278999 411662412502462072044418499)
    ·
      refine ⟨617493618753693108066627749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411662412502462072044418499 617493618753693108066627749)
      ·
        refine ⟨115780053516317457762492703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617493618753693108066627749 115780053516317457762492703)
        ·
          refine ⟨173670080274476186643739055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115780053516317457762492703 173670080274476186643739055)
          ·
            refine ⟨260505120411714279965608583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173670080274476186643739055 260505120411714279965608583)
            ·
              refine ⟨390757680617571419948412875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260505120411714279965608583 390757680617571419948412875)
              ·
                refine ⟨586136520926357129922619313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390757680617571419948412875 586136520926357129922619313)
                ·
                  refine ⟨439602390694767847441964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586136520926357129922619313 439602390694767847441964485)
                  ·
                    refine ⟨82425448255268971395368341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439602390694767847441964485 82425448255268971395368341)
                    ·
                      refine ⟨3863692886965733034157891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82425448255268971395368341 3863692886965733034157891)
                      ·
                        rfl

theorem cell23_7524515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_7524515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524515 prefixEnd_7524515 := by exact prefixLift 7524515
  have htrace : WordTrace (prefixWord ++ tailWord_7524515) baseStart_7524515 baseEnd_7524515 := by
    simpa [prefixWord, tailWord_7524515, baseEnd_7524515] using wordTrace_append hprefix tailTrace_7524515
  have hstable : (prefixWord ++ tailWord_7524515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524515).length < 2 ^ (prefixWord ++ tailWord_7524515).sum := by decide
  have hdescent : baseEnd_7524515 < baseStart_7524515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524606 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7524606 : Nat := 118140960795 + 7524606 * 2 ^ 59
def prefixEnd_7524606 : Nat := 4983230072969 + 3 ^ 40 * 7524606 * 2
def baseEnd_7524606 : Nat := 1287913204568430726039991

theorem tailTrace_7524606 : CollatzResearch.WordTrace tailWord_7524606 prefixEnd_7524606 1287913204568430726039991 := by
  unfold tailWord_7524606
  simp only [CollatzResearch.WordTrace]
  refine ⟨34305615922205629654730209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182963284918430024825227781 34305615922205629654730209)
  ·
    refine ⟨25729211941654222241047657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34305615922205629654730209 25729211941654222241047657)
    ·
      refine ⟨19296908956240666680785743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25729211941654222241047657 19296908956240666680785743)
      ·
        refine ⟨28945363434361000021178615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19296908956240666680785743 28945363434361000021178615)
        ·
          refine ⟨43418045151541500031767923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28945363434361000021178615 43418045151541500031767923)
          ·
            refine ⟨65127067727312250047651885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43418045151541500031767923 65127067727312250047651885)
            ·
              refine ⟨24422650397742093767869457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65127067727312250047651885 24422650397742093767869457)
              ·
                refine ⟨18316987798306570325902093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24422650397742093767869457 18316987798306570325902093)
                ·
                  refine ⟨6868870424364963872213285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18316987798306570325902093 6868870424364963872213285)
                  ·
                    refine ⟨1287913204568430726039991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868870424364963872213285 1287913204568430726039991)
                    ·
                      rfl

theorem cell23_7524606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7524606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524606 prefixEnd_7524606 := by exact prefixLift 7524606
  have htrace : WordTrace (prefixWord ++ tailWord_7524606) baseStart_7524606 baseEnd_7524606 := by
    simpa [prefixWord, tailWord_7524606, baseEnd_7524606] using wordTrace_append hprefix tailTrace_7524606
  have hstable : (prefixWord ++ tailWord_7524606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524606).length < 2 ^ (prefixWord ++ tailWord_7524606).sum := by decide
  have hdescent : baseEnd_7524606 < baseStart_7524606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524616 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_7524616 : Nat := 118140960795 + 7524616 * 2 ^ 59
def prefixEnd_7524616 : Nat := 4983230072969 + 3 ^ 40 * 7524616 * 2
def baseEnd_7524616 : Nat := 3863744748511837138994927

theorem tailTrace_7524616 : CollatzResearch.WordTrace tailWord_7524616 prefixEnd_7524616 3863744748511837138994927 := by
  unfold tailWord_7524616
  simp only [CollatzResearch.WordTrace]
  refine ⟨137222646053804404472852851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182963528071739205963803801 137222646053804404472852851)
  ·
    refine ⟨205833969080706606709279277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137222646053804404472852851 205833969080706606709279277)
    ·
      refine ⟨77187738405264977515979729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205833969080706606709279277 77187738405264977515979729)
      ·
        refine ⟨57890803803948733136984797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77187738405264977515979729 57890803803948733136984797)
        ·
          refine ⟨21709051426480774926369299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57890803803948733136984797 21709051426480774926369299)
          ·
            refine ⟨32563577139721162389553949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21709051426480774926369299 32563577139721162389553949)
            ·
              refine ⟨12211341427395435896082731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32563577139721162389553949 12211341427395435896082731)
              ·
                refine ⟨18317012141093153844124097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12211341427395435896082731 18317012141093153844124097)
                ·
                  refine ⟨13737759105819865383093073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18317012141093153844124097 13737759105819865383093073)
                  ·
                    refine ⟨10303319329364899037319805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13737759105819865383093073 10303319329364899037319805)
                    ·
                      refine ⟨3863744748511837138994927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303319329364899037319805 3863744748511837138994927)
                      ·
                        rfl

theorem cell23_7524616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_7524616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524616 prefixEnd_7524616 := by exact prefixLift 7524616
  have htrace : WordTrace (prefixWord ++ tailWord_7524616) baseStart_7524616 baseEnd_7524616 := by
    simpa [prefixWord, tailWord_7524616, baseEnd_7524616] using wordTrace_append hprefix tailTrace_7524616
  have hstable : (prefixWord ++ tailWord_7524616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524616).length < 2 ^ (prefixWord ++ tailWord_7524616).sum := by decide
  have hdescent : baseEnd_7524616 < baseStart_7524616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524666 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_7524666 : Nat := 118140960795 + 7524666 * 2 ^ 59
def prefixEnd_7524666 : Nat := 4983230072969 + 3 ^ 40 * 7524666 * 2
def baseEnd_7524666 : Nat := 1287923474181520647789899

theorem tailTrace_7524666 : CollatzResearch.WordTrace tailWord_7524666 prefixEnd_7524666 1287923474181520647789899 := by
  unfold tailWord_7524666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68611778939356916871256463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182964743838285111656683901 68611778939356916871256463)
  ·
    refine ⟨102917668409035375306884695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68611778939356916871256463 102917668409035375306884695)
    ·
      refine ⟨154376502613553062960327043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102917668409035375306884695 154376502613553062960327043)
      ·
        refine ⟨231564753920329594440490565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154376502613553062960327043 231564753920329594440490565)
        ·
          refine ⟨43418391360061798957591981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231564753920329594440490565 43418391360061798957591981)
          ·
            refine ⟨16281896760023174609096993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43418391360061798957591981 16281896760023174609096993)
            ·
              refine ⟨12211422570017380956822745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16281896760023174609096993 12211422570017380956822745)
              ·
                refine ⟨9158566927513035717617059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12211422570017380956822745 9158566927513035717617059)
                ·
                  refine ⟨13737850391269553576425589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158566927513035717617059 13737850391269553576425589)
                  ·
                    refine ⟨1287923474181520647789899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13737850391269553576425589 1287923474181520647789899)
                    ·
                      rfl

theorem cell23_7524666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_7524666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524666 prefixEnd_7524666 := by exact prefixLift 7524666
  have htrace : WordTrace (prefixWord ++ tailWord_7524666) baseStart_7524666 baseEnd_7524666 := by
    simpa [prefixWord, tailWord_7524666, baseEnd_7524666] using wordTrace_append hprefix tailTrace_7524666
  have hstable : (prefixWord ++ tailWord_7524666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524666).length < 2 ^ (prefixWord ++ tailWord_7524666).sum := by decide
  have hdescent : baseEnd_7524666 < baseStart_7524666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524679 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 6, 4]
def baseStart_7524679 : Nat := 118140960795 + 7524679 * 2 ^ 59
def prefixEnd_7524679 : Nat := 4983230072969 + 3 ^ 40 * 7524679 * 2
def baseEnd_7524679 : Nat := 1287925699264356797502379

theorem tailTrace_7524679 : CollatzResearch.WordTrace tailWord_7524679 prefixEnd_7524679 1287925699264356797502379 := by
  unfold tailWord_7524679
  simp only [CollatzResearch.WordTrace]
  refine ⟨274447589906380570705249091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182965059937587047136832727 274447589906380570705249091)
  ·
    refine ⟨411671384859570856057873637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274447589906380570705249091 411671384859570856057873637)
    ·
      refine ⟨77188384661169535510851307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411671384859570856057873637 77188384661169535510851307)
      ·
        refine ⟨115782576991754303266276961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77188384661169535510851307 115782576991754303266276961)
        ·
          refine ⟨86836932743815727449707721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115782576991754303266276961 86836932743815727449707721)
          ·
            refine ⟨65127699557861795587280791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86836932743815727449707721 65127699557861795587280791)
            ·
              refine ⟨97691549336792693380921187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65127699557861795587280791 97691549336792693380921187)
              ·
                refine ⟨146537324005189040071381781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97691549336792693380921187 146537324005189040071381781)
                ·
                  refine ⟨6868937062743236253346021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146537324005189040071381781 6868937062743236253346021)
                  ·
                    refine ⟨1287925699264356797502379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868937062743236253346021 1287925699264356797502379)
                    ·
                      rfl

theorem cell23_7524679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_7524679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524679 prefixEnd_7524679 := by exact prefixLift 7524679
  have htrace : WordTrace (prefixWord ++ tailWord_7524679) baseStart_7524679 baseEnd_7524679 := by
    simpa [prefixWord, tailWord_7524679, baseEnd_7524679] using wordTrace_append hprefix tailTrace_7524679
  have hstable : (prefixWord ++ tailWord_7524679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524679).length < 2 ^ (prefixWord ++ tailWord_7524679).sum := by decide
  have hdescent : baseEnd_7524679 < baseStart_7524679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524689 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_7524689 : Nat := 118140960795 + 7524689 * 2 ^ 59
def prefixEnd_7524689 : Nat := 4983230072969 + 3 ^ 40 * 7524689 * 2
def baseEnd_7524689 : Nat := 3863782232599615353382091

theorem tailTrace_7524689 : CollatzResearch.WordTrace tailWord_7524689 prefixEnd_7524689 3863782232599615353382091 := by
  unfold tailWord_7524689
  simp only [CollatzResearch.WordTrace]
  refine ⟨274447954636344342413113121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182965303090896228275408747 274447954636344342413113121)
  ·
    refine ⟨205835965977258256809834841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274447954636344342413113121 205835965977258256809834841)
    ·
      refine ⟨154376974482943692607376131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205835965977258256809834841 154376974482943692607376131)
      ·
        refine ⟨231565461724415538911064197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154376974482943692607376131 231565461724415538911064197)
        ·
          refine ⟨43418524073327913545824537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231565461724415538911064197 43418524073327913545824537)
          ·
            refine ⟨32563893054995935159368403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43418524073327913545824537 32563893054995935159368403)
            ·
              refine ⟨48845839582493902739052605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32563893054995935159368403 48845839582493902739052605)
              ·
                refine ⟨18317189843435213527144727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48845839582493902739052605 18317189843435213527144727)
                ·
                  refine ⟨27475784765152820290717091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18317189843435213527144727 27475784765152820290717091)
                  ·
                    refine ⟨41213677147729230436075637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27475784765152820290717091 41213677147729230436075637)
                    ·
                      refine ⟨3863782232599615353382091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41213677147729230436075637 3863782232599615353382091)
                      ·
                        rfl

theorem cell23_7524689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_7524689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524689 prefixEnd_7524689 := by exact prefixLift 7524689
  have htrace : WordTrace (prefixWord ++ tailWord_7524689) baseStart_7524689 baseEnd_7524689 := by
    simpa [prefixWord, tailWord_7524689, baseEnd_7524689] using wordTrace_append hprefix tailTrace_7524689
  have hstable : (prefixWord ++ tailWord_7524689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524689).length < 2 ^ (prefixWord ++ tailWord_7524689).sum := by decide
  have hdescent : baseEnd_7524689 < baseStart_7524689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524703 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 3, 2, 2]
def baseStart_7524703 : Nat := 118140960795 + 7524703 * 2 ^ 59
def prefixEnd_7524703 : Nat := 4983230072969 + 3 ^ 40 * 7524703 * 2
def baseEnd_7524703 : Nat := 3863789421328778298607027

theorem tailTrace_7524703 : CollatzResearch.WordTrace tailWord_7524703 prefixEnd_7524703 3863789421328778298607027 := by
  unfold tailWord_7524703
  simp only [CollatzResearch.WordTrace]
  refine ⟨274448465258293622804122763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182965643505529081869415175 274448465258293622804122763)
  ·
    refine ⟨411672697887440434206184145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274448465258293622804122763 411672697887440434206184145)
    ·
      refine ⟨308754523415580325654638109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411672697887440434206184145 308754523415580325654638109)
      ·
        refine ⟨115782946280842622120489291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308754523415580325654638109 115782946280842622120489291)
        ·
          refine ⟨173674419421263933180733937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115782946280842622120489291 173674419421263933180733937)
          ·
            refine ⟨130255814565947949885550453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173674419421263933180733937 130255814565947949885550453)
            ·
              refine ⟨12211482615557620301770355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130255814565947949885550453 12211482615557620301770355)
              ·
                refine ⟨18317223923336430452655533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12211482615557620301770355 18317223923336430452655533)
                ·
                  refine ⟨6868958971251161419745825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18317223923336430452655533 6868958971251161419745825)
                  ·
                    refine ⟨5151719228438371064809369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868958971251161419745825 5151719228438371064809369)
                    ·
                      refine ⟨3863789421328778298607027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151719228438371064809369 3863789421328778298607027)
                      ·
                        rfl

theorem cell23_7524703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_7524703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524703 prefixEnd_7524703 := by exact prefixLift 7524703
  have htrace : WordTrace (prefixWord ++ tailWord_7524703) baseStart_7524703 baseEnd_7524703 := by
    simpa [prefixWord, tailWord_7524703, baseEnd_7524703] using wordTrace_append hprefix tailTrace_7524703
  have hstable : (prefixWord ++ tailWord_7524703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524703).length < 2 ^ (prefixWord ++ tailWord_7524703).sum := by decide
  have hdescent : baseEnd_7524703 < baseStart_7524703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524706 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7524706 : Nat := 118140960795 + 7524706 * 2 ^ 59
def prefixEnd_7524706 : Nat := 4983230072969 + 3 ^ 40 * 7524706 * 2
def baseEnd_7524706 : Nat := 3863790961770741786869513

theorem tailTrace_7524706 : CollatzResearch.WordTrace tailWord_7524706 prefixEnd_7524706 3863790961770741786869513 := by
  unfold tailWord_7524706
  simp only [CollatzResearch.WordTrace]
  refine ⟨68612143669320688579120493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182965716451521836210987981 68612143669320688579120493)
  ·
    refine ⟨25729553875995258217170185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68612143669320688579120493 25729553875995258217170185)
    ·
      refine ⟨19297165406996443662877639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25729553875995258217170185 19297165406996443662877639)
      ·
        refine ⟨28945748110494665494316459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19297165406996443662877639 28945748110494665494316459)
        ·
          refine ⟨43418622165741998241474689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28945748110494665494316459 43418622165741998241474689)
          ·
            refine ⟨32563966624306498681106017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43418622165741998241474689 32563966624306498681106017)
            ·
              refine ⟨24422974968229874010829513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32563966624306498681106017 24422974968229874010829513)
              ·
                refine ⟨18317231226172405508122135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24422974968229874010829513 18317231226172405508122135)
                ·
                  refine ⟨27475846839258608262183203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18317231226172405508122135 27475846839258608262183203)
                  ·
                    refine ⟨41213770258887912393274805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27475846839258608262183203 41213770258887912393274805)
                    ·
                      refine ⟨3863790961770741786869513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41213770258887912393274805 3863790961770741786869513)
                      ·
                        rfl

theorem cell23_7524706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7524706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524706 prefixEnd_7524706 := by exact prefixLift 7524706
  have htrace : WordTrace (prefixWord ++ tailWord_7524706) baseStart_7524706 baseEnd_7524706 := by
    simpa [prefixWord, tailWord_7524706, baseEnd_7524706] using wordTrace_append hprefix tailTrace_7524706
  have hstable : (prefixWord ++ tailWord_7524706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524706).length < 2 ^ (prefixWord ++ tailWord_7524706).sum := by decide
  have hdescent : baseEnd_7524706 < baseStart_7524706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524709 : List Nat := [1, 3, 1, 3, 1, 4, 2, 8]
def baseStart_7524709 : Nat := 118140960795 + 7524709 * 2 ^ 59
def prefixEnd_7524709 : Nat := 4983230072969 + 3 ^ 40 * 7524709 * 2
def baseEnd_7524709 : Nat := 143103426007877973153037

theorem tailTrace_7524709 : CollatzResearch.WordTrace tailWord_7524709 prefixEnd_7524709 143103426007877973153037 := by
  unfold tailWord_7524709
  simp only [CollatzResearch.WordTrace]
  refine ⟨274448684096271885828841181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182965789397514590552560787 274448684096271885828841181)
  ·
    refine ⟨102918256536101957185815443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274448684096271885828841181 102918256536101957185815443)
    ·
      refine ⟨154377384804152935778723165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102918256536101957185815443 154377384804152935778723165)
      ·
        refine ⟨57891519301557350917021187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154377384804152935778723165 57891519301557350917021187)
        ·
          refine ⟨86837278952336026375531781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57891519301557350917021187 86837278952336026375531781)
          ·
            refine ⟨16281989803563004945412209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86837278952336026375531781 16281989803563004945412209)
            ·
              refine ⟨12211492352672253709059157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16281989803563004945412209 12211492352672253709059157)
              ·
                refine ⟨143103426007877973153037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12211492352672253709059157 143103426007877973153037)
                ·
                  rfl

theorem cell23_7524709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 8].length) (baseStart_7524709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524709 prefixEnd_7524709 := by exact prefixLift 7524709
  have htrace : WordTrace (prefixWord ++ tailWord_7524709) baseStart_7524709 baseEnd_7524709 := by
    simpa [prefixWord, tailWord_7524709, baseEnd_7524709] using wordTrace_append hprefix tailTrace_7524709
  have hstable : (prefixWord ++ tailWord_7524709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524709).length < 2 ^ (prefixWord ++ tailWord_7524709).sum := by decide
  have hdescent : baseEnd_7524709 < baseStart_7524709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524759 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7524759 : Nat := 118140960795 + 7524759 * 2 ^ 59
def prefixEnd_7524759 : Nat := 4983230072969 + 3 ^ 40 * 7524759 * 2
def baseEnd_7524759 : Nat := 3863818176245430079506769

theorem tailTrace_7524759 : CollatzResearch.WordTrace tailWord_7524759 prefixEnd_7524759 3863818176245430079506769 := by
  unfold tailWord_7524759
  simp only [CollatzResearch.WordTrace]
  refine ⟨274450507746090744368161331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182967005164060496245440887 274450507746090744368161331)
  ·
    refine ⟨411675761619136116552241997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274450507746090744368161331 411675761619136116552241997)
    ·
      refine ⟨154378410607176043707090749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411675761619136116552241997 154378410607176043707090749)
      ·
        refine ⟨57891903977691016390159031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154378410607176043707090749 57891903977691016390159031)
        ·
          refine ⟨86837855966536524585238547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57891903977691016390159031 86837855966536524585238547)
          ·
            refine ⟨130256783949804786877857821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86837855966536524585238547 130256783949804786877857821)
            ·
              refine ⟨48846293981176795079196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130256783949804786877857821 48846293981176795079196683)
              ·
                refine ⟨73269440971765192618795025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48846293981176795079196683 73269440971765192618795025)
                ·
                  refine ⟨54952080728823894464096269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73269440971765192618795025 54952080728823894464096269)
                  ·
                    refine ⟨20607030273308960424036101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54952080728823894464096269 20607030273308960424036101)
                    ·
                      refine ⟨3863818176245430079506769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20607030273308960424036101 3863818176245430079506769)
                      ·
                        rfl

theorem cell23_7524759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7524759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524759 prefixEnd_7524759 := by exact prefixLift 7524759
  have htrace : WordTrace (prefixWord ++ tailWord_7524759) baseStart_7524759 baseEnd_7524759 := by
    simpa [prefixWord, tailWord_7524759, baseEnd_7524759] using wordTrace_append hprefix tailTrace_7524759
  have hstable : (prefixWord ++ tailWord_7524759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524759).length < 2 ^ (prefixWord ++ tailWord_7524759).sum := by decide
  have hdescent : baseEnd_7524759 < baseStart_7524759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524793 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7524793 : Nat := 118140960795 + 7524793 * 2 ^ 59
def prefixEnd_7524793 : Nat := 4983230072969 + 3 ^ 40 * 7524793 * 2
def baseEnd_7524793 : Nat := 3863835634587682946481613

theorem tailTrace_7524793 : CollatzResearch.WordTrace tailWord_7524793 prefixEnd_7524793 3863835634587682946481613 := by
  unfold tailWord_7524793
  simp only [CollatzResearch.WordTrace]
  refine ⟨274451747827967568174899033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182967831885311712116599355 274451747827967568174899033)
  ·
    refine ⟨205838810870975676131174275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274451747827967568174899033 205838810870975676131174275)
    ·
      refine ⟨308758216306463514196761413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205838810870975676131174275 308758216306463514196761413)
      ·
        refine ⟨57892165557461908911892765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308758216306463514196761413 57892165557461908911892765)
        ·
          refine ⟨21709562084048215841959787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57892165557461908911892765 21709562084048215841959787)
          ·
            refine ⟨32564343126072323762939681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21709562084048215841959787 32564343126072323762939681)
            ·
              refine ⟨24423257344554242822204761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32564343126072323762939681 24423257344554242822204761)
              ·
                refine ⟨18317443008415682116653571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24423257344554242822204761 18317443008415682116653571)
                ·
                  refine ⟨27476164512623523174980357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18317443008415682116653571 27476164512623523174980357)
                  ·
                    refine ⟨5151780846116910595308817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27476164512623523174980357 5151780846116910595308817)
                    ·
                      refine ⟨3863835634587682946481613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151780846116910595308817 3863835634587682946481613)
                      ·
                        rfl

theorem cell23_7524793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7524793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524793 prefixEnd_7524793 := by exact prefixLift 7524793
  have htrace : WordTrace (prefixWord ++ tailWord_7524793) baseStart_7524793 baseEnd_7524793 := by
    simpa [prefixWord, tailWord_7524793, baseEnd_7524793] using wordTrace_append hprefix tailTrace_7524793
  have hstable : (prefixWord ++ tailWord_7524793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524793).length < 2 ^ (prefixWord ++ tailWord_7524793).sum := by decide
  have hdescent : baseEnd_7524793 < baseStart_7524793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524797 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_7524797 : Nat := 118140960795 + 7524797 * 2 ^ 59
def prefixEnd_7524797 : Nat := 4983230072969 + 3 ^ 40 * 7524797 * 2
def baseEnd_7524797 : Nat := 3863837688510300930831595

theorem tailTrace_7524797 : CollatzResearch.WordTrace tailWord_7524797 prefixEnd_7524797 3863837688510300930831595 := by
  unfold tailWord_7524797
  simp only [CollatzResearch.WordTrace]
  refine ⟨274451893719953076858044645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182967929146635384572029763 274451893719953076858044645)
  ·
    refine ⟨51459730072491201910883371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274451893719953076858044645 51459730072491201910883371)
    ·
      refine ⟨77189595108736802866325057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51459730072491201910883371 77189595108736802866325057)
      ·
        refine ⟨57892196331552602149743793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77189595108736802866325057 57892196331552602149743793)
        ·
          refine ⟨43419147248664451612307845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57892196331552602149743793 43419147248664451612307845)
          ·
            refine ⟨8141090109124584677307721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43419147248664451612307845 8141090109124584677307721)
            ·
              refine ⟨6105817581843438507980791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8141090109124584677307721 6105817581843438507980791)
              ·
                refine ⟨9158726372765157761971187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105817581843438507980791 9158726372765157761971187)
                ·
                  refine ⟨13738089559147736642956781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158726372765157761971187 13738089559147736642956781)
                  ·
                    refine ⟨5151783584680401241108793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13738089559147736642956781 5151783584680401241108793)
                    ·
                      refine ⟨3863837688510300930831595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151783584680401241108793 3863837688510300930831595)
                      ·
                        rfl

theorem cell23_7524797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_7524797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524797 prefixEnd_7524797 := by exact prefixLift 7524797
  have htrace : WordTrace (prefixWord ++ tailWord_7524797) baseStart_7524797 baseEnd_7524797 := by
    simpa [prefixWord, tailWord_7524797, baseEnd_7524797] using wordTrace_append hprefix tailTrace_7524797
  have hstable : (prefixWord ++ tailWord_7524797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524797).length < 2 ^ (prefixWord ++ tailWord_7524797).sum := by decide
  have hdescent : baseEnd_7524797 < baseStart_7524797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524804 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7524804 : Nat := 118140960795 + 7524804 * 2 ^ 59
def prefixEnd_7524804 : Nat := 4983230072969 + 3 ^ 40 * 7524804 * 2
def baseEnd_7524804 : Nat := 3863841282874882403444063

theorem tailTrace_7524804 : CollatzResearch.WordTrace tailWord_7524804 prefixEnd_7524804 3863841282874882403444063 := by
  unfold tailWord_7524804
  simp only [CollatzResearch.WordTrace]
  refine ⟨137226074515463858526774733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182968099353951811369032977 137226074515463858526774733)
  ·
    refine ⟨51459777943298946947540525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137226074515463858526774733 51459777943298946947540525)
    ·
      refine ⟨19297416728737105105327697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51459777943298946947540525 19297416728737105105327697)
      ·
        refine ⟨14473062546552828828995773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19297416728737105105327697 14473062546552828828995773)
        ·
          refine ⟨5427398454957310810873415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14473062546552828828995773 5427398454957310810873415)
          ·
            refine ⟨8141097682435966216310123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427398454957310810873415 8141097682435966216310123)
            ·
              refine ⟨12211646523653949324465185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141097682435966216310123 12211646523653949324465185)
              ·
                refine ⟨9158734892740461993348889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12211646523653949324465185 9158734892740461993348889)
                ·
                  refine ⟨6869051169555346495011667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9158734892740461993348889 6869051169555346495011667)
                  ·
                    refine ⟨10303576754333019742517501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6869051169555346495011667 10303576754333019742517501)
                    ·
                      refine ⟨3863841282874882403444063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303576754333019742517501 3863841282874882403444063)
                      ·
                        rfl

theorem cell23_7524804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7524804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524804 prefixEnd_7524804 := by exact prefixLift 7524804
  have htrace : WordTrace (prefixWord ++ tailWord_7524804) baseStart_7524804 baseEnd_7524804 := by
    simpa [prefixWord, tailWord_7524804, baseEnd_7524804] using wordTrace_append hprefix tailTrace_7524804
  have hstable : (prefixWord ++ tailWord_7524804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524804).length < 2 ^ (prefixWord ++ tailWord_7524804).sum := by decide
  have hdescent : baseEnd_7524804 < baseStart_7524804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524826 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_7524826 : Nat := 118140960795 + 7524826 * 2 ^ 59
def prefixEnd_7524826 : Nat := 4983230072969 + 3 ^ 40 * 7524826 * 2
def baseEnd_7524826 : Nat := 3863852579449281317368961

theorem tailTrace_7524826 : CollatzResearch.WordTrace tailWord_7524826 prefixEnd_7524826 3863852579449281317368961 := by
  unfold tailWord_7524826
  simp only [CollatzResearch.WordTrace]
  refine ⟨68613237859212003702712583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182968634291232009873900221 68613237859212003702712583)
  ·
    refine ⟨102919856788818005554068875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68613237859212003702712583 102919856788818005554068875)
    ·
      refine ⟨154379785183227008331103313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102919856788818005554068875 154379785183227008331103313)
      ·
        refine ⟨115784838887420256248327485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154379785183227008331103313 115784838887420256248327485)
        ·
          refine ⟨43419314582782596093122807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115784838887420256248327485 43419314582782596093122807)
          ·
            refine ⟨65128971874173894139684211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43419314582782596093122807 65128971874173894139684211)
            ·
              refine ⟨97693457811260841209526317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65128971874173894139684211 97693457811260841209526317)
              ·
                refine ⟨36635046679222815453572369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97693457811260841209526317 36635046679222815453572369)
                ·
                  refine ⟨27476285009417111590179277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36635046679222815453572369 27476285009417111590179277)
                  ·
                    refine ⟨10303606878531416846317229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27476285009417111590179277 10303606878531416846317229)
                    ·
                      refine ⟨3863852579449281317368961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303606878531416846317229 3863852579449281317368961)
                      ·
                        rfl

theorem cell23_7524826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_7524826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524826 prefixEnd_7524826 := by exact prefixLift 7524826
  have htrace : WordTrace (prefixWord ++ tailWord_7524826) baseStart_7524826 baseEnd_7524826 := by
    simpa [prefixWord, tailWord_7524826, baseEnd_7524826] using wordTrace_append hprefix tailTrace_7524826
  have hstable : (prefixWord ++ tailWord_7524826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524826).length < 2 ^ (prefixWord ++ tailWord_7524826).sum := by decide
  have hdescent : baseEnd_7524826 < baseStart_7524826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524846 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_7524846 : Nat := 118140960795 + 7524846 * 2 ^ 59
def prefixEnd_7524846 : Nat := 4983230072969 + 3 ^ 40 * 7524846 * 2
def baseEnd_7524846 : Nat := 1287954283020790413039623

theorem tailTrace_7524846 : CollatzResearch.WordTrace tailWord_7524846 prefixEnd_7524846 1287954283020790413039623 := by
  unfold tailWord_7524846
  simp only [CollatzResearch.WordTrace]
  refine ⟨34306710112096944778322299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182969120597850372151052261 34306710112096944778322299)
  ·
    refine ⟨51460065168145417167483449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34306710112096944778322299 51460065168145417167483449)
    ·
      refine ⟨38595048876109062875612587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51460065168145417167483449 38595048876109062875612587)
      ·
        refine ⟨57892573314163594313418881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38595048876109062875612587 57892573314163594313418881)
        ·
          refine ⟨43419429985622695735064161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57892573314163594313418881 43419429985622695735064161)
          ·
            refine ⟨32564572489217021801298121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43419429985622695735064161 32564572489217021801298121)
            ·
              refine ⟨24423429366912766350973591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32564572489217021801298121 24423429366912766350973591)
              ·
                refine ⟨36635144050369149526460387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24423429366912766350973591 36635144050369149526460387)
                ·
                  refine ⟨54952716075553724289690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36635144050369149526460387 54952716075553724289690581)
                  ·
                    refine ⟨1287954283020790413039623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54952716075553724289690581 1287954283020790413039623)
                    ·
                      rfl

theorem cell23_7524846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_7524846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524846 prefixEnd_7524846 := by exact prefixLift 7524846
  have htrace : WordTrace (prefixWord ++ tailWord_7524846) baseStart_7524846 baseEnd_7524846 := by
    simpa [prefixWord, tailWord_7524846, baseEnd_7524846] using wordTrace_append hprefix tailTrace_7524846
  have hstable : (prefixWord ++ tailWord_7524846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524846).length < 2 ^ (prefixWord ++ tailWord_7524846).sum := by decide
  have hdescent : baseEnd_7524846 < baseStart_7524846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524879 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_7524879 : Nat := 118140960795 + 7524879 * 2 ^ 59
def prefixEnd_7524879 : Nat := 4983230072969 + 3 ^ 40 * 7524879 * 2
def baseEnd_7524879 : Nat := 3863879793923969610006217

theorem tailTrace_7524879 : CollatzResearch.WordTrace tailWord_7524879 prefixEnd_7524879 3863879793923969610006217 := by
  unfold tailWord_7524879
  simp only [CollatzResearch.WordTrace]
  refine ⟨274454884505656004862529691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182969923003770669908353127 274454884505656004862529691)
  ·
    refine ⟨411682326758484007293794537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274454884505656004862529691 411682326758484007293794537)
    ·
      refine ⟨308761745068863005470345903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411682326758484007293794537 308761745068863005470345903)
      ·
        refine ⟨463142617603294508205518855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308761745068863005470345903 463142617603294508205518855)
        ·
          refine ⟨694713926404941762308278283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463142617603294508205518855 694713926404941762308278283)
          ·
            refine ⟨1042070889607412643462417425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694713926404941762308278283 1042070889607412643462417425)
            ·
              refine ⟨781553167205559482596813069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042070889607412643462417425 781553167205559482596813069)
              ·
                refine ⟨293082437702084805973804901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781553167205559482596813069 293082437702084805973804901)
                ·
                  refine ⟨54952957069140901120088419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293082437702084805973804901 54952957069140901120088419)
                  ·
                    refine ⟨82429435603711351680132629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54952957069140901120088419 82429435603711351680132629)
                    ·
                      refine ⟨3863879793923969610006217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82429435603711351680132629 3863879793923969610006217)
                      ·
                        rfl

theorem cell23_7524879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_7524879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524879 prefixEnd_7524879 := by exact prefixLift 7524879
  have htrace : WordTrace (prefixWord ++ tailWord_7524879) baseStart_7524879 baseEnd_7524879 := by
    simpa [prefixWord, tailWord_7524879, baseEnd_7524879] using wordTrace_append hprefix tailTrace_7524879
  have hstable : (prefixWord ++ tailWord_7524879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524879).length < 2 ^ (prefixWord ++ tailWord_7524879).sum := by decide
  have hdescent : baseEnd_7524879 < baseStart_7524879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524943 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 4, 3, 2]
def baseStart_7524943 : Nat := 118140960795 + 7524943 * 2 ^ 59
def prefixEnd_7524943 : Nat := 4983230072969 + 3 ^ 40 * 7524943 * 2
def baseEnd_7524943 : Nat := 3863912656685857359605923

theorem tailTrace_7524943 : CollatzResearch.WordTrace tailWord_7524943 prefixEnd_7524943 3863912656685857359605923 := by
  unfold tailWord_7524943
  simp only [CollatzResearch.WordTrace]
  refine ⟨274457218777424143792859483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182971479184949429195239655 274457218777424143792859483)
  ·
    refine ⟨411685828166136215689289225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274457218777424143792859483 411685828166136215689289225)
    ·
      refine ⟨308764371124602161766966919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411685828166136215689289225 308764371124602161766966919)
      ·
        refine ⟨463146556686903242650450379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308764371124602161766966919 463146556686903242650450379)
        ·
          refine ⟨694719835030354863975675569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463146556686903242650450379 694719835030354863975675569)
          ·
            refine ⟨521039876272766147981756677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694719835030354863975675569 521039876272766147981756677)
            ·
              refine ⟨97694976801143652746579377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 521039876272766147981756677 97694976801143652746579377)
              ·
                refine ⟨73271232600857739559934533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97694976801143652746579377 73271232600857739559934533)
                ·
                  refine ⟨13738356112660826167487725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73271232600857739559934533 13738356112660826167487725)
                  ·
                    refine ⟨5151883542247809812807897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13738356112660826167487725 5151883542247809812807897)
                    ·
                      refine ⟨3863912656685857359605923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151883542247809812807897 3863912656685857359605923)
                      ·
                        rfl

theorem cell23_7524943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3, 2].length) (baseStart_7524943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524943 prefixEnd_7524943 := by exact prefixLift 7524943
  have htrace : WordTrace (prefixWord ++ tailWord_7524943) baseStart_7524943 baseEnd_7524943 := by
    simpa [prefixWord, tailWord_7524943, baseEnd_7524943] using wordTrace_append hprefix tailTrace_7524943
  have hstable : (prefixWord ++ tailWord_7524943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524943).length < 2 ^ (prefixWord ++ tailWord_7524943).sum := by decide
  have hdescent : baseEnd_7524943 < baseStart_7524943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524946 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7524946 : Nat := 118140960795 + 7524946 * 2 ^ 59
def prefixEnd_7524946 : Nat := 4983230072969 + 3 ^ 40 * 7524946 * 2
def baseEnd_7524946 : Nat := 3863914197127820847868409

theorem tailTrace_7524946 : CollatzResearch.WordTrace tailWord_7524946 prefixEnd_7524946 3863914197127820847868409 := by
  unfold tailWord_7524946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68614332049103318826304673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182971552130942183536812461 68614332049103318826304673)
  ·
    refine ⟨51460749036827489119728505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68614332049103318826304673 51460749036827489119728505)
    ·
      refine ⟨38595561777620616839796379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51460749036827489119728505 38595561777620616839796379)
      ·
        refine ⟨57893342666430925259694569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38595561777620616839796379 57893342666430925259694569)
        ·
          refine ⟨43420006999823193944770927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57893342666430925259694569 43420006999823193944770927)
          ·
            refine ⟨65130010499734790917156391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43420006999823193944770927 65130010499734790917156391)
            ·
              refine ⟨97695015749602186375734587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65130010499734790917156391 97695015749602186375734587)
              ·
                refine ⟨146542523624403279563601881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97695015749602186375734587 146542523624403279563601881)
                ·
                  refine ⟨109906892718302459672701411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146542523624403279563601881 109906892718302459672701411)
                  ·
                    refine ⟨164860339077453689509052117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109906892718302459672701411 164860339077453689509052117)
                    ·
                      refine ⟨3863914197127820847868409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164860339077453689509052117 3863914197127820847868409)
                      ·
                        rfl

theorem cell23_7524946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7524946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524946 prefixEnd_7524946 := by exact prefixLift 7524946
  have htrace : WordTrace (prefixWord ++ tailWord_7524946) baseStart_7524946 baseEnd_7524946 := by
    simpa [prefixWord, tailWord_7524946, baseEnd_7524946] using wordTrace_append hprefix tailTrace_7524946
  have hstable : (prefixWord ++ tailWord_7524946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524946).length < 2 ^ (prefixWord ++ tailWord_7524946).sum := by decide
  have hdescent : baseEnd_7524946 < baseStart_7524946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524960 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2]
def baseStart_7524960 : Nat := 118140960795 + 7524960 * 2 ^ 59
def prefixEnd_7524960 : Nat := 4983230072969 + 3 ^ 40 * 7524960 * 2
def baseEnd_7524960 : Nat := 3863921385856983793093345

theorem tailTrace_7524960 : CollatzResearch.WordTrace tailWord_7524960 prefixEnd_7524960 3863921385856983793093345 := by
  unfold tailWord_7524960
  simp only [CollatzResearch.WordTrace]
  refine ⟨137228919409181277848114167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182971892545575037130818889 137228919409181277848114167)
  ·
    refine ⟨205843379113771916772171251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137228919409181277848114167 205843379113771916772171251)
    ·
      refine ⟨308765068670657875158256877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205843379113771916772171251 308765068670657875158256877)
      ·
        refine ⟨115786900751496703184346329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308765068670657875158256877 115786900751496703184346329)
        ·
          refine ⟨86840175563622527388259747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115786900751496703184346329 86840175563622527388259747)
          ·
            refine ⟨130260263345433791082389621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86840175563622527388259747 130260263345433791082389621)
            ·
              refine ⟨12211899688634417913974027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130260263345433791082389621 12211899688634417913974027)
              ·
                refine ⟨18317849532951626870961041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12211899688634417913974027 18317849532951626870961041)
                ·
                  refine ⟨13738387149713720153220781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18317849532951626870961041 13738387149713720153220781)
                  ·
                    refine ⟨5151895181142645057457793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13738387149713720153220781 5151895181142645057457793)
                    ·
                      refine ⟨3863921385856983793093345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151895181142645057457793 3863921385856983793093345)
                      ·
                        rfl

theorem cell23_7524960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_7524960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524960 prefixEnd_7524960 := by exact prefixLift 7524960
  have htrace : WordTrace (prefixWord ++ tailWord_7524960) baseStart_7524960 baseEnd_7524960 := by
    simpa [prefixWord, tailWord_7524960, baseEnd_7524960] using wordTrace_append hprefix tailTrace_7524960
  have hstable : (prefixWord ++ tailWord_7524960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524960).length < 2 ^ (prefixWord ++ tailWord_7524960).sum := by decide
  have hdescent : baseEnd_7524960 < baseStart_7524960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7524993 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7524993 : Nat := 118140960795 + 7524993 * 2 ^ 59
def prefixEnd_7524993 : Nat := 4983230072969 + 3 ^ 40 * 7524993 * 2
def baseEnd_7524993 : Nat := 3863938330718582163980693

theorem tailTrace_7524993 : CollatzResearch.WordTrace tailWord_7524993 prefixEnd_7524993 3863938330718582163980693 := by
  unfold tailWord_7524993
  simp only [CollatzResearch.WordTrace]
  refine ⟨274459042427243002332179633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182972694951495334888119755 274459042427243002332179633)
  ·
    refine ⟨205844281820432251749134725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274459042427243002332179633 205844281820432251749134725)
    ·
      refine ⟨38595802841331047202962761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205844281820432251749134725 38595802841331047202962761)
      ·
        refine ⟨28946852130998285402222071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38595802841331047202962761 28946852130998285402222071)
        ·
          refine ⟨43420278196497428103333107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28946852130998285402222071 43420278196497428103333107)
          ·
            refine ⟨65130417294746142154999661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43420278196497428103333107 65130417294746142154999661)
            ·
              refine ⟨24423906485529803308124873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65130417294746142154999661 24423906485529803308124873)
              ·
                refine ⟨18317929864147352481093655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24423906485529803308124873 18317929864147352481093655)
                ·
                  refine ⟨27476894796221028721640483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18317929864147352481093655 27476894796221028721640483)
                  ·
                    refine ⟨41215342194331543082460725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27476894796221028721640483 41215342194331543082460725)
                    ·
                      refine ⟨3863938330718582163980693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41215342194331543082460725 3863938330718582163980693)
                      ·
                        rfl

theorem cell23_7524993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7524993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7524993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7524993 prefixEnd_7524993 := by exact prefixLift 7524993
  have htrace : WordTrace (prefixWord ++ tailWord_7524993) baseStart_7524993 baseEnd_7524993 := by
    simpa [prefixWord, tailWord_7524993, baseEnd_7524993] using wordTrace_append hprefix tailTrace_7524993
  have hstable : (prefixWord ++ tailWord_7524993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7524993).length < 2 ^ (prefixWord ++ tailWord_7524993).sum := by decide
  have hdescent : baseEnd_7524993 < baseStart_7524993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7524993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525018 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7525018 : Nat := 118140960795 + 7525018 * 2 ^ 59
def prefixEnd_7525018 : Nat := 4983230072969 + 3 ^ 40 * 7525018 * 2
def baseEnd_7525018 : Nat := 3863951167734944566168079

theorem tailTrace_7525018 : CollatzResearch.WordTrace tailWord_7525018 prefixEnd_7525018 3863951167734944566168079 := by
  unfold tailWord_7525018
  simp only [CollatzResearch.WordTrace]
  refine ⟨68614988563038107900459927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182973302834768287734559805 68614988563038107900459927)
  ·
    refine ⟨102922482844557161850689891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68614988563038107900459927 102922482844557161850689891)
    ·
      refine ⟨154383724266835742776034837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102922482844557161850689891 154383724266835742776034837)
      ·
        refine ⟨7236737075007925442626633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154383724266835742776034837 7236737075007925442626633)
        ·
          refine ⟨5427552806255944081969975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7236737075007925442626633 5427552806255944081969975)
          ·
            refine ⟨8141329209383916122954963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427552806255944081969975 8141329209383916122954963)
            ·
              refine ⟨12211993814075874184432445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141329209383916122954963 12211993814075874184432445)
              ·
                refine ⟨4579497680278452819162167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12211993814075874184432445 4579497680278452819162167)
                ·
                  refine ⟨6869246520417679228743251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579497680278452819162167 6869246520417679228743251)
                  ·
                    refine ⟨10303869780626518843114877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6869246520417679228743251 10303869780626518843114877)
                    ·
                      refine ⟨3863951167734944566168079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303869780626518843114877 3863951167734944566168079)
                      ·
                        rfl

theorem cell23_7525018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7525018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525018 prefixEnd_7525018 := by exact prefixLift 7525018
  have htrace : WordTrace (prefixWord ++ tailWord_7525018) baseStart_7525018 baseEnd_7525018 := by
    simpa [prefixWord, tailWord_7525018, baseEnd_7525018] using wordTrace_append hprefix tailTrace_7525018
  have hstable : (prefixWord ++ tailWord_7525018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525018).length < 2 ^ (prefixWord ++ tailWord_7525018).sum := by decide
  have hdescent : baseEnd_7525018 < baseStart_7525018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525040 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3]
def baseStart_7525040 : Nat := 118140960795 + 7525040 * 2 ^ 59
def prefixEnd_7525040 : Nat := 4983230072969 + 3 ^ 40 * 7525040 * 2
def baseEnd_7525040 : Nat := 3863962464309343480092977

theorem tailTrace_7525040 : CollatzResearch.WordTrace tailWord_7525040 prefixEnd_7525040 3863962464309343480092977 := by
  unfold tailWord_7525040
  simp only [CollatzResearch.WordTrace]
  refine ⟨137230378329036364679570287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182973837772048486239427049 137230378329036364679570287)
  ·
    refine ⟨205845567493554547019355431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137230378329036364679570287 205845567493554547019355431)
    ·
      refine ⟨308768351240331820529033147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205845567493554547019355431 308768351240331820529033147)
      ·
        refine ⟨463152526860497730793549721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308768351240331820529033147 463152526860497730793549721)
        ·
          refine ⟨347364395145373298095162291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463152526860497730793549721 347364395145373298095162291)
          ·
            refine ⟨521046592718059947142743437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347364395145373298095162291 521046592718059947142743437)
            ·
              refine ⟨195392472269272480178528789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521046592718059947142743437 195392472269272480178528789)
              ·
                refine ⟨9159022137622147508368537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195392472269272480178528789 9159022137622147508368537)
                ·
                  refine ⟨6869266603216610631276403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9159022137622147508368537 6869266603216610631276403)
                  ·
                    refine ⟨10303899904824915946914605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6869266603216610631276403 10303899904824915946914605)
                    ·
                      refine ⟨3863962464309343480092977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10303899904824915946914605 3863962464309343480092977)
                      ·
                        rfl

theorem cell23_7525040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_7525040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525040 prefixEnd_7525040 := by exact prefixLift 7525040
  have htrace : WordTrace (prefixWord ++ tailWord_7525040) baseStart_7525040 baseEnd_7525040 := by
    simpa [prefixWord, tailWord_7525040, baseEnd_7525040] using wordTrace_append hprefix tailTrace_7525040
  have hstable : (prefixWord ++ tailWord_7525040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525040).length < 2 ^ (prefixWord ++ tailWord_7525040).sum := by decide
  have hdescent : baseEnd_7525040 < baseStart_7525040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525041 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7525041 : Nat := 118140960795 + 7525041 * 2 ^ 59
def prefixEnd_7525041 : Nat := 4983230072969 + 3 ^ 40 * 7525041 * 2
def baseEnd_7525041 : Nat := 3863962977789997976180473

theorem tailTrace_7525041 : CollatzResearch.WordTrace tailWord_7525041 prefixEnd_7525041 3863962977789997976180473 := by
  unfold tailWord_7525041
  simp only [CollatzResearch.WordTrace]
  refine ⟨274460793131069106529926977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182973862087379404353284651 274460793131069106529926977)
  ·
    refine ⟨205845594848301829897445233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274460793131069106529926977 205845594848301829897445233)
    ·
      refine ⟨154384196136226372423083925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205845594848301829897445233 154384196136226372423083925)
      ·
        refine ⟨7236759193885611207332059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154384196136226372423083925 7236759193885611207332059)
        ·
          refine ⟨10855138790828416810998089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236759193885611207332059 10855138790828416810998089)
          ·
            refine ⟨8141354093121312608248567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10855138790828416810998089 8141354093121312608248567)
            ·
              refine ⟨12212031139681968912372851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141354093121312608248567 12212031139681968912372851)
              ·
                refine ⟨18318046709522953368559277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12212031139681968912372851 18318046709522953368559277)
                ·
                  refine ⟨6869267516071107513209729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18318046709522953368559277 6869267516071107513209729)
                  ·
                    refine ⟨5151950637053330634907297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6869267516071107513209729 5151950637053330634907297)
                    ·
                      refine ⟨3863962977789997976180473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151950637053330634907297 3863962977789997976180473)
                      ·
                        rfl

theorem cell23_7525041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7525041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525041 prefixEnd_7525041 := by exact prefixLift 7525041
  have htrace : WordTrace (prefixWord ++ tailWord_7525041) baseStart_7525041 baseEnd_7525041 := by
    simpa [prefixWord, tailWord_7525041, baseEnd_7525041] using wordTrace_append hprefix tailTrace_7525041
  have hstable : (prefixWord ++ tailWord_7525041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525041).length < 2 ^ (prefixWord ++ tailWord_7525041).sum := by decide
  have hdescent : baseEnd_7525041 < baseStart_7525041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525050 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_7525050 : Nat := 118140960795 + 7525050 * 2 ^ 59
def prefixEnd_7525050 : Nat := 4983230072969 + 3 ^ 40 * 7525050 * 2
def baseEnd_7525050 : Nat := 3863967599115888440967931

theorem tailTrace_7525050 : CollatzResearch.WordTrace tailWord_7525050 prefixEnd_7525050 3863967599115888440967931 := by
  unfold tailWord_7525050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68615280347009125266751151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182974080925357667378003069 68615280347009125266751151)
  ·
    refine ⟨102922920520513687900126727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68615280347009125266751151 102922920520513687900126727)
    ·
      refine ⟨154384380780770531850190091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102922920520513687900126727 154384380780770531850190091)
      ·
        refine ⟨231576571171155797775285137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154384380780770531850190091 231576571171155797775285137)
        ·
          refine ⟨173682428378366848331463853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231576571171155797775285137 173682428378366848331463853)
          ·
            refine ⟨65130910641887568124298945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173682428378366848331463853 65130910641887568124298945)
            ·
              refine ⟨48848182981415676093224209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65130910641887568124298945 48848182981415676093224209)
              ·
                refine ⟨36636137236061757069918157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48848182981415676093224209 36636137236061757069918157)
                ·
                  refine ⟨13738551463523158901219309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36636137236061757069918157 13738551463523158901219309)
                  ·
                    refine ⟨5151956798821184587957241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13738551463523158901219309 5151956798821184587957241)
                    ·
                      refine ⟨3863967599115888440967931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151956798821184587957241 3863967599115888440967931)
                      ·
                        rfl

theorem cell23_7525050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_7525050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525050 prefixEnd_7525050 := by exact prefixLift 7525050
  have htrace : WordTrace (prefixWord ++ tailWord_7525050) baseStart_7525050 baseEnd_7525050 := by
    simpa [prefixWord, tailWord_7525050, baseEnd_7525050] using wordTrace_append hprefix tailTrace_7525050
  have hstable : (prefixWord ++ tailWord_7525050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525050).length < 2 ^ (prefixWord ++ tailWord_7525050).sum := by decide
  have hdescent : baseEnd_7525050 < baseStart_7525050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525080 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_7525080 : Nat := 118140960795 + 7525080 * 2 ^ 59
def prefixEnd_7525080 : Nat := 4983230072969 + 3 ^ 40 * 7525080 * 2
def baseEnd_7525080 : Nat := 3863983003535523323592793

theorem tailTrace_7525080 : CollatzResearch.WordTrace tailWord_7525080 prefixEnd_7525080 3863983003535523323592793 := by
  unfold tailWord_7525080
  simp only [CollatzResearch.WordTrace]
  refine ⟨137231107788963908095298347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182974810385285210793731129 137231107788963908095298347)
  ·
    refine ⟨205846661683445862142947521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137231107788963908095298347 205846661683445862142947521)
    ·
      refine ⟨154384996262584396607210641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205846661683445862142947521 154384996262584396607210641)
      ·
        refine ⟨115788747196938297455407981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154384996262584396607210641 115788747196938297455407981)
        ·
          refine ⟨43420780198851861545777993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115788747196938297455407981 43420780198851861545777993)
          ·
            refine ⟨32565585149138896159333495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43420780198851861545777993 32565585149138896159333495)
            ·
              refine ⟨48848377723708344239000243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32565585149138896159333495 48848377723708344239000243)
              ·
                refine ⟨73272566585562516358500365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48848377723708344239000243 73272566585562516358500365)
                ·
                  refine ⟨27477212469585943634437637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73272566585562516358500365 27477212469585943634437637)
                  ·
                    refine ⟨5151977338047364431457057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27477212469585943634437637 5151977338047364431457057)
                    ·
                      refine ⟨3863983003535523323592793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151977338047364431457057 3863983003535523323592793)
                      ·
                        rfl

theorem cell23_7525080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_7525080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525080 prefixEnd_7525080 := by exact prefixLift 7525080
  have htrace : WordTrace (prefixWord ++ tailWord_7525080) baseStart_7525080 baseEnd_7525080 := by
    simpa [prefixWord, tailWord_7525080, baseEnd_7525080] using wordTrace_append hprefix tailTrace_7525080
  have hstable : (prefixWord ++ tailWord_7525080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525080).length < 2 ^ (prefixWord ++ tailWord_7525080).sum := by decide
  have hdescent : baseEnd_7525080 < baseStart_7525080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525097 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 2, 2, 2]
def baseStart_7525097 : Nat := 118140960795 + 7525097 * 2 ^ 59
def prefixEnd_7525097 : Nat := 4983230072969 + 3 ^ 40 * 7525097 * 2
def baseEnd_7525097 : Nat := 3863991732706649757080215

theorem tailTrace_7525097 : CollatzResearch.WordTrace tailWord_7525097 prefixEnd_7525097 3863991732706649757080215 := by
  unfold tailWord_7525097
  simp only [CollatzResearch.WordTrace]
  refine ⟨274462835618866228093965545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182975223745910818729310363 274462835618866228093965545)
  ·
    refine ⟨205847126714149671070474159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274462835618866228093965545 205847126714149671070474159)
    ·
      refine ⟨308770690071224506605711239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205847126714149671070474159 308770690071224506605711239)
      ·
        refine ⟨463156035106836759908566859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308770690071224506605711239 463156035106836759908566859)
        ·
          refine ⟨694734052660255139862850289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463156035106836759908566859 694734052660255139862850289)
          ·
            refine ⟨521050539495191354897137717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694734052660255139862850289 521050539495191354897137717)
            ·
              refine ⟨48848488077674189521606661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521050539495191354897137717 48848488077674189521606661)
              ·
                refine ⟨9159091514563910535301249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48848488077674189521606661 9159091514563910535301249)
                ·
                  refine ⟨6869318635922932901475937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9159091514563910535301249 6869318635922932901475937)
                  ·
                    refine ⟨5151988976942199676106953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6869318635922932901475937 5151988976942199676106953)
                    ·
                      refine ⟨3863991732706649757080215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5151988976942199676106953 3863991732706649757080215)
                      ·
                        rfl

theorem cell23_7525097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2, 2].length) (baseStart_7525097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525097 prefixEnd_7525097 := by exact prefixLift 7525097
  have htrace : WordTrace (prefixWord ++ tailWord_7525097) baseStart_7525097 baseEnd_7525097 := by
    simpa [prefixWord, tailWord_7525097, baseEnd_7525097] using wordTrace_append hprefix tailTrace_7525097
  have hstable : (prefixWord ++ tailWord_7525097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525097).length < 2 ^ (prefixWord ++ tailWord_7525097).sum := by decide
  have hdescent : baseEnd_7525097 < baseStart_7525097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525110 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7525110 : Nat := 118140960795 + 7525110 * 2 ^ 59
def prefixEnd_7525110 : Nat := 4983230072969 + 3 ^ 40 * 7525110 * 2
def baseEnd_7525110 : Nat := 3863998407955158206217655

theorem tailTrace_7525110 : CollatzResearch.WordTrace tailWord_7525110 prefixEnd_7525110 3863998407955158206217655 := by
  unfold tailWord_7525110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17153956860488695707136799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182975539845212754209459189 17153956860488695707136799)
  ·
    refine ⟨25730935290733043560705199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17153956860488695707136799 25730935290733043560705199)
    ·
      refine ⟨38596402936099565341057799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25730935290733043560705199 38596402936099565341057799)
      ·
        refine ⟨57894604404149348011586699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38596402936099565341057799 57894604404149348011586699)
        ·
          refine ⟨86841906606224022017380049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57894604404149348011586699 86841906606224022017380049)
          ·
            refine ⟨65131429954668016513035037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86841906606224022017380049 65131429954668016513035037)
            ·
              refine ⟨24424286233000506192388139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65131429954668016513035037 24424286233000506192388139)
              ·
                refine ⟨36636429349500759288582209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24424286233000506192388139 36636429349500759288582209)
                ·
                  refine ⟨27477322012125569466436657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36636429349500759288582209 27477322012125569466436657)
                  ·
                    refine ⟨20607991509094177099827493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27477322012125569466436657 20607991509094177099827493)
                    ·
                      refine ⟨3863998407955158206217655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20607991509094177099827493 3863998407955158206217655)
                      ·
                        rfl

theorem cell23_7525110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7525110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525110 prefixEnd_7525110 := by exact prefixLift 7525110
  have htrace : WordTrace (prefixWord ++ tailWord_7525110) baseStart_7525110 baseEnd_7525110 := by
    simpa [prefixWord, tailWord_7525110, baseEnd_7525110] using wordTrace_append hprefix tailTrace_7525110
  have hstable : (prefixWord ++ tailWord_7525110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525110).length < 2 ^ (prefixWord ++ tailWord_7525110).sum := by decide
  have hdescent : baseEnd_7525110 < baseStart_7525110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525165 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7525165 : Nat := 118140960795 + 7525165 * 2 ^ 59
def prefixEnd_7525165 : Nat := 4983230072969 + 3 ^ 40 * 7525165 * 2
def baseEnd_7525165 : Nat := 3864026649391155491029903

theorem tailTrace_7525165 : CollatzResearch.WordTrace tailWord_7525165 prefixEnd_7525165 3864026649391155491029903 := by
  unfold tailWord_7525165
  simp only [CollatzResearch.WordTrace]
  refine ⟨274465315782619875707440949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182976877188413250471627299 274465315782619875707440949)
  ·
    refine ⟨25731123354620613347572589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274465315782619875707440949 25731123354620613347572589)
    ·
      refine ⟨9649171257982730005339721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25731123354620613347572589 9649171257982730005339721)
      ·
        refine ⟨7236878443487047504004791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9649171257982730005339721 7236878443487047504004791)
        ·
          refine ⟨10855317665230571256007187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236878443487047504004791 10855317665230571256007187)
          ·
            refine ⟨16282976497845856884010781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10855317665230571256007187 16282976497845856884010781)
            ·
              refine ⟨6106116186692196331504043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16282976497845856884010781 6106116186692196331504043)
              ·
                refine ⟨9159174280038294497256065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106116186692196331504043 9159174280038294497256065)
                ·
                  refine ⟨6869380710028720872942049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9159174280038294497256065 6869380710028720872942049)
                  ·
                    refine ⟨5152035532521540654706537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6869380710028720872942049 5152035532521540654706537)
                    ·
                      refine ⟨3864026649391155491029903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152035532521540654706537 3864026649391155491029903)
                      ·
                        rfl

theorem cell23_7525165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7525165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525165 prefixEnd_7525165 := by exact prefixLift 7525165
  have htrace : WordTrace (prefixWord ++ tailWord_7525165) baseStart_7525165 baseEnd_7525165 := by
    simpa [prefixWord, tailWord_7525165, baseEnd_7525165] using wordTrace_append hprefix tailTrace_7525165
  have hstable : (prefixWord ++ tailWord_7525165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525165).length < 2 ^ (prefixWord ++ tailWord_7525165).sum := by decide
  have hdescent : baseEnd_7525165 < baseStart_7525165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525188 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 5]
def baseStart_7525188 : Nat := 118140960795 + 7525188 * 2 ^ 59
def prefixEnd_7525188 : Nat := 4983230072969 + 3 ^ 40 * 7525188 * 2
def baseEnd_7525188 : Nat := 429337606605134322338033

theorem tailTrace_7525188 : CollatzResearch.WordTrace tailWord_7525188 prefixEnd_7525188 429337606605134322338033 := by
  unfold tailWord_7525188
  simp only [CollatzResearch.WordTrace]
  refine ⟨137233077330768275317764109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182977436441024367090352145 137233077330768275317764109)
  ·
    refine ⟨51462403999038103244161541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137233077330768275317764109 51462403999038103244161541)
    ·
      refine ⟨9649200749819644358280289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51462403999038103244161541 9649200749819644358280289)
      ·
        refine ⟨7236900562364733268710217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9649200749819644358280289 7236900562364733268710217)
        ·
          refine ⟨5427675421773549951532663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7236900562364733268710217 5427675421773549951532663)
          ·
            refine ⟨8141513132660324927298995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427675421773549951532663 8141513132660324927298995)
            ·
              refine ⟨12212269698990487390948493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141513132660324927298995 12212269698990487390948493)
              ·
                refine ⟨4579601137121432771605685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12212269698990487390948493 4579601137121432771605685)
                ·
                  refine ⟨429337606605134322338033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4579601137121432771605685 429337606605134322338033)
                  ·
                    rfl

theorem cell23_7525188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_7525188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525188 prefixEnd_7525188 := by exact prefixLift 7525188
  have htrace : WordTrace (prefixWord ++ tailWord_7525188) baseStart_7525188 baseEnd_7525188 := by
    simpa [prefixWord, tailWord_7525188, baseEnd_7525188] using wordTrace_append hprefix tailTrace_7525188
  have hstable : (prefixWord ++ tailWord_7525188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525188).length < 2 ^ (prefixWord ++ tailWord_7525188).sum := by decide
  have hdescent : baseEnd_7525188 < baseStart_7525188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525193 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 8]
def baseStart_7525193 : Nat := 118140960795 + 7525193 * 2 ^ 59
def prefixEnd_7525193 : Nat := 4983230072969 + 3 ^ 40 * 7525193 * 2
def baseEnd_7525193 : Nat := 429337891872164597942197

theorem tailTrace_7525193 : CollatzResearch.WordTrace tailWord_7525193 prefixEnd_7525193 429337891872164597942197 := by
  unfold tailWord_7525193
  simp only [CollatzResearch.WordTrace]
  refine ⟨274466337026518436489460233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182977558017678957659640155 274466337026518436489460233)
  ·
    refine ⟨205849752769888827367095175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274466337026518436489460233 205849752769888827367095175)
    ·
      refine ⟨308774629154833241050642763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205849752769888827367095175 308774629154833241050642763)
      ·
        refine ⟨463161943732249861575964145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308774629154833241050642763 463161943732249861575964145)
        ·
          refine ⟨347371457799187396181973109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463161943732249861575964145 347371457799187396181973109)
          ·
            refine ⟨32566074168673818392059979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347371457799187396181973109 32566074168673818392059979)
            ·
              refine ⟨48849111253010727588089969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32566074168673818392059979 48849111253010727588089969)
              ·
                refine ⟨36636833439758045691067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48849111253010727588089969 36636833439758045691067477)
                ·
                  refine ⟨429337891872164597942197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36636833439758045691067477 429337891872164597942197)
                  ·
                    rfl

theorem cell23_7525193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_7525193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525193 prefixEnd_7525193 := by exact prefixLift 7525193
  have htrace : WordTrace (prefixWord ++ tailWord_7525193) baseStart_7525193 baseEnd_7525193 := by
    simpa [prefixWord, tailWord_7525193, baseEnd_7525193] using wordTrace_append hprefix tailTrace_7525193
  have hstable : (prefixWord ++ tailWord_7525193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525193).length < 2 ^ (prefixWord ++ tailWord_7525193).sum := by decide
  have hdescent : baseEnd_7525193 < baseStart_7525193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525207 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_7525207 : Nat := 118140960795 + 7525207 * 2 ^ 59
def prefixEnd_7525207 : Nat := 4983230072969 + 3 ^ 40 * 7525207 * 2
def baseEnd_7525207 : Nat := 3864048215578644326704709

theorem tailTrace_7525207 : CollatzResearch.WordTrace tailWord_7525207 prefixEnd_7525207 3864048215578644326704709 := by
  unfold tailWord_7525207
  simp only [CollatzResearch.WordTrace]
  refine ⟨274466847648467716880469875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182977898432311811253646583 274466847648467716880469875)
  ·
    refine ⟨411700271472701575320704813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274466847648467716880469875 411700271472701575320704813)
    ·
      refine ⟨154387601802263090745264305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411700271472701575320704813 154387601802263090745264305)
      ·
        refine ⟨115790701351697318058948229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154387601802263090745264305 115790701351697318058948229)
        ·
          refine ⟨21710756503443247136052793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115790701351697318058948229 21710756503443247136052793)
          ·
            refine ⟨16283067377582435352039595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21710756503443247136052793 16283067377582435352039595)
            ·
              refine ⟨24424601066373653028059393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16283067377582435352039595 24424601066373653028059393)
              ·
                refine ⟨18318450799780239771044545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24424601066373653028059393 18318450799780239771044545)
                ·
                  refine ⟨13738838099835179828283409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18318450799780239771044545 13738838099835179828283409)
                  ·
                    refine ⟨10304128574876384871212557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13738838099835179828283409 10304128574876384871212557)
                    ·
                      refine ⟨3864048215578644326704709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10304128574876384871212557 3864048215578644326704709)
                      ·
                        rfl

theorem cell23_7525207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_7525207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525207 prefixEnd_7525207 := by exact prefixLift 7525207
  have htrace : WordTrace (prefixWord ++ tailWord_7525207) baseStart_7525207 baseEnd_7525207 := by
    simpa [prefixWord, tailWord_7525207, baseEnd_7525207] using wordTrace_append hprefix tailTrace_7525207
  have hstable : (prefixWord ++ tailWord_7525207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525207).length < 2 ^ (prefixWord ++ tailWord_7525207).sum := by decide
  have hdescent : baseEnd_7525207 < baseStart_7525207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525240 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_7525240 : Nat := 118140960795 + 7525240 * 2 ^ 59
def prefixEnd_7525240 : Nat := 4983230072969 + 3 ^ 40 * 7525240 * 2
def baseEnd_7525240 : Nat := 1288021720146747565864019

theorem tailTrace_7525240 : CollatzResearch.WordTrace tailWord_7525240 prefixEnd_7525240 1288021720146747565864019 := by
  unfold tailWord_7525240
  simp only [CollatzResearch.WordTrace]
  refine ⟨137234025628674081758210587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182978700838232109010947449 137234025628674081758210587)
  ·
    refine ⟨205851038443011122637315881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137234025628674081758210587 205851038443011122637315881)
    ·
      refine ⟨154388278832258341977986911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205851038443011122637315881 154388278832258341977986911)
      ·
        refine ⟨231582418248387512966980367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154388278832258341977986911 231582418248387512966980367)
        ·
          refine ⟨347373627372581269450470551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231582418248387512966980367 347373627372581269450470551)
          ·
            refine ⟨521060441058871904175705827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347373627372581269450470551 521060441058871904175705827)
            ·
              refine ⟨781590661588307856263558741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521060441058871904175705827 781590661588307856263558741)
              ·
                refine ⟨9159265565487982690588579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 781590661588307856263558741 9159265565487982690588579)
                ·
                  refine ⟨13738898348231974035882869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9159265565487982690588579 13738898348231974035882869)
                  ·
                    refine ⟨1288021720146747565864019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13738898348231974035882869 1288021720146747565864019)
                    ·
                      rfl

theorem cell23_7525240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_7525240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525240 prefixEnd_7525240 := by exact prefixLift 7525240
  have htrace : WordTrace (prefixWord ++ tailWord_7525240) baseStart_7525240 baseEnd_7525240 := by
    simpa [prefixWord, tailWord_7525240, baseEnd_7525240] using wordTrace_append hprefix tailTrace_7525240
  have hstable : (prefixWord ++ tailWord_7525240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525240).length < 2 ^ (prefixWord ++ tailWord_7525240).sum := by decide
  have hdescent : baseEnd_7525240 < baseStart_7525240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525247 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 2, 3, 2]
def baseStart_7525247 : Nat := 118140960795 + 7525247 * 2 ^ 59
def prefixEnd_7525247 : Nat := 4983230072969 + 3 ^ 40 * 7525247 * 2
def baseEnd_7525247 : Nat := 3864068754804824170204525

theorem tailTrace_7525247 : CollatzResearch.WordTrace tailWord_7525247 prefixEnd_7525247 3864068754804824170204525 := by
  unfold tailWord_7525247
  simp only [CollatzResearch.WordTrace]
  refine ⟨274468306568322803711925995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182978871045548535807950663 274468306568322803711925995)
  ·
    refine ⟨411702459852484205567888993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274468306568322803711925995 411702459852484205567888993)
    ·
      refine ⟨308776844889363154175916745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411702459852484205567888993 308776844889363154175916745)
      ·
        refine ⟨231582633667022365631937559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308776844889363154175916745 231582633667022365631937559)
        ·
          refine ⟨347373950500533548447906339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231582633667022365631937559 347373950500533548447906339)
          ·
            refine ⟨521060925750800322671859509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347373950500533548447906339 521060925750800322671859509)
            ·
              refine ⟨48849461789137530250486829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521060925750800322671859509 48849461789137530250486829)
              ·
                refine ⟨18318548170926573843932561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48849461789137530250486829 18318548170926573843932561)
                ·
                  refine ⟨13738911128194930382949421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18318548170926573843932561 13738911128194930382949421)
                  ·
                    refine ⟨5152091673073098893606033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13738911128194930382949421 5152091673073098893606033)
                    ·
                      refine ⟨3864068754804824170204525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152091673073098893606033 3864068754804824170204525)
                      ·
                        rfl

theorem cell23_7525247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_7525247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525247 prefixEnd_7525247 := by exact prefixLift 7525247
  have htrace : WordTrace (prefixWord ++ tailWord_7525247) baseStart_7525247 baseEnd_7525247 := by
    simpa [prefixWord, tailWord_7525247, baseEnd_7525247] using wordTrace_append hprefix tailTrace_7525247
  have hstable : (prefixWord ++ tailWord_7525247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525247).length < 2 ^ (prefixWord ++ tailWord_7525247).sum := by decide
  have hdescent : baseEnd_7525247 < baseStart_7525247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525280 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_7525280 : Nat := 118140960795 + 7525280 * 2 ^ 59
def prefixEnd_7525280 : Nat := 4983230072969 + 3 ^ 40 * 7525280 * 2
def baseEnd_7525280 : Nat := 3864085699666422541091873

theorem tailTrace_7525280 : CollatzResearch.WordTrace tailWord_7525280 prefixEnd_7525280 3864085699666422541091873 := by
  unfold tailWord_7525280
  simp only [CollatzResearch.WordTrace]
  refine ⟨137234755088601625173938647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182979673451468833565251529 137234755088601625173938647)
  ·
    refine ⟨205852132632902437760907971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137234755088601625173938647 205852132632902437760907971)
    ·
      refine ⟨308778198949353656641361957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205852132632902437760907971 308778198949353656641361957)
      ·
        refine ⟨57895912303003810620255367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308778198949353656641361957 57895912303003810620255367)
        ·
          refine ⟨86843868454505715930383051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57895912303003810620255367 86843868454505715930383051)
          ·
            refine ⟨130265802681758573895574577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86843868454505715930383051 130265802681758573895574577)
            ·
              refine ⟨97699352011318930421680933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130265802681758573895574577 97699352011318930421680933)
              ·
                refine ⟨18318628502122299454065175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97699352011318930421680933 18318628502122299454065175)
                ·
                  refine ⟨27477942753183449181097763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18318628502122299454065175 27477942753183449181097763)
                  ·
                    refine ⟨41216914129775173771646645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27477942753183449181097763 41216914129775173771646645)
                    ·
                      refine ⟨3864085699666422541091873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41216914129775173771646645 3864085699666422541091873)
                      ·
                        rfl

theorem cell23_7525280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_7525280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525280 prefixEnd_7525280 := by exact prefixLift 7525280
  have htrace : WordTrace (prefixWord ++ tailWord_7525280) baseStart_7525280 baseEnd_7525280 := by
    simpa [prefixWord, tailWord_7525280, baseEnd_7525280] using wordTrace_append hprefix tailTrace_7525280
  have hstable : (prefixWord ++ tailWord_7525280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525280).length < 2 ^ (prefixWord ++ tailWord_7525280).sum := by decide
  have hdescent : baseEnd_7525280 < baseStart_7525280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525362 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7525362 : Nat := 118140960795 + 7525362 * 2 ^ 59
def prefixEnd_7525362 : Nat := 4983230072969 + 3 ^ 40 * 7525362 * 2
def baseEnd_7525362 : Nat := 3864127805080091220266497

theorem tailTrace_7525362 : CollatzResearch.WordTrace tailWord_7525362 prefixEnd_7525362 3864127805080091220266497 := by
  unfold tailWord_7525362
  simp only [CollatzResearch.WordTrace]
  refine ⟨68618125240726544588090585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182981667308604118901574893 68618125240726544588090585)
  ·
    refine ⟨51463593930544908441067939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68618125240726544588090585 51463593930544908441067939)
    ·
      refine ⟨77195390895817362661601909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51463593930544908441067939 77195390895817362661601909)
      ·
        refine ⟨7237067896482877749525179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77195390895817362661601909 7237067896482877749525179)
        ·
          refine ⟨10855601844724316624287769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237067896482877749525179 10855601844724316624287769)
          ·
            refine ⟨8141701383543237468215827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10855601844724316624287769 8141701383543237468215827)
            ·
              refine ⟨12212552075314856202323741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141701383543237468215827 12212552075314856202323741)
              ·
                refine ⟨4579707028243071075871403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12212552075314856202323741 4579707028243071075871403)
                ·
                  refine ⟨6869560542364606613807105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579707028243071075871403 6869560542364606613807105)
                  ·
                    refine ⟨5152170406773454960355329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6869560542364606613807105 5152170406773454960355329)
                    ·
                      refine ⟨3864127805080091220266497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152170406773454960355329 3864127805080091220266497)
                      ·
                        rfl

theorem cell23_7525362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7525362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525362 prefixEnd_7525362 := by exact prefixLift 7525362
  have htrace : WordTrace (prefixWord ++ tailWord_7525362) baseStart_7525362 baseEnd_7525362 := by
    simpa [prefixWord, tailWord_7525362, baseEnd_7525362] using wordTrace_append hprefix tailTrace_7525362
  have hstable : (prefixWord ++ tailWord_7525362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525362).length < 2 ^ (prefixWord ++ tailWord_7525362).sum := by decide
  have hdescent : baseEnd_7525362 < baseStart_7525362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525405 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_7525405 : Nat := 118140960795 + 7525405 * 2 ^ 59
def prefixEnd_7525405 : Nat := 4983230072969 + 3 ^ 40 * 7525405 * 2
def baseEnd_7525405 : Nat := 3864149884748234552028799

theorem tailTrace_7525405 : CollatzResearch.WordTrace tailWord_7525405 prefixEnd_7525405 3864149884748234552028799 := by
  unfold tailWord_7525405
  simp only [CollatzResearch.WordTrace]
  refine ⟨274474069301750396696177669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182982712867833597797451779 274474069301750396696177669)
  ·
    refine ⟨51463887994078199380533313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274474069301750396696177669 51463887994078199380533313)
    ·
      refine ⟨38597915995558649535399985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51463887994078199380533313 38597915995558649535399985)
      ·
        refine ⟨28948436996668987151549989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38597915995558649535399985 28948436996668987151549989)
        ·
          refine ⟨5427831936875435090915623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28948436996668987151549989 5427831936875435090915623)
          ·
            refine ⟨8141747905313152636373435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427831936875435090915623 8141747905313152636373435)
            ·
              refine ⟨12212621857969728954560153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141747905313152636373435 12212621857969728954560153)
              ·
                refine ⟨9159466393477296715920115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12212621857969728954560153 9159466393477296715920115)
                ·
                  refine ⟨13739199590215945073880173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9159466393477296715920115 13739199590215945073880173)
                  ·
                    refine ⟨5152199846330979402705065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13739199590215945073880173 5152199846330979402705065)
                    ·
                      refine ⟨3864149884748234552028799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152199846330979402705065 3864149884748234552028799)
                      ·
                        rfl

theorem cell23_7525405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_7525405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525405 prefixEnd_7525405 := by exact prefixLift 7525405
  have htrace : WordTrace (prefixWord ++ tailWord_7525405) baseStart_7525405 baseEnd_7525405 := by
    simpa [prefixWord, tailWord_7525405, baseEnd_7525405] using wordTrace_append hprefix tailTrace_7525405
  have hstable : (prefixWord ++ tailWord_7525405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525405).length < 2 ^ (prefixWord ++ tailWord_7525405).sum := by decide
  have hdescent : baseEnd_7525405 < baseStart_7525405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525441 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 5]
def baseStart_7525441 : Nat := 118140960795 + 7525441 * 2 ^ 59
def prefixEnd_7525441 : Nat := 4983230072969 + 3 ^ 40 * 7525441 * 2
def baseEnd_7525441 : Nat := 429352041116866267908737

theorem tailTrace_7525441 : CollatzResearch.WordTrace tailWord_7525441 prefixEnd_7525441 429352041116866267908737 := by
  unfold tailWord_7525441
  simp only [CollatzResearch.WordTrace]
  refine ⟨274475382329619974844488177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182983588219746649896325451 274475382329619974844488177)
  ·
    refine ⟨205856536747214981133366133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274475382329619974844488177 205856536747214981133366133)
    ·
      refine ⟨19299050320051404481253075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205856536747214981133366133 19299050320051404481253075)
      ·
        refine ⟨28948575480077106721879613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19299050320051404481253075 28948575480077106721879613)
        ·
          refine ⟨10855715805028915020704855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28948575480077106721879613 10855715805028915020704855)
          ·
            refine ⟨16283573707543372531057283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10855715805028915020704855 16283573707543372531057283)
            ·
              refine ⟨24425360561315058796585925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16283573707543372531057283 24425360561315058796585925)
              ·
                refine ⟨4579755105246573524359861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24425360561315058796585925 4579755105246573524359861)
                ·
                  refine ⟨429352041116866267908737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4579755105246573524359861 429352041116866267908737)
                  ·
                    rfl

theorem cell23_7525441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 5].length) (baseStart_7525441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525441 prefixEnd_7525441 := by exact prefixLift 7525441
  have htrace : WordTrace (prefixWord ++ tailWord_7525441) baseStart_7525441 baseEnd_7525441 := by
    simpa [prefixWord, tailWord_7525441, baseEnd_7525441] using wordTrace_append hprefix tailTrace_7525441
  have hstable : (prefixWord ++ tailWord_7525441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525441).length < 2 ^ (prefixWord ++ tailWord_7525441).sum := by decide
  have hdescent : baseEnd_7525441 < baseStart_7525441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525447 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_7525447 : Nat := 118140960795 + 7525447 * 2 ^ 59
def prefixEnd_7525447 : Nat := 4983230072969 + 3 ^ 40 * 7525447 * 2
def baseEnd_7525447 : Nat := 3864171450935723387703605

theorem tailTrace_7525447 : CollatzResearch.WordTrace tailWord_7525447 prefixEnd_7525447 3864171450935723387703605 := by
  unfold tailWord_7525447
  simp only [CollatzResearch.WordTrace]
  refine ⟨274475601167598237869206595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182983734111732158579471063 274475601167598237869206595)
  ·
    refine ⟨411713401751397356803809893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274475601167598237869206595 411713401751397356803809893)
    ·
      refine ⟨77196262828387004400714355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411713401751397356803809893 77196262828387004400714355)
      ·
        refine ⟨115794394242580506601071533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77196262828387004400714355 115794394242580506601071533)
        ·
          refine ⟨43422897840967689975401825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115794394242580506601071533 43422897840967689975401825)
          ·
            refine ⟨32567173380725767481551369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43422897840967689975401825 32567173380725767481551369)
            ·
              refine ⟨24425380035544325611163527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32567173380725767481551369 24425380035544325611163527)
              ·
                refine ⟨36638070053316488416745291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24425380035544325611163527 36638070053316488416745291)
                ·
                  refine ⟨54957105079974732625117937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36638070053316488416745291 54957105079974732625117937)
                  ·
                    refine ⟨41217828809981049468838453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54957105079974732625117937 41217828809981049468838453)
                    ·
                      refine ⟨3864171450935723387703605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41217828809981049468838453 3864171450935723387703605)
                      ·
                        rfl

theorem cell23_7525447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_7525447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525447 prefixEnd_7525447 := by exact prefixLift 7525447
  have htrace : WordTrace (prefixWord ++ tailWord_7525447) baseStart_7525447 baseEnd_7525447 := by
    simpa [prefixWord, tailWord_7525447, baseEnd_7525447] using wordTrace_append hprefix tailTrace_7525447
  have hstable : (prefixWord ++ tailWord_7525447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525447).length < 2 ^ (prefixWord ++ tailWord_7525447).sum := by decide
  have hdescent : baseEnd_7525447 < baseStart_7525447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525457 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_7525457 : Nat := 118140960795 + 7525457 * 2 ^ 59
def prefixEnd_7525457 : Nat := 4983230072969 + 3 ^ 40 * 7525457 * 2
def baseEnd_7525457 : Nat := 3864176585742268348578559

theorem tailTrace_7525457 : CollatzResearch.WordTrace tailWord_7525457 prefixEnd_7525457 3864176585742268348578559 := by
  unfold tailWord_7525457
  simp only [CollatzResearch.WordTrace]
  refine ⟨274475965897562009577070625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182983977265041339718047083 274475965897562009577070625)
  ·
    refine ⟨205856974423171507182802969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274475965897562009577070625 205856974423171507182802969)
    ·
      refine ⟨154392730817378630387102227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205856974423171507182802969 154392730817378630387102227)
      ·
        refine ⟨231589096226067945580653341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154392730817378630387102227 231589096226067945580653341)
        ·
          refine ⟨86845911084775479592745003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231589096226067945580653341 86845911084775479592745003)
          ·
            refine ⟨130268866627163219389117505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86845911084775479592745003 130268866627163219389117505)
            ·
              refine ⟨97701649970372414541838129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130268866627163219389117505 97701649970372414541838129)
              ·
                refine ⟨73276237477779310906378597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97701649970372414541838129 73276237477779310906378597)
                ·
                  refine ⟨13739294527083620794945987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73276237477779310906378597 13739294527083620794945987)
                  ·
                    refine ⟨20608941790625431192418981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13739294527083620794945987 20608941790625431192418981)
                    ·
                      refine ⟨3864176585742268348578559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20608941790625431192418981 3864176585742268348578559)
                      ·
                        rfl

theorem cell23_7525457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_7525457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525457 prefixEnd_7525457 := by exact prefixLift 7525457
  have htrace : WordTrace (prefixWord ++ tailWord_7525457) baseStart_7525457 baseEnd_7525457 := by
    simpa [prefixWord, tailWord_7525457, baseEnd_7525457] using wordTrace_append hprefix tailTrace_7525457
  have hstable : (prefixWord ++ tailWord_7525457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525457).length < 2 ^ (prefixWord ++ tailWord_7525457).sum := by decide
  have hdescent : baseEnd_7525457 < baseStart_7525457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525501 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_7525501 : Nat := 118140960795 + 7525501 * 2 ^ 59
def prefixEnd_7525501 : Nat := 4983230072969 + 3 ^ 40 * 7525501 * 2
def baseEnd_7525501 : Nat := 1288066392963688725476119

theorem tailTrace_7525501 : CollatzResearch.WordTrace tailWord_7525501 prefixEnd_7525501 1288066392963688725476119 := by
  unfold tailWord_7525501
  simp only [CollatzResearch.WordTrace]
  refine ⟨274477570709402605091672357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182985047139601736727781571 274477570709402605091672357)
  ·
    refine ⟨51464544508012988454688567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274477570709402605091672357 51464544508012988454688567)
    ·
      refine ⟨77196816762019482682032851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51464544508012988454688567 77196816762019482682032851)
      ·
        refine ⟨115795225143029224023049277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77196816762019482682032851 115795225143029224023049277)
        ·
          refine ⟨43423209428635959008643479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115795225143029224023049277 43423209428635959008643479)
          ·
            refine ⟨65134814142953938512965219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43423209428635959008643479 65134814142953938512965219)
            ·
              refine ⟨97702221214430907769447829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65134814142953938512965219 97702221214430907769447829)
              ·
                refine ⟨4579791619426448801692867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97702221214430907769447829 4579791619426448801692867)
                ·
                  refine ⟨6869687429139673202539301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579791619426448801692867 6869687429139673202539301)
                  ·
                    refine ⟨1288066392963688725476119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6869687429139673202539301 1288066392963688725476119)
                    ·
                      rfl

theorem cell23_7525501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_7525501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525501 prefixEnd_7525501 := by exact prefixLift 7525501
  have htrace : WordTrace (prefixWord ++ tailWord_7525501) baseStart_7525501 baseEnd_7525501 := by
    simpa [prefixWord, tailWord_7525501, baseEnd_7525501] using wordTrace_append hprefix tailTrace_7525501
  have hstable : (prefixWord ++ tailWord_7525501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525501).length < 2 ^ (prefixWord ++ tailWord_7525501).sum := by decide
  have hdescent : baseEnd_7525501 < baseStart_7525501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525535 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 1, 4]
def baseStart_7525535 : Nat := 118140960795 + 7525535 * 2 ^ 59
def prefixEnd_7525535 : Nat := 4983230072969 + 3 ^ 40 * 7525535 * 2
def baseEnd_7525535 : Nat := 1288072212411106347801067

theorem tailTrace_7525535 : CollatzResearch.WordTrace tailWord_7525535 prefixEnd_7525535 1288072212411106347801067 := by
  unfold tailWord_7525535
  simp only [CollatzResearch.WordTrace]
  refine ⟨274478810791279428898410059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182985873860852952598940039 274478810791279428898410059)
  ·
    refine ⟨411718216186919143347615089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274478810791279428898410059 411718216186919143347615089)
    ·
      refine ⟨308788662140189357510711317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411718216186919143347615089 308788662140189357510711317)
      ·
        refine ⟨14474468537821376133314593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308788662140189357510711317 14474468537821376133314593)
        ·
          refine ⟨10855851403366032099985945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14474468537821376133314593 10855851403366032099985945)
          ·
            refine ⟨8141888552524524074989459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10855851403366032099985945 8141888552524524074989459)
            ·
              refine ⟨12212832828786786112484189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141888552524524074989459 12212832828786786112484189)
              ·
                refine ⟨4579812310795044792181571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12212832828786786112484189 4579812310795044792181571)
                ·
                  refine ⟨6869718466192567188272357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4579812310795044792181571 6869718466192567188272357)
                  ·
                    refine ⟨1288072212411106347801067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6869718466192567188272357 1288072212411106347801067)
                    ·
                      rfl

theorem cell23_7525535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 4].length) (baseStart_7525535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525535 prefixEnd_7525535 := by exact prefixLift 7525535
  have htrace : WordTrace (prefixWord ++ tailWord_7525535) baseStart_7525535 baseEnd_7525535 := by
    simpa [prefixWord, tailWord_7525535, baseEnd_7525535] using wordTrace_append hprefix tailTrace_7525535
  have hstable : (prefixWord ++ tailWord_7525535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525535).length < 2 ^ (prefixWord ++ tailWord_7525535).sum := by decide
  have hdescent : baseEnd_7525535 < baseStart_7525535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525601 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_7525601 : Nat := 118140960795 + 7525601 * 2 ^ 59
def prefixEnd_7525601 : Nat := 4983230072969 + 3 ^ 40 * 7525601 * 2
def baseEnd_7525601 : Nat := 3864250526956515785177897

theorem tailTrace_7525601 : CollatzResearch.WordTrace tailWord_7525601 prefixEnd_7525601 3864250526956515785177897 := by
  unfold tailWord_7525601
  simp only [CollatzResearch.WordTrace]
  refine ⟨274481218009040322170312657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182987478672693548113541771 274481218009040322170312657)
  ·
    refine ⟨205860913506780241627734493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274481218009040322170312657 205860913506780241627734493)
    ·
      refine ⟨77197842565042590610400435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205860913506780241627734493 77197842565042590610400435)
      ·
        refine ⟨115796763847563885915600653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77197842565042590610400435 115796763847563885915600653)
        ·
          refine ⟨43423786442836457218350245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115796763847563885915600653 43423786442836457218350245)
          ·
            refine ⟨8141959958031835728440671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43423786442836457218350245 8141959958031835728440671)
            ·
              refine ⟨12212939937047753592661007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141959958031835728440671 12212939937047753592661007)
              ·
                refine ⟨18319409905571630388991511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12212939937047753592661007 18319409905571630388991511)
                ·
                  refine ⟨27479114858357445583487267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18319409905571630388991511 27479114858357445583487267)
                  ·
                    refine ⟨41218672287536168375230901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27479114858357445583487267 41218672287536168375230901)
                    ·
                      refine ⟨3864250526956515785177897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41218672287536168375230901 3864250526956515785177897)
                      ·
                        rfl

theorem cell23_7525601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_7525601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525601 prefixEnd_7525601 := by exact prefixLift 7525601
  have htrace : WordTrace (prefixWord ++ tailWord_7525601) baseStart_7525601 baseEnd_7525601 := by
    simpa [prefixWord, tailWord_7525601, baseEnd_7525601] using wordTrace_append hprefix tailTrace_7525601
  have hstable : (prefixWord ++ tailWord_7525601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525601).length < 2 ^ (prefixWord ++ tailWord_7525601).sum := by decide
  have hdescent : baseEnd_7525601 < baseStart_7525601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525631 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_7525631 : Nat := 118140960795 + 7525631 * 2 ^ 59
def prefixEnd_7525631 : Nat := 4983230072969 + 3 ^ 40 * 7525631 * 2
def baseEnd_7525631 : Nat := 3864265931376150667802759

theorem tailTrace_7525631 : CollatzResearch.WordTrace tailWord_7525631 prefixEnd_7525631 3864265931376150667802759 := by
  unfold tailWord_7525631
  simp only [CollatzResearch.WordTrace]
  refine ⟨274482312198931637293904747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182988208132621091529269831 274482312198931637293904747)
  ·
    refine ⟨411723468298397455940857121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274482312198931637293904747 411723468298397455940857121)
    ·
      refine ⟨308792601223798091955642841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411723468298397455940857121 308792601223798091955642841)
      ·
        refine ⟨231594450917848568966732131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308792601223798091955642841 231594450917848568966732131)
        ·
          refine ⟨347391676376772853450098197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231594450917848568966732131 347391676376772853450098197)
          ·
            refine ⟨16283984830161227505473353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 347391676376772853450098197 16283984830161227505473353)
            ·
              refine ⟨12212988622620920629105015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16283984830161227505473353 12212988622620920629105015)
              ·
                refine ⟨18319482933931380943657523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12212988622620920629105015 18319482933931380943657523)
                ·
                  refine ⟨27479224400897071415486285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18319482933931380943657523 27479224400897071415486285)
                  ·
                    refine ⟨10304709150336401780807357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27479224400897071415486285 10304709150336401780807357)
                    ·
                      refine ⟨3864265931376150667802759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10304709150336401780807357 3864265931376150667802759)
                      ·
                        rfl

theorem cell23_7525631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_7525631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525631 prefixEnd_7525631 := by exact prefixLift 7525631
  have htrace : WordTrace (prefixWord ++ tailWord_7525631) baseStart_7525631 baseEnd_7525631 := by
    simpa [prefixWord, tailWord_7525631, baseEnd_7525631] using wordTrace_append hprefix tailTrace_7525631
  have hstable : (prefixWord ++ tailWord_7525631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525631).length < 2 ^ (prefixWord ++ tailWord_7525631).sum := by decide
  have hdescent : baseEnd_7525631 < baseStart_7525631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525641 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 3, 3, 2]
def baseStart_7525641 : Nat := 118140960795 + 7525641 * 2 ^ 59
def prefixEnd_7525641 : Nat := 4983230072969 + 3 ^ 40 * 7525641 * 2
def baseEnd_7525641 : Nat := 3864271066182695628677713

theorem tailTrace_7525641 : CollatzResearch.WordTrace tailWord_7525641 prefixEnd_7525641 3864271066182695628677713 := by
  unfold tailWord_7525641
  simp only [CollatzResearch.WordTrace]
  refine ⟨274482676928895409001768777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182988451285930272667845851 274482676928895409001768777)
  ·
    refine ⟨205862007696671556751326583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274482676928895409001768777 205862007696671556751326583)
    ·
      refine ⟨308793011545007335126989875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205862007696671556751326583 308793011545007335126989875)
      ·
        refine ⟨463189517317511002690484813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308793011545007335126989875 463189517317511002690484813)
        ·
          refine ⟨173696068994066626008931805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463189517317511002690484813 173696068994066626008931805)
          ·
            refine ⟨65136025872774984753349427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173696068994066626008931805 65136025872774984753349427)
            ·
              refine ⟨97704038809162477130024141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65136025872774984753349427 97704038809162477130024141)
              ·
                refine ⟨36639014553435928923759053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97704038809162477130024141 36639014553435928923759053)
                ·
                  refine ⟨13739630457538473346409645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36639014553435928923759053 13739630457538473346409645)
                  ·
                    refine ⟨5152361421576927504903617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13739630457538473346409645 5152361421576927504903617)
                    ·
                      refine ⟨3864271066182695628677713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152361421576927504903617 3864271066182695628677713)
                      ·
                        rfl

theorem cell23_7525641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3, 2].length) (baseStart_7525641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525641 prefixEnd_7525641 := by exact prefixLift 7525641
  have htrace : WordTrace (prefixWord ++ tailWord_7525641) baseStart_7525641 baseEnd_7525641 := by
    simpa [prefixWord, tailWord_7525641, baseEnd_7525641] using wordTrace_append hprefix tailTrace_7525641
  have hstable : (prefixWord ++ tailWord_7525641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525641).length < 2 ^ (prefixWord ++ tailWord_7525641).sum := by decide
  have hdescent : baseEnd_7525641 < baseStart_7525641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525805 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7525805 : Nat := 118140960795 + 7525805 * 2 ^ 59
def prefixEnd_7525805 : Nat := 4983230072969 + 3 ^ 40 * 7525805 * 2
def baseEnd_7525805 : Nat := 1288118425670010995675653

theorem tailTrace_7525805 : CollatzResearch.WordTrace tailWord_7525805 prefixEnd_7525805 1288118425670010995675653 := by
  unfold tailWord_7525805
  simp only [CollatzResearch.WordTrace]
  refine ⟨274488658500301265010738869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182992439000200843340492579 274488658500301265010738869)
  ·
    refine ⟨25733311734403243594756769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274488658500301265010738869 25733311734403243594756769)
    ·
      refine ⟨19299983800802432696067577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25733311734403243594756769 19299983800802432696067577)
      ·
        refine ⟨14474987850601824522050683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19299983800802432696067577 14474987850601824522050683)
        ·
          refine ⟨21712481775902736783076025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14474987850601824522050683 21712481775902736783076025)
          ·
            refine ⟨16284361331927052587307019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21712481775902736783076025 16284361331927052587307019)
            ·
              refine ⟨24426541997890578880960529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16284361331927052587307019 24426541997890578880960529)
              ·
                refine ⟨18319906498417934160720397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24426541997890578880960529 18319906498417934160720397)
                ·
                  refine ⟨6869964936906725310270149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18319906498417934160720397 6869964936906725310270149)
                  ·
                    refine ⟨1288118425670010995675653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6869964936906725310270149 1288118425670010995675653)
                    ·
                      rfl

theorem cell23_7525805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7525805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525805 prefixEnd_7525805 := by exact prefixLift 7525805
  have htrace : WordTrace (prefixWord ++ tailWord_7525805) baseStart_7525805 baseEnd_7525805 := by
    simpa [prefixWord, tailWord_7525805, baseEnd_7525805] using wordTrace_append hprefix tailTrace_7525805
  have hstable : (prefixWord ++ tailWord_7525805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525805).length < 2 ^ (prefixWord ++ tailWord_7525805).sum := by decide
  have hdescent : baseEnd_7525805 < baseStart_7525805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525845 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_7525845 : Nat := 118140960795 + 7525845 * 2 ^ 59
def prefixEnd_7525845 : Nat := 4983230072969 + 3 ^ 40 * 7525845 * 2
def baseEnd_7525845 : Nat := 3864375816236212830526775

theorem tailTrace_7525845 : CollatzResearch.WordTrace tailWord_7525845 prefixEnd_7525845 3864375816236212830526775 := by
  unfold tailWord_7525845
  simp only [CollatzResearch.WordTrace]
  refine ⟨274490117420156351842194989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182993411613437567894796659 274490117420156351842194989)
  ·
    refine ⟨102933794032558631940823121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274490117420156351842194989 102933794032558631940823121)
    ·
      refine ⟨77200345524418973955617341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102933794032558631940823121 77200345524418973955617341)
      ·
        refine ⟨28950129571657115233356503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77200345524418973955617341 28950129571657115233356503)
        ·
          refine ⟨43425194357485672850034755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28950129571657115233356503 43425194357485672850034755)
          ·
            refine ⟨65137791536228509275052133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43425194357485672850034755 65137791536228509275052133)
            ·
              refine ⟨12213335913042845489072275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65137791536228509275052133 12213335913042845489072275)
              ·
                refine ⟨18320003869564268233608413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12213335913042845489072275 18320003869564268233608413)
                ·
                  refine ⟨6870001451086600587603155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18320003869564268233608413 6870001451086600587603155)
                  ·
                    refine ⟨10305002176629900881404733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6870001451086600587603155 10305002176629900881404733)
                    ·
                      refine ⟨3864375816236212830526775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10305002176629900881404733 3864375816236212830526775)
                      ·
                        rfl

theorem cell23_7525845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_7525845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525845 prefixEnd_7525845 := by exact prefixLift 7525845
  have htrace : WordTrace (prefixWord ++ tailWord_7525845) baseStart_7525845 baseEnd_7525845 := by
    simpa [prefixWord, tailWord_7525845, baseEnd_7525845] using wordTrace_append hprefix tailTrace_7525845
  have hstable : (prefixWord ++ tailWord_7525845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525845).length < 2 ^ (prefixWord ++ tailWord_7525845).sum := by decide
  have hdescent : baseEnd_7525845 < baseStart_7525845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525881 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7525881 : Nat := 118140960795 + 7525881 * 2 ^ 59
def prefixEnd_7525881 : Nat := 4983230072969 + 3 ^ 40 * 7525881 * 2
def baseEnd_7525881 : Nat := 3864394301539774689676609

theorem tailTrace_7525881 : CollatzResearch.WordTrace tailWord_7525881 prefixEnd_7525881 3864394301539774689676609 := by
  unfold tailWord_7525881
  simp only [CollatzResearch.WordTrace]
  refine ⟨274491430448025929990505497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182994286965350619993670331 274491430448025929990505497)
  ·
    refine ⟨205868572836019447492879123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274491430448025929990505497 205868572836019447492879123)
    ·
      refine ⟨308802859254029171239318685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205868572836019447492879123 308802859254029171239318685)
      ·
        refine ⟨115801072220260939214744507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308802859254029171239318685 115801072220260939214744507)
        ·
          refine ⟨173701608330391408822116761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115801072220260939214744507 173701608330391408822116761)
          ·
            refine ⟨130276206247793556616587571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173701608330391408822116761 130276206247793556616587571)
            ·
              refine ⟨195414309371690334924881357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130276206247793556616587571 195414309371690334924881357)
              ·
                refine ⟨73280366014383875596830509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195414309371690334924881357 73280366014383875596830509)
                ·
                  refine ⟨27480137255393953348811441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73280366014383875596830509 27480137255393953348811441)
                  ·
                    refine ⟨20610102941545465011608581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27480137255393953348811441 20610102941545465011608581)
                    ·
                      refine ⟨3864394301539774689676609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20610102941545465011608581 3864394301539774689676609)
                      ·
                        rfl

theorem cell23_7525881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7525881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525881 prefixEnd_7525881 := by exact prefixLift 7525881
  have htrace : WordTrace (prefixWord ++ tailWord_7525881) baseStart_7525881 baseEnd_7525881 := by
    simpa [prefixWord, tailWord_7525881, baseEnd_7525881] using wordTrace_append hprefix tailTrace_7525881
  have hstable : (prefixWord ++ tailWord_7525881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525881).length < 2 ^ (prefixWord ++ tailWord_7525881).sum := by decide
  have hdescent : baseEnd_7525881 < baseStart_7525881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525961 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_7525961 : Nat := 118140960795 + 7525961 * 2 ^ 59
def prefixEnd_7525961 : Nat := 4983230072969 + 3 ^ 40 * 7525961 * 2
def baseEnd_7525961 : Nat := 3864435379992134376676241

theorem tailTrace_7525961 : CollatzResearch.WordTrace tailWord_7525961 prefixEnd_7525961 3864435379992134376676241 := by
  unfold tailWord_7525961
  simp only [CollatzResearch.WordTrace]
  refine ⟨274494348287736103653417737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182996232191824069102278491 274494348287736103653417737)
  ·
    refine ⟨205870761215802077740063303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274494348287736103653417737 205870761215802077740063303)
    ·
      refine ⟨308806141823703116610094955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205870761215802077740063303 308806141823703116610094955)
      ·
        refine ⟨463209212735554674915142433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308806141823703116610094955 463209212735554674915142433)
        ·
          refine ⟨347406909551666006186356825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463209212735554674915142433 347406909551666006186356825)
          ·
            refine ⟨260555182163749504639767619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347406909551666006186356825 260555182163749504639767619)
            ·
              refine ⟨390832773245624256959651429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260555182163749504639767619 390832773245624256959651429)
              ·
                refine ⟨73281144983554548179934643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390832773245624256959651429 73281144983554548179934643)
                ·
                  refine ⟨109921717475331822269901965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73281144983554548179934643 109921717475331822269901965)
                  ·
                    refine ⟨41220644053249433351213237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109921717475331822269901965 41220644053249433351213237)
                    ·
                      refine ⟨3864435379992134376676241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41220644053249433351213237 3864435379992134376676241)
                      ·
                        rfl

theorem cell23_7525961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_7525961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525961 prefixEnd_7525961 := by exact prefixLift 7525961
  have htrace : WordTrace (prefixWord ++ tailWord_7525961) baseStart_7525961 baseEnd_7525961 := by
    simpa [prefixWord, tailWord_7525961, baseEnd_7525961] using wordTrace_append hprefix tailTrace_7525961
  have hstable : (prefixWord ++ tailWord_7525961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525961).length < 2 ^ (prefixWord ++ tailWord_7525961).sum := by decide
  have hdescent : baseEnd_7525961 < baseStart_7525961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525975 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_7525975 : Nat := 118140960795 + 7525975 * 2 ^ 59
def prefixEnd_7525975 : Nat := 4983230072969 + 3 ^ 40 * 7525975 * 2
def baseEnd_7525975 : Nat := 3864442568721297321901177

theorem tailTrace_7525975 : CollatzResearch.WordTrace tailWord_7525975 prefixEnd_7525975 3864442568721297321901177 := by
  unfold tailWord_7525975
  simp only [CollatzResearch.WordTrace]
  refine ⟨274494858909685384044427379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182996572606456922696284919 274494858909685384044427379)
  ·
    refine ⟨411742288364528076066641069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274494858909685384044427379 411742288364528076066641069)
    ·
      refine ⟨154403358136698028524990401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411742288364528076066641069 154403358136698028524990401)
      ·
        refine ⟨115802518602523521393742801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154403358136698028524990401 115802518602523521393742801)
        ·
          refine ⟨86851888951892641045307101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115802518602523521393742801 86851888951892641045307101)
          ·
            refine ⟨32569458356959740391990163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86851888951892641045307101 32569458356959740391990163)
            ·
              refine ⟨48854187535439610587985245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32569458356959740391990163 48854187535439610587985245)
              ·
                refine ⟨18320320325789853970494467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48854187535439610587985245 18320320325789853970494467)
                ·
                  refine ⟨27480480488684780955741701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18320320325789853970494467 27480480488684780955741701)
                  ·
                    refine ⟨5152590091628396429201569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27480480488684780955741701 5152590091628396429201569)
                    ·
                      refine ⟨3864442568721297321901177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152590091628396429201569 3864442568721297321901177)
                      ·
                        rfl

theorem cell23_7525975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_7525975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525975 prefixEnd_7525975 := by exact prefixLift 7525975
  have htrace : WordTrace (prefixWord ++ tailWord_7525975) baseStart_7525975 baseEnd_7525975 := by
    simpa [prefixWord, tailWord_7525975, baseEnd_7525975] using wordTrace_append hprefix tailTrace_7525975
  have hstable : (prefixWord ++ tailWord_7525975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525975).length < 2 ^ (prefixWord ++ tailWord_7525975).sum := by decide
  have hdescent : baseEnd_7525975 < baseStart_7525975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7525992 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7525992 : Nat := 118140960795 + 7525992 * 2 ^ 59
def prefixEnd_7525992 : Nat := 4983230072969 + 3 ^ 40 * 7525992 * 2
def baseEnd_7525992 : Nat := 3864451297892423755388599

theorem tailTrace_7525992 : CollatzResearch.WordTrace tailWord_7525992 prefixEnd_7525992 3864451297892423755388599 := by
  unfold tailWord_7525992
  simp only [CollatzResearch.WordTrace]
  refine ⟨137247739475311897973898115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182996985967082530631864153 137247739475311897973898115)
  ·
    refine ⟨205871609212967846960847173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137247739475311897973898115 205871609212967846960847173)
    ·
      refine ⟨38600926727431471305158845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205871609212967846960847173 38600926727431471305158845)
      ·
        refine ⟨14475347522786801739434567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38600926727431471305158845 14475347522786801739434567)
        ·
          refine ⟨21713021284180202609151851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475347522786801739434567 21713021284180202609151851)
          ·
            refine ⟨32569531926270303913727777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713021284180202609151851 32569531926270303913727777)
            ·
              refine ⟨24427148944702727935295833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32569531926270303913727777 24427148944702727935295833)
              ·
                refine ⟨18320361708527045951471875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24427148944702727935295833 18320361708527045951471875)
                ·
                  refine ⟨27480542562790568927207813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18320361708527045951471875 27480542562790568927207813)
                  ·
                    refine ⟨5152601730523231673851465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27480542562790568927207813 5152601730523231673851465)
                    ·
                      refine ⟨3864451297892423755388599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152601730523231673851465 3864451297892423755388599)
                      ·
                        rfl

theorem cell23_7525992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7525992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7525992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7525992 prefixEnd_7525992 := by exact prefixLift 7525992
  have htrace : WordTrace (prefixWord ++ tailWord_7525992) baseStart_7525992 baseEnd_7525992 := by
    simpa [prefixWord, tailWord_7525992, baseEnd_7525992] using wordTrace_append hprefix tailTrace_7525992
  have hstable : (prefixWord ++ tailWord_7525992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7525992).length < 2 ^ (prefixWord ++ tailWord_7525992).sum := by decide
  have hdescent : baseEnd_7525992 < baseStart_7525992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7525992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526005 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7526005 : Nat := 118140960795 + 7526005 * 2 ^ 59
def prefixEnd_7526005 : Nat := 4983230072969 + 3 ^ 40 * 7526005 * 2
def baseEnd_7526005 : Nat := 3864457973140932204526039

theorem tailTrace_7526005 : CollatzResearch.WordTrace tailWord_7526005 prefixEnd_7526005 3864457973140932204526039 := by
  unfold tailWord_7526005
  simp only [CollatzResearch.WordTrace]
  refine ⟨274495953099576699168019469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182997302066384466112012979 274495953099576699168019469)
  ·
    refine ⟨102935982412341262188007301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274495953099576699168019469 102935982412341262188007301)
    ·
      refine ⟨19300496702313986660251369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102935982412341262188007301 19300496702313986660251369)
      ·
        refine ⟨14475372526735489995188527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19300496702313986660251369 14475372526735489995188527)
        ·
          refine ⟨21713058790103234992782791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475372526735489995188527 21713058790103234992782791)
          ·
            refine ⟨32569588185154852489174187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713058790103234992782791 32569588185154852489174187)
            ·
              refine ⟨48854382277732278733761281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32569588185154852489174187 48854382277732278733761281)
              ·
                refine ⟨36640786708299209050320961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48854382277732278733761281 36640786708299209050320961)
                ·
                  refine ⟨27480590031224406787740721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36640786708299209050320961 27480590031224406787740721)
                  ·
                    refine ⟨20610442523418305090805541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27480590031224406787740721 20610442523418305090805541)
                    ·
                      refine ⟨3864457973140932204526039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20610442523418305090805541 3864457973140932204526039)
                      ·
                        rfl

theorem cell23_7526005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7526005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526005 prefixEnd_7526005 := by exact prefixLift 7526005
  have htrace : WordTrace (prefixWord ++ tailWord_7526005) baseStart_7526005 baseEnd_7526005 := by
    simpa [prefixWord, tailWord_7526005, baseEnd_7526005] using wordTrace_append hprefix tailTrace_7526005
  have hstable : (prefixWord ++ tailWord_7526005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526005).length < 2 ^ (prefixWord ++ tailWord_7526005).sum := by decide
  have hdescent : baseEnd_7526005 < baseStart_7526005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526026 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_7526026 : Nat := 118140960795 + 7526026 * 2 ^ 59
def prefixEnd_7526026 : Nat := 4983230072969 + 3 ^ 40 * 7526026 * 2
def baseEnd_7526026 : Nat := 3864468756234676622363443

theorem tailTrace_7526026 : CollatzResearch.WordTrace tailWord_7526026 prefixEnd_7526026 3864468756234676622363443 := by
  unfold tailWord_7526026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68624179758125154938633483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182997812688333746503022621 68624179758125154938633483)
  ·
    refine ⟨102936269637187732407950225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68624179758125154938633483 102936269637187732407950225)
    ·
      refine ⟨77202202227890799305962669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102936269637187732407950225 77202202227890799305962669)
      ·
        refine ⟨28950825835459049739736001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77202202227890799305962669 28950825835459049739736001)
        ·
          refine ⟨21713119376594287304802001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28950825835459049739736001 21713119376594287304802001)
          ·
            refine ⟨16284839532445715478601501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21713119376594287304802001 16284839532445715478601501)
            ·
              refine ⟨6106814824667143304475563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16284839532445715478601501 6106814824667143304475563)
              ·
                refine ⟨9160222237000714956713345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106814824667143304475563 9160222237000714956713345)
                ·
                  refine ⟨6870166677750536217535009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9160222237000714956713345 6870166677750536217535009)
                  ·
                    refine ⟨5152625008312902163151257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6870166677750536217535009 5152625008312902163151257)
                    ·
                      refine ⟨3864468756234676622363443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152625008312902163151257 3864468756234676622363443)
                      ·
                        rfl

theorem cell23_7526026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_7526026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526026 prefixEnd_7526026 := by exact prefixLift 7526026
  have htrace : WordTrace (prefixWord ++ tailWord_7526026) baseStart_7526026 baseEnd_7526026 := by
    simpa [prefixWord, tailWord_7526026, baseEnd_7526026] using wordTrace_append hprefix tailTrace_7526026
  have hstable : (prefixWord ++ tailWord_7526026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526026).length < 2 ^ (prefixWord ++ tailWord_7526026).sum := by decide
  have hdescent : baseEnd_7526026 < baseStart_7526026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526155 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4]
def baseStart_7526155 : Nat := 118140960795 + 7526155 * 2 ^ 59
def prefixEnd_7526155 : Nat := 4983230072969 + 3 ^ 40 * 7526155 * 2
def baseEnd_7526155 : Nat := 3864534995239106617650349

theorem tailTrace_7526155 : CollatzResearch.WordTrace tailWord_7526155 prefixEnd_7526155 3864534995239106617650349 := by
  unfold tailWord_7526155
  simp only [CollatzResearch.WordTrace]
  refine ⟨274501424049033274785979919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183000949366022183190653279 274501424049033274785979919)
  ·
    refine ⟨411752136073549912178969879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274501424049033274785979919 411752136073549912178969879)
    ·
      refine ⟨617628204110324868268454819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411752136073549912178969879 617628204110324868268454819)
      ·
        refine ⟨926442306165487302402682229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617628204110324868268454819 926442306165487302402682229)
        ·
          refine ⟨86853966203014434600251459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 926442306165487302402682229 86853966203014434600251459)
          ·
            refine ⟨130280949304521651900377189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86853966203014434600251459 130280949304521651900377189)
            ·
              refine ⟨24427677994597809731320723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130280949304521651900377189 24427677994597809731320723)
              ·
                refine ⟨36641516991896714596981085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24427677994597809731320723 36641516991896714596981085)
                ·
                  refine ⟨13740568871961267973867907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36641516991896714596981085 13740568871961267973867907)
                  ·
                    refine ⟨20610853307941901960801861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13740568871961267973867907 20610853307941901960801861)
                    ·
                      refine ⟨3864534995239106617650349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20610853307941901960801861 3864534995239106617650349)
                      ·
                        rfl

theorem cell23_7526155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4].length) (baseStart_7526155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526155 prefixEnd_7526155 := by exact prefixLift 7526155
  have htrace : WordTrace (prefixWord ++ tailWord_7526155) baseStart_7526155 baseEnd_7526155 := by
    simpa [prefixWord, tailWord_7526155, baseEnd_7526155] using wordTrace_append hprefix tailTrace_7526155
  have hstable : (prefixWord ++ tailWord_7526155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526155).length < 2 ^ (prefixWord ++ tailWord_7526155).sum := by decide
  have hdescent : baseEnd_7526155 < baseStart_7526155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526165 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7526165 : Nat := 118140960795 + 7526165 * 2 ^ 59
def prefixEnd_7526165 : Nat := 4983230072969 + 3 ^ 40 * 7526165 * 2
def baseEnd_7526165 : Nat := 1288180043348550526175101

theorem tailTrace_7526165 : CollatzResearch.WordTrace tailWord_7526165 prefixEnd_7526165 1288180043348550526175101 := by
  unfold tailWord_7526165
  simp only [CollatzResearch.WordTrace]
  refine ⟨274501788778997046493843949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183001192519331364329229299 274501788778997046493843949)
  ·
    refine ⟨102938170792123892435191481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274501788778997046493843949 102938170792123892435191481)
    ·
      refine ⟨77203628094092919326393611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102938170792123892435191481 77203628094092919326393611)
      ·
        refine ⟨115805442141139378989590417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77203628094092919326393611 115805442141139378989590417)
        ·
          refine ⟨86854081605854534242192813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115805442141139378989590417 86854081605854534242192813)
          ·
            refine ⟨32570280602195450340822305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86854081605854534242192813 32570280602195450340822305)
            ·
              refine ⟨24427710451646587755616729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32570280602195450340822305 24427710451646587755616729)
              ·
                refine ⟨18320782838734940816712547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24427710451646587755616729 18320782838734940816712547)
                ·
                  refine ⟨27481174258102411225068821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18320782838734940816712547 27481174258102411225068821)
                  ·
                    refine ⟨1288180043348550526175101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27481174258102411225068821 1288180043348550526175101)
                    ·
                      rfl

theorem cell23_7526165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7526165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526165 prefixEnd_7526165 := by exact prefixLift 7526165
  have htrace : WordTrace (prefixWord ++ tailWord_7526165) baseStart_7526165 baseEnd_7526165 := by
    simpa [prefixWord, tailWord_7526165, baseEnd_7526165] using wordTrace_append hprefix tailTrace_7526165
  have hstable : (prefixWord ++ tailWord_7526165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526165).length < 2 ^ (prefixWord ++ tailWord_7526165).sum := by decide
  have hdescent : baseEnd_7526165 < baseStart_7526165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526172 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_7526172 : Nat := 118140960795 + 7526172 * 2 ^ 59
def prefixEnd_7526172 : Nat := 4983230072969 + 3 ^ 40 * 7526172 * 2
def baseEnd_7526172 : Nat := 3864543724410233051137771

theorem tailTrace_7526172 : CollatzResearch.WordTrace tailWord_7526172 prefixEnd_7526172 3864543724410233051137771 := by
  unfold tailWord_7526172
  simp only [CollatzResearch.WordTrace]
  refine ⟨137251022044985843344674385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183001362726647791126232513 137251022044985843344674385)
  ·
    refine ⟨102938266533739382508505789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137251022044985843344674385 102938266533739382508505789)
    ·
      refine ⟨38601849950152268440689671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102938266533739382508505789 38601849950152268440689671)
      ·
        refine ⟨57902774925228402661034507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38601849950152268440689671 57902774925228402661034507)
        ·
          refine ⟨86854162387842603991551761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57902774925228402661034507 86854162387842603991551761)
          ·
            refine ⟨65140621790881952993663821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86854162387842603991551761 65140621790881952993663821)
            ·
              refine ⟨24427733171580732372623933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65140621790881952993663821 24427733171580732372623933)
              ·
                refine ⟨9160399939342774639733975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24427733171580732372623933 9160399939342774639733975)
                ·
                  refine ⟨13740599909014161959600963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9160399939342774639733975 13740599909014161959600963)
                  ·
                    refine ⟨20610899863521242939401445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13740599909014161959600963 20610899863521242939401445)
                    ·
                      refine ⟨3864543724410233051137771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20610899863521242939401445 3864543724410233051137771)
                      ·
                        rfl

theorem cell23_7526172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_7526172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526172 prefixEnd_7526172 := by exact prefixLift 7526172
  have htrace : WordTrace (prefixWord ++ tailWord_7526172) baseStart_7526172 baseEnd_7526172 := by
    simpa [prefixWord, tailWord_7526172, baseEnd_7526172] using wordTrace_append hprefix tailTrace_7526172
  have hstable : (prefixWord ++ tailWord_7526172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526172).length < 2 ^ (prefixWord ++ tailWord_7526172).sum := by decide
  have hdescent : baseEnd_7526172 < baseStart_7526172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526175 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7526175 : Nat := 118140960795 + 7526175 * 2 ^ 59
def prefixEnd_7526175 : Nat := 4983230072969 + 3 ^ 40 * 7526175 * 2
def baseEnd_7526175 : Nat := 3864545264852196539400257

theorem tailTrace_7526175 : CollatzResearch.WordTrace tailWord_7526175 prefixEnd_7526175 3864545264852196539400257 := by
  unfold tailWord_7526175
  simp only [CollatzResearch.WordTrace]
  refine ⟨274502153508960818201707979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183001435672640545467805319 274502153508960818201707979)
  ·
    refine ⟨411753230263441227302561969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274502153508960818201707979 411753230263441227302561969)
    ·
      refine ⟨308814922697580920476921477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411753230263441227302561969 308814922697580920476921477)
      ·
        refine ⟨57902798005796422589422777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308814922697580920476921477 57902798005796422589422777)
        ·
          refine ⟨43427098504347316942067083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57902798005796422589422777 43427098504347316942067083)
          ·
            refine ⟨65140647756520975413100625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43427098504347316942067083 65140647756520975413100625)
            ·
              refine ⟨48855485817390731559825469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65140647756520975413100625 48855485817390731559825469)
              ·
                refine ⟨18320807181521524334934551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48855485817390731559825469 18320807181521524334934551)
                ·
                  refine ⟨27481210772282286502401827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18320807181521524334934551 27481210772282286502401827)
                  ·
                    refine ⟨41221816158423429753602741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27481210772282286502401827 41221816158423429753602741)
                    ·
                      refine ⟨3864545264852196539400257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41221816158423429753602741 3864545264852196539400257)
                      ·
                        rfl

theorem cell23_7526175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7526175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526175 prefixEnd_7526175 := by exact prefixLift 7526175
  have htrace : WordTrace (prefixWord ++ tailWord_7526175) baseStart_7526175 baseEnd_7526175 := by
    simpa [prefixWord, tailWord_7526175, baseEnd_7526175] using wordTrace_append hprefix tailTrace_7526175
  have hstable : (prefixWord ++ tailWord_7526175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526175).length < 2 ^ (prefixWord ++ tailWord_7526175).sum := by decide
  have hdescent : baseEnd_7526175 < baseStart_7526175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526202 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_7526202 : Nat := 118140960795 + 7526202 * 2 ^ 59
def prefixEnd_7526202 : Nat := 4983230072969 + 3 ^ 40 * 7526202 * 2
def baseEnd_7526202 : Nat := 3864559128829867933762633

theorem tailTrace_7526202 : CollatzResearch.WordTrace tailWord_7526202 prefixEnd_7526202 3864559128829867933762633 := by
  unfold tailWord_7526202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68625784569965750453235215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183002092186575334541960573 68625784569965750453235215)
  ·
    refine ⟨102938676854948625679852823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68625784569965750453235215 102938676854948625679852823)
    ·
      refine ⟨154408015282422938519779235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102938676854948625679852823 154408015282422938519779235)
      ·
        refine ⟨231612022923634407779668853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154408015282422938519779235 231612022923634407779668853)
        ·
          refine ⟨21713627149090725729343955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231612022923634407779668853 21713627149090725729343955)
          ·
            refine ⟨32570440723636088594015933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713627149090725729343955 32570440723636088594015933)
            ·
              refine ⟨12213915271363533222755975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32570440723636088594015933 12213915271363533222755975)
              ·
                refine ⟨18320872907045299834133963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12213915271363533222755975 18320872907045299834133963)
                ·
                  refine ⟨27481309360567949751200945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18320872907045299834133963 27481309360567949751200945)
                  ·
                    refine ⟨20610982020425962313400709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27481309360567949751200945 20610982020425962313400709)
                    ·
                      refine ⟨3864559128829867933762633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20610982020425962313400709 3864559128829867933762633)
                      ·
                        rfl

theorem cell23_7526202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_7526202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526202 prefixEnd_7526202 := by exact prefixLift 7526202
  have htrace : WordTrace (prefixWord ++ tailWord_7526202) baseStart_7526202 baseEnd_7526202 := by
    simpa [prefixWord, tailWord_7526202, baseEnd_7526202] using wordTrace_append hprefix tailTrace_7526202
  have hstable : (prefixWord ++ tailWord_7526202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526202).length < 2 ^ (prefixWord ++ tailWord_7526202).sum := by decide
  have hdescent : baseEnd_7526202 < baseStart_7526202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526206 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_7526206 : Nat := 118140960795 + 7526206 * 2 ^ 59
def prefixEnd_7526206 : Nat := 4983230072969 + 3 ^ 40 * 7526206 * 2
def baseEnd_7526206 : Nat := 3864561182752485918112615

theorem tailTrace_7526206 : CollatzResearch.WordTrace tailWord_7526206 prefixEnd_7526206 3864561182752485918112615 := by
  unfold tailWord_7526206
  simp only [CollatzResearch.WordTrace]
  refine ⟨34312910521481063812010809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183002189447899006997390981 34312910521481063812010809)
  ·
    refine ⟨25734682891110797859008107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34312910521481063812010809 25734682891110797859008107)
    ·
      refine ⟨38602024336666196788512161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25734682891110797859008107 38602024336666196788512161)
      ·
        refine ⟨28951518252499647591384121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38602024336666196788512161 28951518252499647591384121)
        ·
          refine ⟨21713638689374735693538091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28951518252499647591384121 21713638689374735693538091)
          ·
            refine ⟨32570458034062103540307137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713638689374735693538091 32570458034062103540307137)
            ·
              refine ⟨24427843525546577655230353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32570458034062103540307137 24427843525546577655230353)
              ·
                refine ⟨18320882644159933241422765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24427843525546577655230353 18320882644159933241422765)
                ·
                  refine ⟨6870330991559974965533537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18320882644159933241422765 6870330991559974965533537)
                  ·
                    refine ⟨5152748243669981224150153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6870330991559974965533537 5152748243669981224150153)
                    ·
                      refine ⟨3864561182752485918112615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152748243669981224150153 3864561182752485918112615)
                      ·
                        rfl

theorem cell23_7526206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_7526206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526206 prefixEnd_7526206 := by exact prefixLift 7526206
  have htrace : WordTrace (prefixWord ++ tailWord_7526206) baseStart_7526206 baseEnd_7526206 := by
    simpa [prefixWord, tailWord_7526206, baseEnd_7526206] using wordTrace_append hprefix tailTrace_7526206
  have hstable : (prefixWord ++ tailWord_7526206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526206).length < 2 ^ (prefixWord ++ tailWord_7526206).sum := by decide
  have hdescent : baseEnd_7526206 < baseStart_7526206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526232 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_7526232 : Nat := 118140960795 + 7526232 * 2 ^ 59
def prefixEnd_7526232 : Nat := 4983230072969 + 3 ^ 40 * 7526232 * 2
def baseEnd_7526232 : Nat := 3864574533249502816387495

theorem tailTrace_7526232 : CollatzResearch.WordTrace tailWord_7526232 prefixEnd_7526232 3864574533249502816387495 := by
  unfold tailWord_7526232
  simp only [CollatzResearch.WordTrace]
  refine ⟨137252116234877158468266475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183002821646502877957688633 137252116234877158468266475)
  ·
    refine ⟨205878174352315737702399713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137252116234877158468266475 205878174352315737702399713)
    ·
      refine ⟨154408630764236803276799785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205878174352315737702399713 154408630764236803276799785)
      ·
        refine ⟨115806473073177602457599839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154408630764236803276799785 115806473073177602457599839)
        ·
          refine ⟨173709709609766403686399759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115806473073177602457599839 173709709609766403686399759)
          ·
            refine ⟨260564564414649605529599639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173709709609766403686399759 260564564414649605529599639)
            ·
              refine ⟨390846846621974408294399459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260564564414649605529599639 390846846621974408294399459)
              ·
                refine ⟨586270269932961612441599189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390846846621974408294399459 586270269932961612441599189)
                ·
                  refine ⟨13740709451553787791599981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 586270269932961612441599189 13740709451553787791599981)
                  ·
                    refine ⟨5152766044332670421849993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13740709451553787791599981 5152766044332670421849993)
                    ·
                      refine ⟨3864574533249502816387495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152766044332670421849993 3864574533249502816387495)
                      ·
                        rfl

theorem cell23_7526232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_7526232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526232 prefixEnd_7526232 := by exact prefixLift 7526232
  have htrace : WordTrace (prefixWord ++ tailWord_7526232) baseStart_7526232 baseEnd_7526232 := by
    simpa [prefixWord, tailWord_7526232, baseEnd_7526232] using wordTrace_append hprefix tailTrace_7526232
  have hstable : (prefixWord ++ tailWord_7526232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526232).length < 2 ^ (prefixWord ++ tailWord_7526232).sum := by decide
  have hdescent : baseEnd_7526232 < baseStart_7526232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526245 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7526245 : Nat := 118140960795 + 7526245 * 2 ^ 59
def prefixEnd_7526245 : Nat := 4983230072969 + 3 ^ 40 * 7526245 * 2
def baseEnd_7526245 : Nat := 3864581208498011265524935

theorem tailTrace_7526245 : CollatzResearch.WordTrace tailWord_7526245 prefixEnd_7526245 3864581208498011265524935 := by
  unfold tailWord_7526245
  simp only [CollatzResearch.WordTrace]
  refine ⟨274504706618707220156756189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183003137745804813437837459 274504706618707220156756189)
  ·
    refine ⟨102939264982015207558783571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274504706618707220156756189 102939264982015207558783571)
    ·
      refine ⟨154408897473022811338175357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102939264982015207558783571 154408897473022811338175357)
      ·
        refine ⟨57903336552383554251815759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154408897473022811338175357 57903336552383554251815759)
        ·
          refine ⟨86855004828575331377723639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57903336552383554251815759 86855004828575331377723639)
          ·
            refine ⟨130282507242862997066585459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86855004828575331377723639 130282507242862997066585459)
            ·
              refine ⟨195423760864294495599878189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130282507242862997066585459 195423760864294495599878189)
              ·
                refine ⟨73283910324110435849954321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195423760864294495599878189 73283910324110435849954321)
                ·
                  refine ⟨54962932743082826887465741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73283910324110435849954321 54962932743082826887465741)
                  ·
                    refine ⟨20611099778656060082799653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54962932743082826887465741 20611099778656060082799653)
                    ·
                      refine ⟨3864581208498011265524935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20611099778656060082799653 3864581208498011265524935)
                      ·
                        rfl

theorem cell23_7526245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7526245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526245 prefixEnd_7526245 := by exact prefixLift 7526245
  have htrace : WordTrace (prefixWord ++ tailWord_7526245) baseStart_7526245 baseEnd_7526245 := by
    simpa [prefixWord, tailWord_7526245, baseEnd_7526245] using wordTrace_append hprefix tailTrace_7526245
  have hstable : (prefixWord ++ tailWord_7526245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526245).length < 2 ^ (prefixWord ++ tailWord_7526245).sum := by decide
  have hdescent : baseEnd_7526245 < baseStart_7526245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526250 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_7526250 : Nat := 118140960795 + 7526250 * 2 ^ 59
def prefixEnd_7526250 : Nat := 4983230072969 + 3 ^ 40 * 7526250 * 2
def baseEnd_7526250 : Nat := 1288194591967094581987471

theorem tailTrace_7526250 : CollatzResearch.WordTrace tailWord_7526250 prefixEnd_7526250 1288194591967094581987471 := by
  unfold tailWord_7526250
  simp only [CollatzResearch.WordTrace]
  refine ⟨68626222245922276502672051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183003259322459404007125469 68626222245922276502672051)
  ·
    refine ⟨102939333368883414754008077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68626222245922276502672051 102939333368883414754008077)
    ·
      refine ⟨38602250013331280532753029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102939333368883414754008077 38602250013331280532753029)
      ·
        refine ⟨7237921877499615099891193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38602250013331280532753029 7237921877499615099891193)
        ·
          refine ⟨5428441408124711324918395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7237921877499615099891193 5428441408124711324918395)
          ·
            refine ⟨8142662112187066987377593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428441408124711324918395 8142662112187066987377593)
            ·
              refine ⟨6106996584140300240533195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8142662112187066987377593 6106996584140300240533195)
              ·
                refine ⟨9160494876210450360799793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106996584140300240533195 9160494876210450360799793)
                ·
                  refine ⟨6870371157157837770599845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9160494876210450360799793 6870371157157837770599845)
                  ·
                    refine ⟨1288194591967094581987471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6870371157157837770599845 1288194591967094581987471)
                    ·
                      rfl

theorem cell23_7526250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_7526250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526250 prefixEnd_7526250 := by exact prefixLift 7526250
  have htrace : WordTrace (prefixWord ++ tailWord_7526250) baseStart_7526250 baseEnd_7526250 := by
    simpa [prefixWord, tailWord_7526250, baseEnd_7526250] using wordTrace_append hprefix tailTrace_7526250
  have hstable : (prefixWord ++ tailWord_7526250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526250).length < 2 ^ (prefixWord ++ tailWord_7526250).sum := by decide
  have hdescent : baseEnd_7526250 < baseStart_7526250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526265 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_7526265 : Nat := 118140960795 + 7526265 * 2 ^ 59
def prefixEnd_7526265 : Nat := 4983230072969 + 3 ^ 40 * 7526265 * 2
def baseEnd_7526265 : Nat := 3864591478111101187274843

theorem tailTrace_7526265 : CollatzResearch.WordTrace tailWord_7526265 prefixEnd_7526265 3864591478111101187274843 := by
  unfold tailWord_7526265
  simp only [CollatzResearch.WordTrace]
  refine ⟨274505436078634763572484249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183003624052423175714989499 274505436078634763572484249)
  ·
    refine ⟨205879077058976072679363187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274505436078634763572484249 205879077058976072679363187)
    ·
      refine ⟨308818615588464109019044781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205879077058976072679363187 308818615588464109019044781)
      ·
        refine ⟨115806980845674040882141793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308818615588464109019044781 115806980845674040882141793)
        ·
          refine ⟨86855235634255530661606345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115806980845674040882141793 86855235634255530661606345)
          ·
            refine ⟨65141426725691647996204759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86855235634255530661606345 65141426725691647996204759)
            ·
              refine ⟨97712140088537471994307139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65141426725691647996204759 97712140088537471994307139)
              ·
                refine ⟨146568210132806207991460709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97712140088537471994307139 146568210132806207991460709)
                ·
                  refine ⟨27481539399901163998398883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146568210132806207991460709 27481539399901163998398883)
                  ·
                    refine ⟨41222309099851745997598325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27481539399901163998398883 41222309099851745997598325)
                    ·
                      refine ⟨3864591478111101187274843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41222309099851745997598325 3864591478111101187274843)
                      ·
                        rfl

theorem cell23_7526265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_7526265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526265 prefixEnd_7526265 := by exact prefixLift 7526265
  have htrace : WordTrace (prefixWord ++ tailWord_7526265) baseStart_7526265 baseEnd_7526265 := by
    simpa [prefixWord, tailWord_7526265, baseEnd_7526265] using wordTrace_append hprefix tailTrace_7526265
  have hstable : (prefixWord ++ tailWord_7526265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526265).length < 2 ^ (prefixWord ++ tailWord_7526265).sum := by decide
  have hdescent : baseEnd_7526265 < baseStart_7526265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526352 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_7526352 : Nat := 118140960795 + 7526352 * 2 ^ 59
def prefixEnd_7526352 : Nat := 4983230072969 + 3 ^ 40 * 7526352 * 2
def baseEnd_7526352 : Nat := 3864636150928042346886943

theorem tailTrace_7526352 : CollatzResearch.WordTrace tailWord_7526352 prefixEnd_7526352 3864636150928042346886943 := by
  unfold tailWord_7526352
  simp only [CollatzResearch.WordTrace]
  refine ⟨137254304614659788715450655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183005739486213051620600873 137254304614659788715450655)
  ·
    refine ⟨205881456921989683073175983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137254304614659788715450655 205881456921989683073175983)
    ·
      refine ⟨308822185382984524609763975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205881456921989683073175983 308822185382984524609763975)
      ·
        refine ⟨463233278074476786914645963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308822185382984524609763975 463233278074476786914645963)
        ·
          refine ⟨694849917111715180371968945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463233278074476786914645963 694849917111715180371968945)
          ·
            refine ⟨521137437833786385278976709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694849917111715180371968945 521137437833786385278976709)
            ·
              refine ⟨97713269593834947239808133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 521137437833786385278976709 97713269593834947239808133)
              ·
                refine ⟨18321238048844052607464025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97713269593834947239808133 18321238048844052607464025)
                ·
                  refine ⟨13740928536633039455598019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18321238048844052607464025 13740928536633039455598019)
                  ·
                    refine ⟨20611392804949559183397029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13740928536633039455598019 20611392804949559183397029)
                    ·
                      refine ⟨3864636150928042346886943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20611392804949559183397029 3864636150928042346886943)
                      ·
                        rfl

theorem cell23_7526352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_7526352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526352 prefixEnd_7526352 := by exact prefixLift 7526352
  have htrace : WordTrace (prefixWord ++ tailWord_7526352) baseStart_7526352 baseEnd_7526352 := by
    simpa [prefixWord, tailWord_7526352, baseEnd_7526352] using wordTrace_append hprefix tailTrace_7526352
  have hstable : (prefixWord ++ tailWord_7526352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526352).length < 2 ^ (prefixWord ++ tailWord_7526352).sum := by decide
  have hdescent : baseEnd_7526352 < baseStart_7526352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526364 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7526364 : Nat := 118140960795 + 7526364 * 2 ^ 59
def prefixEnd_7526364 : Nat := 4983230072969 + 3 ^ 40 * 7526364 * 2
def baseEnd_7526364 : Nat := 3864642312695896299936889

theorem tailTrace_7526364 : CollatzResearch.WordTrace tailWord_7526364 prefixEnd_7526364 3864642312695896299936889 := by
  unfold tailWord_7526364
  simp only [CollatzResearch.WordTrace]
  refine ⟨137254523452638051740169073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183006031270184068986892097 137254523452638051740169073)
  ·
    refine ⟨102940892589478538805126805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137254523452638051740169073 102940892589478538805126805)
    ·
      refine ⟨4825354340131806506490319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102940892589478538805126805 4825354340131806506490319)
      ·
        refine ⟨7238031510197709759735479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825354340131806506490319 7238031510197709759735479)
        ·
          refine ⟨10857047265296564639603219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7238031510197709759735479 10857047265296564639603219)
          ·
            refine ⟨16285570897944846959404829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10857047265296564639603219 16285570897944846959404829)
            ·
              refine ⟨6107089086729317609776811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16285570897944846959404829 6107089086729317609776811)
              ·
                refine ⟨9160633630093976414665217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107089086729317609776811 9160633630093976414665217)
                ·
                  refine ⟨6870475222570482310998913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9160633630093976414665217 6870475222570482310998913)
                  ·
                    refine ⟨5152856416927861733249185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6870475222570482310998913 5152856416927861733249185)
                    ·
                      refine ⟨3864642312695896299936889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152856416927861733249185 3864642312695896299936889)
                      ·
                        rfl

theorem cell23_7526364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7526364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526364 prefixEnd_7526364 := by exact prefixLift 7526364
  have htrace : WordTrace (prefixWord ++ tailWord_7526364) baseStart_7526364 baseEnd_7526364 := by
    simpa [prefixWord, tailWord_7526364, baseEnd_7526364] using wordTrace_append hprefix tailTrace_7526364
  have hstable : (prefixWord ++ tailWord_7526364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526364).length < 2 ^ (prefixWord ++ tailWord_7526364).sum := by decide
  have hdescent : baseEnd_7526364 < baseStart_7526364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526369 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_7526369 : Nat := 118140960795 + 7526369 * 2 ^ 59
def prefixEnd_7526369 : Nat := 4983230072969 + 3 ^ 40 * 7526369 * 2
def baseEnd_7526369 : Nat := 3864644880099168780374365

theorem tailTrace_7526369 : CollatzResearch.WordTrace tailWord_7526369 prefixEnd_7526369 3864644880099168780374365 := by
  unfold tailWord_7526369
  simp only [CollatzResearch.WordTrace]
  refine ⟨274509229270257989334270161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183006152846838659556180107 274509229270257989334270161)
  ·
    refine ⟨205881921952693492000702621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274509229270257989334270161 205881921952693492000702621)
    ·
      refine ⟨77205720732260059500263483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205881921952693492000702621 77205720732260059500263483)
      ·
        refine ⟨115808581098390089250395225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77205720732260059500263483 115808581098390089250395225)
        ·
          refine ⟨86856435823792566937796419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115808581098390089250395225 86856435823792566937796419)
          ·
            refine ⟨130284653735688850406694629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86856435823792566937796419 130284653735688850406694629)
            ·
              refine ⟨24428372575441659451255243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130284653735688850406694629 24428372575441659451255243)
              ·
                refine ⟨36642558863162489176882865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24428372575441659451255243 36642558863162489176882865)
                ·
                  refine ⟨27481919147371866882662149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36642558863162489176882865 27481919147371866882662149)
                  ·
                    refine ⟨5152859840132225040499153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27481919147371866882662149 5152859840132225040499153)
                    ·
                      refine ⟨3864644880099168780374365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5152859840132225040499153 3864644880099168780374365)
                      ·
                        rfl

theorem cell23_7526369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_7526369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526369 prefixEnd_7526369 := by exact prefixLift 7526369
  have htrace : WordTrace (prefixWord ++ tailWord_7526369) baseStart_7526369 baseEnd_7526369 := by
    simpa [prefixWord, tailWord_7526369, baseEnd_7526369] using wordTrace_append hprefix tailTrace_7526369
  have hstable : (prefixWord ++ tailWord_7526369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526369).length < 2 ^ (prefixWord ++ tailWord_7526369).sum := by decide
  have hdescent : baseEnd_7526369 < baseStart_7526369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526372 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_7526372 : Nat := 118140960795 + 7526372 * 2 ^ 59
def prefixEnd_7526372 : Nat := 4983230072969 + 3 ^ 40 * 7526372 * 2
def baseEnd_7526372 : Nat := 3864646420541132268636851

theorem tailTrace_7526372 : CollatzResearch.WordTrace tailWord_7526372 prefixEnd_7526372 3864646420541132268636851 := by
  unfold tailWord_7526372
  simp only [CollatzResearch.WordTrace]
  refine ⟨137254669344623560423314685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183006225792831413897752913 137254669344623560423314685)
  ·
    refine ⟨51470501004233835158743007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137254669344623560423314685 51470501004233835158743007)
    ·
      refine ⟨77205751506350752738114511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51470501004233835158743007 77205751506350752738114511)
      ·
        refine ⟨115808627259526129107171767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77205751506350752738114511 115808627259526129107171767)
        ·
          refine ⟨173712940889289193660757651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115808627259526129107171767 173712940889289193660757651)
          ·
            refine ⟨260569411333933790491136477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173712940889289193660757651 260569411333933790491136477)
            ·
              refine ⟨97713529250225171434176179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260569411333933790491136477 97713529250225171434176179)
              ·
                refine ⟨146570293875337757151264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97713529250225171434176179 146570293875337757151264269)
                ·
                  refine ⟨54963860203251658931724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146570293875337757151264269 54963860203251658931724101)
                  ·
                    refine ⟨10305723788109686049698269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54963860203251658931724101 10305723788109686049698269)
                    ·
                      refine ⟨3864646420541132268636851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10305723788109686049698269 3864646420541132268636851)
                      ·
                        rfl

theorem cell23_7526372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_7526372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526372 prefixEnd_7526372 := by exact prefixLift 7526372
  have htrace : WordTrace (prefixWord ++ tailWord_7526372) baseStart_7526372 baseEnd_7526372 := by
    simpa [prefixWord, tailWord_7526372, baseEnd_7526372] using wordTrace_append hprefix tailTrace_7526372
  have hstable : (prefixWord ++ tailWord_7526372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526372).length < 2 ^ (prefixWord ++ tailWord_7526372).sum := by decide
  have hdescent : baseEnd_7526372 < baseStart_7526372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526426 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_7526426 : Nat := 118140960795 + 7526426 * 2 ^ 59
def prefixEnd_7526426 : Nat := 4983230072969 + 3 ^ 40 * 7526426 * 2
def baseEnd_7526426 : Nat := 429408238721830561929067

theorem tailTrace_7526426 : CollatzResearch.WordTrace tailWord_7526426 prefixEnd_7526426 429408238721830561929067 := by
  unfold tailWord_7526426
  simp only [CollatzResearch.WordTrace]
  refine ⟨68627827057762872017273783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183007538820700992046063421 68627827057762872017273783)
  ·
    refine ⟨102941740586644308025910675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68627827057762872017273783 102941740586644308025910675)
    ·
      refine ⟨154412610879966462038866013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102941740586644308025910675 154412610879966462038866013)
      ·
        refine ⟨57904729079987423264574755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154412610879966462038866013 57904729079987423264574755)
        ·
          refine ⟨86857093619981134896862133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57904729079987423264574755 86857093619981134896862133)
          ·
            refine ⟨8142852526873231396580825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86857093619981134896862133 8142852526873231396580825)
            ·
              refine ⟨6107139395154923547435619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8142852526873231396580825 6107139395154923547435619)
              ·
                refine ⟨9160709092732385321153429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107139395154923547435619 9160709092732385321153429)
                ·
                  refine ⟨429408238721830561929067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9160709092732385321153429 429408238721830561929067)
                  ·
                    rfl

theorem cell23_7526426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_7526426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526426 prefixEnd_7526426 := by exact prefixLift 7526426
  have htrace : WordTrace (prefixWord ++ tailWord_7526426) baseStart_7526426 baseEnd_7526426 := by
    simpa [prefixWord, tailWord_7526426, baseEnd_7526426] using wordTrace_append hprefix tailTrace_7526426
  have hstable : (prefixWord ++ tailWord_7526426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526426).length < 2 ^ (prefixWord ++ tailWord_7526426).sum := by decide
  have hdescent : baseEnd_7526426 < baseStart_7526426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526472 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_7526472 : Nat := 118140960795 + 7526472 * 2 ^ 59
def prefixEnd_7526472 : Nat := 4983230072969 + 3 ^ 40 * 7526472 * 2
def baseEnd_7526472 : Nat := 3864697768606581877386391

theorem tailTrace_7526472 : CollatzResearch.WordTrace tailWord_7526472 prefixEnd_7526472 3864697768606581877386391 := by
  unfold tailWord_7526472
  simp only [CollatzResearch.WordTrace]
  refine ⟨137256492994442418962634835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183008657325923225283513113 137256492994442418962634835)
  ·
    refine ⟨205884739491663628443952253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137256492994442418962634835 205884739491663628443952253)
    ·
      refine ⟨77206777309373860666482095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205884739491663628443952253 77206777309373860666482095)
      ·
        refine ⟨115810165964060790999723143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77206777309373860666482095 115810165964060790999723143)
        ·
          refine ⟨173715248946091186499584715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115810165964060790999723143 173715248946091186499584715)
          ·
            refine ⟨260572873419136779749377073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173715248946091186499584715 260572873419136779749377073)
            ·
              refine ⟨195429655064352584812032805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260572873419136779749377073 195429655064352584812032805)
              ·
                refine ⟨36643060324566109652256151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195429655064352584812032805 36643060324566109652256151)
                ·
                  refine ⟨54964590486849164478384227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36643060324566109652256151 54964590486849164478384227)
                  ·
                    refine ⟨82446885730273746717576341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54964590486849164478384227 82446885730273746717576341)
                    ·
                      refine ⟨3864697768606581877386391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82446885730273746717576341 3864697768606581877386391)
                      ·
                        rfl

theorem cell23_7526472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_7526472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526472 prefixEnd_7526472 := by exact prefixLift 7526472
  have htrace : WordTrace (prefixWord ++ tailWord_7526472) baseStart_7526472 baseEnd_7526472 := by
    simpa [prefixWord, tailWord_7526472, baseEnd_7526472] using wordTrace_append hprefix tailTrace_7526472
  have hstable : (prefixWord ++ tailWord_7526472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526472).length < 2 ^ (prefixWord ++ tailWord_7526472).sum := by decide
  have hdescent : baseEnd_7526472 < baseStart_7526472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526489 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_7526489 : Nat := 118140960795 + 7526489 * 2 ^ 59
def prefixEnd_7526489 : Nat := 4983230072969 + 3 ^ 40 * 7526489 * 2
def baseEnd_7526489 : Nat := 3864706497777708310873813

theorem tailTrace_7526489 : CollatzResearch.WordTrace tailWord_7526489 prefixEnd_7526489 3864706497777708310873813 := by
  unfold tailWord_7526489
  simp only [CollatzResearch.WordTrace]
  refine ⟨274513606029823249828638521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183009070686548833219092347 274513606029823249828638521)
  ·
    refine ⟨205885204522367437371478891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274513606029823249828638521 205885204522367437371478891)
    ·
      refine ⟨308827806783551156057218337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205885204522367437371478891 308827806783551156057218337)
      ·
        refine ⟨231620855087663367042913753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308827806783551156057218337 231620855087663367042913753)
        ·
          refine ⟨173715641315747525282185315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231620855087663367042913753 173715641315747525282185315)
          ·
            refine ⟨260573461973621287923277973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173715641315747525282185315 260573461973621287923277973)
            ·
              refine ⟨12214381030013497871403655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260573461973621287923277973 12214381030013497871403655)
              ·
                refine ⟨18321571545020246807105483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12214381030013497871403655 18321571545020246807105483)
                ·
                  refine ⟨27482357317530370210658225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18321571545020246807105483 27482357317530370210658225)
                  ·
                    refine ⟨20611767988147777657993669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27482357317530370210658225 20611767988147777657993669)
                    ·
                      refine ⟨3864706497777708310873813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20611767988147777657993669 3864706497777708310873813)
                      ·
                        rfl

theorem cell23_7526489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_7526489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526489 prefixEnd_7526489 := by exact prefixLift 7526489
  have htrace : WordTrace (prefixWord ++ tailWord_7526489) baseStart_7526489 baseEnd_7526489 := by
    simpa [prefixWord, tailWord_7526489, baseEnd_7526489] using wordTrace_append hprefix tailTrace_7526489
  have hstable : (prefixWord ++ tailWord_7526489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526489).length < 2 ^ (prefixWord ++ tailWord_7526489).sum := by decide
  have hdescent : baseEnd_7526489 < baseStart_7526489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526583 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_7526583 : Nat := 118140960795 + 7526583 * 2 ^ 59
def prefixEnd_7526583 : Nat := 4983230072969 + 3 ^ 40 * 7526583 * 2
def baseEnd_7526583 : Nat := 3864754764959230943098381

theorem tailTrace_7526583 : CollatzResearch.WordTrace tailWord_7526583 prefixEnd_7526583 3864754764959230943098381 := by
  unfold tailWord_7526583
  simp only [CollatzResearch.WordTrace]
  refine ⟨274517034491482703882560403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183011356327655135921706935 274517034491482703882560403)
  ·
    refine ⟨411775551737224055823840605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274517034491482703882560403 411775551737224055823840605)
    ·
      refine ⟨154415831901459020933940227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411775551737224055823840605 154415831901459020933940227)
      ·
        refine ⟨231623747852188531400910341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154415831901459020933940227 231623747852188531400910341)
        ·
          refine ⟨43429452722285349637670689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231623747852188531400910341 43429452722285349637670689)
          ·
            refine ⟨32572089541714012228253017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43429452722285349637670689 32572089541714012228253017)
            ·
              refine ⟨24429067156285509171189763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32572089541714012228253017 24429067156285509171189763)
              ·
                refine ⟨36643600734428263756784645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24429067156285509171189763 36643600734428263756784645)
                ·
                  refine ⟨6870675137705299454397121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36643600734428263756784645 6870675137705299454397121)
                  ·
                    refine ⟨5153006353278974590797841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6870675137705299454397121 5153006353278974590797841)
                    ·
                      refine ⟨3864754764959230943098381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153006353278974590797841 3864754764959230943098381)
                      ·
                        rfl

theorem cell23_7526583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_7526583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526583 prefixEnd_7526583 := by exact prefixLift 7526583
  have htrace : WordTrace (prefixWord ++ tailWord_7526583) baseStart_7526583 baseEnd_7526583 := by
    simpa [prefixWord, tailWord_7526583, baseEnd_7526583] using wordTrace_append hprefix tailTrace_7526583
  have hstable : (prefixWord ++ tailWord_7526583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526583).length < 2 ^ (prefixWord ++ tailWord_7526583).sum := by decide
  have hdescent : baseEnd_7526583 < baseStart_7526583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526594 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7526594 : Nat := 118140960795 + 7526594 * 2 ^ 59
def prefixEnd_7526594 : Nat := 4983230072969 + 3 ^ 40 * 7526594 * 2
def baseEnd_7526594 : Nat := 3864760413246430400060831

theorem tailTrace_7526594 : CollatzResearch.WordTrace tailWord_7526594 prefixEnd_7526594 3864760413246430400060831 := by
  unfold tailWord_7526594
  simp only [CollatzResearch.WordTrace]
  refine ⟨68629358923610713190302709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183011623796295235174140557 68629358923610713190302709)
  ·
    refine ⟨6434002399088504361590879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68629358923610713190302709 6434002399088504361590879)
    ·
      refine ⟨9651003598632756542386319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434002399088504361590879 9651003598632756542386319)
      ·
        refine ⟨14476505397949134813579479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651003598632756542386319 14476505397949134813579479)
        ·
          refine ⟨21714758096923702220369219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14476505397949134813579479 21714758096923702220369219)
          ·
            refine ⟨32572137145385553330553829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21714758096923702220369219 32572137145385553330553829)
            ·
              refine ⟨6107275714759791249478843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32572137145385553330553829 6107275714759791249478843)
              ·
                refine ⟨9160913572139686874218265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107275714759791249478843 9160913572139686874218265)
                ·
                  refine ⟨6870685179104765155663699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9160913572139686874218265 6870685179104765155663699)
                  ·
                    refine ⟨10306027768657147733495549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6870685179104765155663699 10306027768657147733495549)
                    ·
                      refine ⟨3864760413246430400060831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10306027768657147733495549 3864760413246430400060831)
                      ·
                        rfl

theorem cell23_7526594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7526594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526594 prefixEnd_7526594 := by exact prefixLift 7526594
  have htrace : WordTrace (prefixWord ++ tailWord_7526594) baseStart_7526594 baseEnd_7526594 := by
    simpa [prefixWord, tailWord_7526594, baseEnd_7526594] using wordTrace_append hprefix tailTrace_7526594
  have hstable : (prefixWord ++ tailWord_7526594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526594).length < 2 ^ (prefixWord ++ tailWord_7526594).sum := by decide
  have hdescent : baseEnd_7526594 < baseStart_7526594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526604 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7526604 : Nat := 118140960795 + 7526604 * 2 ^ 59
def prefixEnd_7526604 : Nat := 4983230072969 + 3 ^ 40 * 7526604 * 2
def baseEnd_7526604 : Nat := 3864765548052975360935785

theorem tailTrace_7526604 : CollatzResearch.WordTrace tailWord_7526604 prefixEnd_7526604 3864765548052975360935785 := by
  unfold tailWord_7526604
  simp only [CollatzResearch.WordTrace]
  refine ⟨137258900212203312234537433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183011866949604416312716577 137258900212203312234537433)
  ·
    refine ⟨102944175159152484175903075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137258900212203312234537433 102944175159152484175903075)
    ·
      refine ⟨154416262738728726263854613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102944175159152484175903075 154416262738728726263854613)
      ·
        refine ⟨7238262315877909043618185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154416262738728726263854613 7238262315877909043618185)
        ·
          refine ⟨5428696736908431782713639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238262315877909043618185 5428696736908431782713639)
          ·
            refine ⟨8143045105362647674070459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428696736908431782713639 8143045105362647674070459)
            ·
              refine ⟨12214567658043971511105689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8143045105362647674070459 12214567658043971511105689)
              ·
                refine ⟨9160925743532978633329267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12214567658043971511105689 9160925743532978633329267)
                ·
                  refine ⟨13741388615299467949993901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9160925743532978633329267 13741388615299467949993901)
                  ·
                    refine ⟨5153020730737300481247713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13741388615299467949993901 5153020730737300481247713)
                    ·
                      refine ⟨3864765548052975360935785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153020730737300481247713 3864765548052975360935785)
                      ·
                        rfl

theorem cell23_7526604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7526604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526604 prefixEnd_7526604 := by exact prefixLift 7526604
  have htrace : WordTrace (prefixWord ++ tailWord_7526604) baseStart_7526604 baseEnd_7526604 := by
    simpa [prefixWord, tailWord_7526604, baseEnd_7526604] using wordTrace_append hprefix tailTrace_7526604
  have hstable : (prefixWord ++ tailWord_7526604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526604).length < 2 ^ (prefixWord ++ tailWord_7526604).sum := by decide
  have hdescent : baseEnd_7526604 < baseStart_7526604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526619 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 2, 5]
def baseStart_7526619 : Nat := 118140960795 + 7526619 * 2 ^ 59
def prefixEnd_7526619 : Nat := 4983230072969 + 3 ^ 40 * 7526619 * 2
def baseEnd_7526619 : Nat := 1288257750087597600749405

theorem tailTrace_7526619 : CollatzResearch.WordTrace tailWord_7526619 prefixEnd_7526619 1288257750087597600749405 := by
  unfold tailWord_7526619
  simp only [CollatzResearch.WordTrace]
  refine ⟨274518347519352282030870911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183012231679568188020580607 274518347519352282030870911)
  ·
    refine ⟨411777521279028423046306367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274518347519352282030870911 411777521279028423046306367)
    ·
      refine ⟨617666281918542634569459551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411777521279028423046306367 617666281918542634569459551)
      ·
        refine ⟨926499422877813951854189327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617666281918542634569459551 926499422877813951854189327)
        ·
          refine ⟨1389749134316720927781283991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926499422877813951854189327 1389749134316720927781283991)
          ·
            refine ⟨2084623701475081391671925987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389749134316720927781283991 2084623701475081391671925987)
            ·
              refine ⟨3126935552212622087507888981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084623701475081391671925987 3126935552212622087507888981)
              ·
                refine ⟨18321888001245832543991537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3126935552212622087507888981 18321888001245832543991537)
                ·
                  refine ⟨13741416000934374407993653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18321888001245832543991537 13741416000934374407993653)
                  ·
                    refine ⟨1288257750087597600749405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13741416000934374407993653 1288257750087597600749405)
                    ·
                      rfl

theorem cell23_7526619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 5].length) (baseStart_7526619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526619 prefixEnd_7526619 := by exact prefixLift 7526619
  have htrace : WordTrace (prefixWord ++ tailWord_7526619) baseStart_7526619 baseEnd_7526619 := by
    simpa [prefixWord, tailWord_7526619, baseEnd_7526619] using wordTrace_append hprefix tailTrace_7526619
  have hstable : (prefixWord ++ tailWord_7526619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526619).length < 2 ^ (prefixWord ++ tailWord_7526619).sum := by decide
  have hdescent : baseEnd_7526619 < baseStart_7526619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526646 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7526646 : Nat := 118140960795 + 7526646 * 2 ^ 59
def prefixEnd_7526646 : Nat := 4983230072969 + 3 ^ 40 * 7526646 * 2
def baseEnd_7526646 : Nat := 3864787114240464196610591

theorem tailTrace_7526646 : CollatzResearch.WordTrace tailWord_7526646 prefixEnd_7526646 3864787114240464196610591 := by
  unfold tailWord_7526646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17157458268140904102631487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183012888193502977094735861 17157458268140904102631487)
  ·
    refine ⟨25736187402211356153947231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17157458268140904102631487 25736187402211356153947231)
    ·
      refine ⟨38604281103317034230920847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25736187402211356153947231 38604281103317034230920847)
      ·
        refine ⟨57906421654975551346381271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38604281103317034230920847 57906421654975551346381271)
        ·
          refine ⟨86859632482463327019571907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57906421654975551346381271 86859632482463327019571907)
          ·
            refine ⟨130289448723694990529357861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86859632482463327019571907 130289448723694990529357861)
            ·
              refine ⟨24429271635692810724254599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130289448723694990529357861 24429271635692810724254599)
              ·
                refine ⟨36643907453539216086381899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24429271635692810724254599 36643907453539216086381899)
                ·
                  refine ⟨54965861180308824129572849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36643907453539216086381899 54965861180308824129572849)
                  ·
                    refine ⟨41224395885231618097179637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54965861180308824129572849 41224395885231618097179637)
                    ·
                      refine ⟨3864787114240464196610591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41224395885231618097179637 3864787114240464196610591)
                      ·
                        rfl

theorem cell23_7526646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7526646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526646 prefixEnd_7526646 := by exact prefixLift 7526646
  have htrace : WordTrace (prefixWord ++ tailWord_7526646) baseStart_7526646 baseEnd_7526646 := by
    simpa [prefixWord, tailWord_7526646, baseEnd_7526646] using wordTrace_append hprefix tailTrace_7526646
  have hstable : (prefixWord ++ tailWord_7526646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526646).length < 2 ^ (prefixWord ++ tailWord_7526646).sum := by decide
  have hdescent : baseEnd_7526646 < baseStart_7526646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526656 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2]
def baseStart_7526656 : Nat := 118140960795 + 7526656 * 2 ^ 59
def prefixEnd_7526656 : Nat := 4983230072969 + 3 ^ 40 * 7526656 * 2
def baseEnd_7526656 : Nat := 3864792249047009157485545

theorem tailTrace_7526656 : CollatzResearch.WordTrace tailWord_7526656 prefixEnd_7526656 3864792249047009157485545 := by
  unfold tailWord_7526656
  simp only [CollatzResearch.WordTrace]
  refine ⟨137259848510109118674983911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183013131346812158233311881 137259848510109118674983911)
  ·
    refine ⟨205889772765163678012475867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137259848510109118674983911 205889772765163678012475867)
    ·
      refine ⟨308834659147745517018713801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205889772765163678012475867 308834659147745517018713801)
      ·
        refine ⟨231625994360809137764035351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308834659147745517018713801 231625994360809137764035351)
        ·
          refine ⟨347438991541213706646053027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231625994360809137764035351 347438991541213706646053027)
          ·
            refine ⟨521158487311820559969079541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347438991541213706646053027 521158487311820559969079541)
            ·
              refine ⟨48858608185483177497101207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521158487311820559969079541 48858608185483177497101207)
              ·
                refine ⟨73287912278224766245651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48858608185483177497101207 73287912278224766245651811)
                ·
                  refine ⟨109931868417337149368477717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73287912278224766245651811 109931868417337149368477717)
                  ·
                    refine ⟨5153056332062678876647393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109931868417337149368477717 5153056332062678876647393)
                    ·
                      refine ⟨3864792249047009157485545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153056332062678876647393 3864792249047009157485545)
                      ·
                        rfl

theorem cell23_7526656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_7526656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526656 prefixEnd_7526656 := by exact prefixLift 7526656
  have htrace : WordTrace (prefixWord ++ tailWord_7526656) baseStart_7526656 baseEnd_7526656 := by
    simpa [prefixWord, tailWord_7526656, baseEnd_7526656] using wordTrace_append hprefix tailTrace_7526656
  have hstable : (prefixWord ++ tailWord_7526656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526656).length < 2 ^ (prefixWord ++ tailWord_7526656).sum := by decide
  have hdescent : baseEnd_7526656 < baseStart_7526656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526666 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_7526666 : Nat := 118140960795 + 7526666 * 2 ^ 59
def prefixEnd_7526666 : Nat := 4983230072969 + 3 ^ 40 * 7526666 * 2
def baseEnd_7526666 : Nat := 1288265794617851372786833

theorem tailTrace_7526666 : CollatzResearch.WordTrace tailWord_7526666 prefixEnd_7526666 1288265794617851372786833 := by
  unfold tailWord_7526666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68630015437545502264457963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183013374500121339371887901 68630015437545502264457963)
  ·
    refine ⟨102945023156318253396686945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68630015437545502264457963 102945023156318253396686945)
    ·
      refine ⟨77208767367238690047515209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102945023156318253396686945 77208767367238690047515209)
      ·
        refine ⟨57906575525429017535636407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77208767367238690047515209 57906575525429017535636407)
        ·
          refine ⟨86859863288143526303454611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57906575525429017535636407 86859863288143526303454611)
          ·
            refine ⟨130289794932215289455181917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86859863288143526303454611 130289794932215289455181917)
            ·
              refine ⟨48858673099580733545693219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130289794932215289455181917 48858673099580733545693219)
              ·
                refine ⟨73288009649371100318539829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48858673099580733545693219 73288009649371100318539829)
                ·
                  refine ⟨6870750904628540654863109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73288009649371100318539829 6870750904628540654863109)
                  ·
                    refine ⟨1288265794617851372786833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6870750904628540654863109 1288265794617851372786833)
                    ·
                      rfl

theorem cell23_7526666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_7526666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526666 prefixEnd_7526666 := by exact prefixLift 7526666
  have htrace : WordTrace (prefixWord ++ tailWord_7526666) baseStart_7526666 baseEnd_7526666 := by
    simpa [prefixWord, tailWord_7526666, baseEnd_7526666] using wordTrace_append hprefix tailTrace_7526666
  have hstable : (prefixWord ++ tailWord_7526666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526666).length < 2 ^ (prefixWord ++ tailWord_7526666).sum := by decide
  have hdescent : baseEnd_7526666 < baseStart_7526666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526673 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_7526673 : Nat := 118140960795 + 7526673 * 2 ^ 59
def prefixEnd_7526673 : Nat := 4983230072969 + 3 ^ 40 * 7526673 * 2
def baseEnd_7526673 : Nat := 3864800978218135590972967

theorem tailTrace_7526673 : CollatzResearch.WordTrace tailWord_7526673 prefixEnd_7526673 3864800978218135590972967 := by
  unfold tailWord_7526673
  simp only [CollatzResearch.WordTrace]
  refine ⟨274520317061156649253336673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183013544707437766168891115 274520317061156649253336673)
  ·
    refine ⟨205890237795867486940002505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274520317061156649253336673 205890237795867486940002505)
    ·
      refine ⟨154417678346900615205001879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205890237795867486940002505 154417678346900615205001879)
      ·
        refine ⟨231626517520350922807502819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154417678346900615205001879 231626517520350922807502819)
        ·
          refine ⟨347439776280526384211254229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231626517520350922807502819 347439776280526384211254229)
          ·
            refine ⟨8143119756574837129951271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 347439776280526384211254229 8143119756574837129951271)
            ·
              refine ⟨12214679634862255694926907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8143119756574837129951271 12214679634862255694926907)
              ·
                refine ⟨18322019452293383542390361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12214679634862255694926907 18322019452293383542390361)
                ·
                  refine ⟨13741514589220037656792771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18322019452293383542390361 13741514589220037656792771)
                  ·
                    refine ⟨20612271883830056485189157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13741514589220037656792771 20612271883830056485189157)
                    ·
                      refine ⟨3864800978218135590972967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20612271883830056485189157 3864800978218135590972967)
                      ·
                        rfl

theorem cell23_7526673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_7526673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526673 prefixEnd_7526673 := by exact prefixLift 7526673
  have htrace : WordTrace (prefixWord ++ tailWord_7526673) baseStart_7526673 baseEnd_7526673 := by
    simpa [prefixWord, tailWord_7526673, baseEnd_7526673] using wordTrace_append hprefix tailTrace_7526673
  have hstable : (prefixWord ++ tailWord_7526673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526673).length < 2 ^ (prefixWord ++ tailWord_7526673).sum := by decide
  have hdescent : baseEnd_7526673 < baseStart_7526673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526683 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 1, 4]
def baseStart_7526683 : Nat := 118140960795 + 7526683 * 2 ^ 59
def prefixEnd_7526683 : Nat := 4983230072969 + 3 ^ 40 * 7526683 * 2
def baseEnd_7526683 : Nat := 1288268704341560183949307

theorem tailTrace_7526683 : CollatzResearch.WordTrace tailWord_7526683 prefixEnd_7526683 1288268704341560183949307 := by
  unfold tailWord_7526683
  simp only [CollatzResearch.WordTrace]
  refine ⟨274520681791120420961200703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183013787860746947307467135 274520681791120420961200703)
  ·
    refine ⟨411781022686680631441801055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274520681791120420961200703 411781022686680631441801055)
    ·
      refine ⟨617671534030020947162701583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411781022686680631441801055 617671534030020947162701583)
      ·
        refine ⟨926507301045031420744052375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617671534030020947162701583 926507301045031420744052375)
        ·
          refine ⟨1389760951567547131116078563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926507301045031420744052375 1389760951567547131116078563)
          ·
            refine ⟨2084641427351320696674117845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389760951567547131116078563 2084641427351320696674117845)
            ·
              refine ⟨48858783453546578828299637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2084641427351320696674117845 48858783453546578828299637)
              ·
                refine ⟨4580510948769991765153091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48858783453546578828299637 4580510948769991765153091)
                ·
                  refine ⟨6870766423154987647729637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580510948769991765153091 6870766423154987647729637)
                  ·
                    refine ⟨1288268704341560183949307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6870766423154987647729637 1288268704341560183949307)
                    ·
                      rfl

theorem cell23_7526683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 4].length) (baseStart_7526683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526683 prefixEnd_7526683 := by exact prefixLift 7526683
  have htrace : WordTrace (prefixWord ++ tailWord_7526683) baseStart_7526683 baseEnd_7526683 := by
    simpa [prefixWord, tailWord_7526683, baseEnd_7526683] using wordTrace_append hprefix tailTrace_7526683
  have hstable : (prefixWord ++ tailWord_7526683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526683).length < 2 ^ (prefixWord ++ tailWord_7526683).sum := by decide
  have hdescent : baseEnd_7526683 < baseStart_7526683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526723 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 3]
def baseStart_7526723 : Nat := 118140960795 + 7526723 * 2 ^ 59
def prefixEnd_7526723 : Nat := 4983230072969 + 3 ^ 40 * 7526723 * 2
def baseEnd_7526723 : Nat := 3864826652250860395347737

theorem tailTrace_7526723 : CollatzResearch.WordTrace tailWord_7526723 prefixEnd_7526723 3864826652250860395347737 := by
  unfold tailWord_7526723
  simp only [CollatzResearch.WordTrace]
  refine ⟨274522140710975507792656823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183014760473983671861771215 274522140710975507792656823)
  ·
    refine ⟨411783211066463261688985235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274522140710975507792656823 411783211066463261688985235)
    ·
      refine ⟨617674816599694892533477853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411783211066463261688985235 617674816599694892533477853)
      ·
        refine ⟨231628056224885584700054195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617674816599694892533477853 231628056224885584700054195)
        ·
          refine ⟨347442084337328377050081293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231628056224885584700054195 347442084337328377050081293)
          ·
            refine ⟨130290781626498141393780485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347442084337328377050081293 130290781626498141393780485)
            ·
              refine ⟨24429521554968401511333841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130290781626498141393780485 24429521554968401511333841)
              ·
                refine ⟨18322141166226301133500381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24429521554968401511333841 18322141166226301133500381)
                ·
                  refine ⟨6870802937334862925062643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18322141166226301133500381 6870802937334862925062643)
                  ·
                    refine ⟨10306204406002294387593965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6870802937334862925062643 10306204406002294387593965)
                    ·
                      refine ⟨3864826652250860395347737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10306204406002294387593965 3864826652250860395347737)
                      ·
                        rfl

theorem cell23_7526723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_7526723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526723 prefixEnd_7526723 := by exact prefixLift 7526723
  have htrace : WordTrace (prefixWord ++ tailWord_7526723) baseStart_7526723 baseEnd_7526723 := by
    simpa [prefixWord, tailWord_7526723, baseEnd_7526723] using wordTrace_append hprefix tailTrace_7526723
  have hstable : (prefixWord ++ tailWord_7526723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526723).length < 2 ^ (prefixWord ++ tailWord_7526723).sum := by decide
  have hdescent : baseEnd_7526723 < baseStart_7526723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526746 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_7526746 : Nat := 118140960795 + 7526746 * 2 ^ 59
def prefixEnd_7526746 : Nat := 4983230072969 + 3 ^ 40 * 7526746 * 2
def baseEnd_7526746 : Nat := 3864838462305913805360131

theorem tailTrace_7526746 : CollatzResearch.WordTrace tailWord_7526746 prefixEnd_7526746 3864838462305913805360131 := by
  unfold tailWord_7526746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68630744897473045680186023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183015319726594788480496061 68630744897473045680186023)
  ·
    refine ⟨102946117346209568520279035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68630744897473045680186023 102946117346209568520279035)
    ·
      refine ⟨154419176019314352780418553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102946117346209568520279035 154419176019314352780418553)
      ·
        refine ⟨115814382014485764585313915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154419176019314352780418553 115814382014485764585313915)
        ·
          refine ⟨173721573021728646877970873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115814382014485764585313915 173721573021728646877970873)
          ·
            refine ⟨130291179766296485158478155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173721573021728646877970873 130291179766296485158478155)
            ·
              refine ⟨195436769649444727737717233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130291179766296485158478155 195436769649444727737717233)
              ·
                refine ⟨146577577237083545803287925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195436769649444727737717233 146577577237083545803287925)
                ·
                  refine ⟨13741647865976582419058243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146577577237083545803287925 13741647865976582419058243)
                  ·
                    refine ⟨20612471798964873628587365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13741647865976582419058243 20612471798964873628587365)
                    ·
                      refine ⟨3864838462305913805360131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20612471798964873628587365 3864838462305913805360131)
                      ·
                        rfl

theorem cell23_7526746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_7526746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526746 prefixEnd_7526746 := by exact prefixLift 7526746
  have htrace : WordTrace (prefixWord ++ tailWord_7526746) baseStart_7526746 baseEnd_7526746 := by
    simpa [prefixWord, tailWord_7526746, baseEnd_7526746] using wordTrace_append hprefix tailTrace_7526746
  have hstable : (prefixWord ++ tailWord_7526746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526746).length < 2 ^ (prefixWord ++ tailWord_7526746).sum := by decide
  have hdescent : baseEnd_7526746 < baseStart_7526746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526793 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_7526793 : Nat := 118140960795 + 7526793 * 2 ^ 59
def prefixEnd_7526793 : Nat := 4983230072969 + 3 ^ 40 * 7526793 * 2
def baseEnd_7526793 : Nat := 3864862595896675121472415

theorem tailTrace_7526793 : CollatzResearch.WordTrace tailWord_7526793 prefixEnd_7526793 3864862595896675121472415 := by
  unfold tailWord_7526793
  simp only [CollatzResearch.WordTrace]
  refine ⟨274524693820721909747705033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183016462547147939831803355 274524693820721909747705033)
  ·
    refine ⟨205893520365541432310778775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274524693820721909747705033 205893520365541432310778775)
    ·
      refine ⟨308840280548312148466168163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205893520365541432310778775 308840280548312148466168163)
      ·
        refine ⟨463260420822468222699252245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308840280548312148466168163 463260420822468222699252245)
        ·
          refine ⟨21715332226053197939027449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 463260420822468222699252245 21715332226053197939027449)
          ·
            refine ⟨16286499169539898454270587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21715332226053197939027449 16286499169539898454270587)
            ·
              refine ⟨24429748754309847681405881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16286499169539898454270587 24429748754309847681405881)
              ·
                refine ⟨18322311565732385761054411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24429748754309847681405881 18322311565732385761054411)
                ·
                  refine ⟨27483467348598578641581617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18322311565732385761054411 27483467348598578641581617)
                  ·
                    refine ⟨20612600511448933981186213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27483467348598578641581617 20612600511448933981186213)
                    ·
                      refine ⟨3864862595896675121472415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20612600511448933981186213 3864862595896675121472415)
                      ·
                        rfl

theorem cell23_7526793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_7526793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526793 prefixEnd_7526793 := by exact prefixLift 7526793
  have htrace : WordTrace (prefixWord ++ tailWord_7526793) baseStart_7526793 baseEnd_7526793 := by
    simpa [prefixWord, tailWord_7526793, baseEnd_7526793] using wordTrace_append hprefix tailTrace_7526793
  have hstable : (prefixWord ++ tailWord_7526793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526793).length < 2 ^ (prefixWord ++ tailWord_7526793).sum := by decide
  have hdescent : baseEnd_7526793 < baseStart_7526793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526816 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_7526816 : Nat := 118140960795 + 7526816 * 2 ^ 59
def prefixEnd_7526816 : Nat := 4983230072969 + 3 ^ 40 * 7526816 * 2
def baseEnd_7526816 : Nat := 1288291468650576177161603

theorem tailTrace_7526816 : CollatzResearch.WordTrace tailWord_7526816 prefixEnd_7526816 1288291468650576177161603 := by
  unfold tailWord_7526816
  simp only [CollatzResearch.WordTrace]
  refine ⟨137262766349819292337896151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183017021799759056450528201 137262766349819292337896151)
  ·
    refine ⟨205894149524728938506844227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137262766349819292337896151 205894149524728938506844227)
    ·
      refine ⟨308841224287093407760266341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205894149524728938506844227 308841224287093407760266341)
      ·
        refine ⟨57907729553830013955049939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308841224287093407760266341 57907729553830013955049939)
        ·
          refine ⟨86861594330745020932574909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57907729553830013955049939 86861594330745020932574909)
          ·
            refine ⟨32573097874029382849715591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86861594330745020932574909 32573097874029382849715591)
            ·
              refine ⟨48859646811044074274573387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32573097874029382849715591 48859646811044074274573387)
              ·
                refine ⟨73289470216566111411860081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48859646811044074274573387 73289470216566111411860081)
                ·
                  refine ⟨54967102662424583558895061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73289470216566111411860081 54967102662424583558895061)
                  ·
                    refine ⟨1288291468650576177161603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54967102662424583558895061 1288291468650576177161603)
                    ·
                      rfl

theorem cell23_7526816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_7526816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526816 prefixEnd_7526816 := by exact prefixLift 7526816
  have htrace : WordTrace (prefixWord ++ tailWord_7526816) baseStart_7526816 baseEnd_7526816 := by
    simpa [prefixWord, tailWord_7526816, baseEnd_7526816] using wordTrace_append hprefix tailTrace_7526816
  have hstable : (prefixWord ++ tailWord_7526816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526816).length < 2 ^ (prefixWord ++ tailWord_7526816).sum := by decide
  have hdescent : baseEnd_7526816 < baseStart_7526816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526840 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_7526840 : Nat := 118140960795 + 7526840 * 2 ^ 59
def prefixEnd_7526840 : Nat := 4983230072969 + 3 ^ 40 * 7526840 * 2
def baseEnd_7526840 : Nat := 3864886729487436437584699

theorem tailTrace_7526840 : CollatzResearch.WordTrace tailWord_7526840 prefixEnd_7526840 3864886729487436437584699 := by
  unfold tailWord_7526840
  simp only [CollatzResearch.WordTrace]
  refine ⟨137263204025775818387332987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183017605367701091183110649 137263204025775818387332987)
  ·
    refine ⟨205894806038663727580999481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137263204025775818387332987 205894806038663727580999481)
    ·
      refine ⟨154421104528997795685749611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205894806038663727580999481 154421104528997795685749611)
      ·
        refine ⟨231631656793496693528624417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154421104528997795685749611 231631656793496693528624417)
        ·
          refine ⟨173723742595122520146468313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231631656793496693528624417 173723742595122520146468313)
          ·
            refine ⟨130292806946341890109851235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173723742595122520146468313 130292806946341890109851235)
            ·
              refine ⟨195439210419512835164776853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130292806946341890109851235 195439210419512835164776853)
              ·
                refine ⟨9161212988414664148348915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195439210419512835164776853 9161212988414664148348915)
                ·
                  refine ⟨13741819482621996222523373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161212988414664148348915 13741819482621996222523373)
                  ·
                    refine ⟨5153182305983248583446265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13741819482621996222523373 5153182305983248583446265)
                    ·
                      refine ⟨3864886729487436437584699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153182305983248583446265 3864886729487436437584699)
                      ·
                        rfl

theorem cell23_7526840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_7526840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526840 prefixEnd_7526840 := by exact prefixLift 7526840
  have htrace : WordTrace (prefixWord ++ tailWord_7526840) baseStart_7526840 baseEnd_7526840 := by
    simpa [prefixWord, tailWord_7526840, baseEnd_7526840] using wordTrace_append hprefix tailTrace_7526840
  have hstable : (prefixWord ++ tailWord_7526840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526840).length < 2 ^ (prefixWord ++ tailWord_7526840).sum := by decide
  have hdescent : baseEnd_7526840 < baseStart_7526840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526857 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 1, 3, 2]
def baseStart_7526857 : Nat := 118140960795 + 7526857 * 2 ^ 59
def prefixEnd_7526857 : Nat := 4983230072969 + 3 ^ 40 * 7526857 * 2
def baseEnd_7526857 : Nat := 3864895458658562871072121

theorem tailTrace_7526857 : CollatzResearch.WordTrace tailWord_7526857 prefixEnd_7526857 3864895458658562871072121 := by
  unfold tailWord_7526857
  simp only [CollatzResearch.WordTrace]
  refine ⟨274527028092490048678034825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183018018728326699118689883 274527028092490048678034825)
  ·
    refine ⟨205895271069367536508526119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274527028092490048678034825 205895271069367536508526119)
    ·
      refine ⟨308842906604051304762789179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205895271069367536508526119 308842906604051304762789179)
      ·
        refine ⟨463264359906076957144183769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308842906604051304762789179 463264359906076957144183769)
        ·
          refine ⟨347448269929557717858137827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463264359906076957144183769 347448269929557717858137827)
          ·
            refine ⟨521172404894336576787206741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347448269929557717858137827 521172404894336576787206741)
            ·
              refine ⟨6107489119855506759225079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 521172404894336576787206741 6107489119855506759225079)
              ·
                refine ⟨9161233679783260138837619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107489119855506759225079 9161233679783260138837619)
                ·
                  refine ⟨13741850519674890208256429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161233679783260138837619 13741850519674890208256429)
                  ·
                    refine ⟨5153193944878083828096161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13741850519674890208256429 5153193944878083828096161)
                    ·
                      refine ⟨3864895458658562871072121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153193944878083828096161 3864895458658562871072121)
                      ·
                        rfl

theorem cell23_7526857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 3, 2].length) (baseStart_7526857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526857 prefixEnd_7526857 := by exact prefixLift 7526857
  have htrace : WordTrace (prefixWord ++ tailWord_7526857) baseStart_7526857 baseEnd_7526857 := by
    simpa [prefixWord, tailWord_7526857, baseEnd_7526857] using wordTrace_append hprefix tailTrace_7526857
  have hstable : (prefixWord ++ tailWord_7526857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526857).length < 2 ^ (prefixWord ++ tailWord_7526857).sum := by decide
  have hdescent : baseEnd_7526857 < baseStart_7526857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526923 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 4, 5]
def baseStart_7526923 : Nat := 118140960795 + 7526923 * 2 ^ 59
def prefixEnd_7526923 : Nat := 4983230072969 + 3 ^ 40 * 7526923 * 2
def baseEnd_7526923 : Nat := 1288309782793919870948939

theorem tailTrace_7526923 : CollatzResearch.WordTrace tailWord_7526923 prefixEnd_7526923 1288309782793919870948939 := by
  unfold tailWord_7526923
  simp only [CollatzResearch.WordTrace]
  refine ⟨274529435310250941949937423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183019623540167294633291615 274529435310250941949937423)
  ·
    refine ⟨411794152965376412924906135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274529435310250941949937423 411794152965376412924906135)
    ·
      refine ⟨617691229448064619387359203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411794152965376412924906135 617691229448064619387359203)
      ·
        refine ⟨926536844172096929081038805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617691229448064619387359203 926536844172096929081038805)
        ·
          refine ⟨21715707285283521775336847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 926536844172096929081038805 21715707285283521775336847)
          ·
            refine ⟨32573560927925282663005271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21715707285283521775336847 32573560927925282663005271)
            ·
              refine ⟨48860341391887923994507907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32573560927925282663005271 48860341391887923994507907)
              ·
                refine ⟨73290512087831885991761861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48860341391887923994507907 73290512087831885991761861)
                ·
                  refine ⟨13741971016468478623455349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73290512087831885991761861 13741971016468478623455349)
                  ·
                    refine ⟨1288309782793919870948939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13741971016468478623455349 1288309782793919870948939)
                    ·
                      rfl

theorem cell23_7526923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 5].length) (baseStart_7526923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526923 prefixEnd_7526923 := by exact prefixLift 7526923
  have htrace : WordTrace (prefixWord ++ tailWord_7526923) baseStart_7526923 baseEnd_7526923 := by
    simpa [prefixWord, tailWord_7526923, baseEnd_7526923] using wordTrace_append hprefix tailTrace_7526923
  have hstable : (prefixWord ++ tailWord_7526923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526923).length < 2 ^ (prefixWord ++ tailWord_7526923).sum := by decide
  have hdescent : baseEnd_7526923 < baseStart_7526923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526933 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_7526933 : Nat := 118140960795 + 7526933 * 2 ^ 59
def prefixEnd_7526933 : Nat := 4983230072969 + 3 ^ 40 * 7526933 * 2
def baseEnd_7526933 : Nat := 3864934483188304573721771

theorem tailTrace_7526933 : CollatzResearch.WordTrace tailWord_7526933 prefixEnd_7526933 3864934483188304573721771 := by
  unfold tailWord_7526933
  simp only [CollatzResearch.WordTrace]
  refine ⟨274529800040214713657801453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183019866693476475771867635 274529800040214713657801453)
  ·
    refine ⟨102948675015080517621675545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274529800040214713657801453 102948675015080517621675545)
    ·
      refine ⟨77211506261310388216256659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102948675015080517621675545 77211506261310388216256659)
      ·
        refine ⟨115817259391965582324384989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77211506261310388216256659 115817259391965582324384989)
        ·
          refine ⟨43431472271987093371644371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115817259391965582324384989 43431472271987093371644371)
          ·
            refine ⟨65147208407980640057466557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43431472271987093371644371 65147208407980640057466557)
            ·
              refine ⟨24430203152992740021549959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65147208407980640057466557 24430203152992740021549959)
              ·
                refine ⟨36645304729489110032324939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24430203152992740021549959 36645304729489110032324939)
                ·
                  refine ⟨54967957094233665048487409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36645304729489110032324939 54967957094233665048487409)
                  ·
                    refine ⟨41225967820675248786365557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54967957094233665048487409 41225967820675248786365557)
                    ·
                      refine ⟨3864934483188304573721771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41225967820675248786365557 3864934483188304573721771)
                      ·
                        rfl

theorem cell23_7526933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_7526933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526933 prefixEnd_7526933 := by exact prefixLift 7526933
  have htrace : WordTrace (prefixWord ++ tailWord_7526933) baseStart_7526933 baseEnd_7526933 := by
    simpa [prefixWord, tailWord_7526933, baseEnd_7526933] using wordTrace_append hprefix tailTrace_7526933
  have hstable : (prefixWord ++ tailWord_7526933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526933).length < 2 ^ (prefixWord ++ tailWord_7526933).sum := by decide
  have hdescent : baseEnd_7526933 < baseStart_7526933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7526943 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7526943 : Nat := 118140960795 + 7526943 * 2 ^ 59
def prefixEnd_7526943 : Nat := 4983230072969 + 3 ^ 40 * 7526943 * 2
def baseEnd_7526943 : Nat := 3864939617994849534596725

theorem tailTrace_7526943 : CollatzResearch.WordTrace tailWord_7526943 prefixEnd_7526943 3864939617994849534596725 := by
  unfold tailWord_7526943
  simp only [CollatzResearch.WordTrace]
  refine ⟨274530164770178485365665483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183020109846785656910443655 274530164770178485365665483)
  ·
    refine ⟨411795247155267728048498225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274530164770178485365665483 411795247155267728048498225)
    ·
      refine ⟨308846435366450796036373669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411795247155267728048498225 308846435366450796036373669)
      ·
        refine ⟨57908706631209524256820063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308846435366450796036373669 57908706631209524256820063)
        ·
          refine ⟨86863059946814286385230095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57908706631209524256820063 86863059946814286385230095)
          ·
            refine ⟨130294589920221429577845143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86863059946814286385230095 130294589920221429577845143)
            ·
              refine ⟨195441884880332144366767715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130294589920221429577845143 195441884880332144366767715)
              ·
                refine ⟨293162827320498216550151573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195441884880332144366767715 293162827320498216550151573)
                ·
                  refine ⟨13742007530648353900788355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293162827320498216550151573 13742007530648353900788355)
                  ·
                    refine ⟨20613011295972530851182533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13742007530648353900788355 20613011295972530851182533)
                    ·
                      refine ⟨3864939617994849534596725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20613011295972530851182533 3864939617994849534596725)
                      ·
                        rfl

theorem cell23_7526943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7526943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7526943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7526943 prefixEnd_7526943 := by exact prefixLift 7526943
  have htrace : WordTrace (prefixWord ++ tailWord_7526943) baseStart_7526943 baseEnd_7526943 := by
    simpa [prefixWord, tailWord_7526943, baseEnd_7526943] using wordTrace_append hprefix tailTrace_7526943
  have hstable : (prefixWord ++ tailWord_7526943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7526943).length < 2 ^ (prefixWord ++ tailWord_7526943).sum := by decide
  have hdescent : baseEnd_7526943 < baseStart_7526943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7526943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527043 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 3, 6]
def baseStart_7527043 : Nat := 118140960795 + 7527043 * 2 ^ 59
def prefixEnd_7527043 : Nat := 4983230072969 + 3 ^ 40 * 7527043 * 2
def baseEnd_7527043 : Nat := 1288330322020099714448755

theorem tailTrace_7527043 : CollatzResearch.WordTrace tailWord_7527043 prefixEnd_7527043 1288330322020099714448755 := by
  unfold tailWord_7527043
  simp only [CollatzResearch.WordTrace]
  refine ⟨274533812069816202444305783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183022541379877468296203855 274533812069816202444305783)
  ·
    refine ⟨411800718104724303666458675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274533812069816202444305783 411800718104724303666458675)
    ·
      refine ⟨617701077157086455499688013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411800718104724303666458675 617701077157086455499688013)
      ·
        refine ⟨231637903933907420812383005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617701077157086455499688013 231637903933907420812383005)
        ·
          refine ⟨86864213975215282804643627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231637903933907420812383005 86864213975215282804643627)
          ·
            refine ⟨130296320962822924206965441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86864213975215282804643627 130296320962822924206965441)
            ·
              refine ⟨97722240722117193155224081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130296320962822924206965441 97722240722117193155224081)
              ·
                refine ⟨73291680541587894866418061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97722240722117193155224081 73291680541587894866418061)
                ·
                  refine ⟨27484380203095460574906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73291680541587894866418061 27484380203095460574906773)
                  ·
                    refine ⟨1288330322020099714448755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27484380203095460574906773 1288330322020099714448755)
                    ·
                      rfl

theorem cell23_7527043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_7527043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527043 prefixEnd_7527043 := by exact prefixLift 7527043
  have htrace : WordTrace (prefixWord ++ tailWord_7527043) baseStart_7527043 baseEnd_7527043 := by
    simpa [prefixWord, tailWord_7527043, baseEnd_7527043] using wordTrace_append hprefix tailTrace_7527043
  have hstable : (prefixWord ++ tailWord_7527043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527043).length < 2 ^ (prefixWord ++ tailWord_7527043).sum := by decide
  have hdescent : baseEnd_7527043 < baseStart_7527043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527044 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_7527044 : Nat := 118140960795 + 7527044 * 2 ^ 59
def prefixEnd_7527044 : Nat := 4983230072969 + 3 ^ 40 * 7527044 * 2
def baseEnd_7527044 : Nat := 3864991479540953639433761

theorem tailTrace_7527044 : CollatzResearch.WordTrace tailWord_7527044 prefixEnd_7527044 3864991479540953639433761 := by
  unfold tailWord_7527044
  simp only [CollatzResearch.WordTrace]
  refine ⟨137266924271406289807546093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183022565695208386410061457 137266924271406289807546093)
  ·
    refine ⟨51475096601777358677829785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137266924271406289807546093 51475096601777358677829785)
    ·
      refine ⟨38606322451333019008372339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51475096601777358677829785 38606322451333019008372339)
      ·
        refine ⟨57909483676999528512558509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38606322451333019008372339 57909483676999528512558509)
        ·
          refine ⟨21716056378874823192209441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57909483676999528512558509 21716056378874823192209441)
          ·
            refine ⟨16287042284156117394157081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21716056378874823192209441 16287042284156117394157081)
            ·
              refine ⟨12215281713117088045617811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16287042284156117394157081 12215281713117088045617811)
              ·
                refine ⟨18322922569675632068426717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12215281713117088045617811 18322922569675632068426717)
                ·
                  refine ⟨6871095963628362025660019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18322922569675632068426717 6871095963628362025660019)
                  ·
                    refine ⟨10306643945442543038490029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6871095963628362025660019 10306643945442543038490029)
                    ·
                      refine ⟨3864991479540953639433761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10306643945442543038490029 3864991479540953639433761)
                      ·
                        rfl

theorem cell23_7527044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_7527044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527044 prefixEnd_7527044 := by exact prefixLift 7527044
  have htrace : WordTrace (prefixWord ++ tailWord_7527044) baseStart_7527044 baseEnd_7527044 := by
    simpa [prefixWord, tailWord_7527044, baseEnd_7527044] using wordTrace_append hprefix tailTrace_7527044
  have hstable : (prefixWord ++ tailWord_7527044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527044).length < 2 ^ (prefixWord ++ tailWord_7527044).sum := by decide
  have hdescent : baseEnd_7527044 < baseStart_7527044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527087 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_7527087 : Nat := 118140960795 + 7527087 * 2 ^ 59
def prefixEnd_7527087 : Nat := 4983230072969 + 3 ^ 40 * 7527087 * 2
def baseEnd_7527087 : Nat := 3865013559209096971196063

theorem tailTrace_7527087 : CollatzResearch.WordTrace tailWord_7527087 prefixEnd_7527087 3865013559209096971196063 := by
  unfold tailWord_7527087
  simp only [CollatzResearch.WordTrace]
  refine ⟨274535416881656797958907515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183023611254437865305938343 274535416881656797958907515)
  ·
    refine ⟨411803125322485196938361273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274535416881656797958907515 411803125322485196938361273)
    ·
      refine ⟨308852343991863897703770955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411803125322485196938361273 308852343991863897703770955)
      ·
        refine ⟨463278515987795846555656433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308852343991863897703770955 463278515987795846555656433)
        ·
          refine ⟨347458886990846884916742325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463278515987795846555656433 347458886990846884916742325)
          ·
            refine ⟨32574270655391895460944593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347458886990846884916742325 32574270655391895460944593)
            ·
              refine ⟨24430702991543921595708445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32574270655391895460944593 24430702991543921595708445)
              ·
                refine ⟨9161513621828970598390667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24430702991543921595708445 9161513621828970598390667)
                ·
                  refine ⟨13742270432743455897586001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161513621828970598390667 13742270432743455897586001)
                  ·
                    refine ⟨10306702824557591923189501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13742270432743455897586001 10306702824557591923189501)
                    ·
                      refine ⟨3865013559209096971196063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10306702824557591923189501 3865013559209096971196063)
                      ·
                        rfl

theorem cell23_7527087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_7527087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527087 prefixEnd_7527087 := by exact prefixLift 7527087
  have htrace : WordTrace (prefixWord ++ tailWord_7527087) baseStart_7527087 baseEnd_7527087 := by
    simpa [prefixWord, tailWord_7527087, baseEnd_7527087] using wordTrace_append hprefix tailTrace_7527087
  have hstable : (prefixWord ++ tailWord_7527087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527087).length < 2 ^ (prefixWord ++ tailWord_7527087).sum := by decide
  have hdescent : baseEnd_7527087 < baseStart_7527087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527101 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_7527101 : Nat := 118140960795 + 7527101 * 2 ^ 59
def prefixEnd_7527101 : Nat := 4983230072969 + 3 ^ 40 * 7527101 * 2
def baseEnd_7527101 : Nat := 3865020747938259916420999

theorem tailTrace_7527101 : CollatzResearch.WordTrace tailWord_7527101 prefixEnd_7527101 3865020747938259916420999 := by
  unfold tailWord_7527101
  simp only [CollatzResearch.WordTrace]
  refine ⟨274535927503606078349917157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183023951669070718899944771 274535927503606078349917157)
  ·
    refine ⟨51475486406926139690609467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274535927503606078349917157 51475486406926139690609467)
    ·
      refine ⟨77213229610389209535914201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51475486406926139690609467 77213229610389209535914201)
      ·
        refine ⟨57909922207791907151935651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77213229610389209535914201 57909922207791907151935651)
        ·
          refine ⟨86864883311687860727903477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57909922207791907151935651 86864883311687860727903477)
          ·
            refine ⟨8143582810470736943240951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86864883311687860727903477 8143582810470736943240951)
            ·
              refine ⟨12215374215706105414861427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8143582810470736943240951 12215374215706105414861427)
              ·
                refine ⟨18323061323559158122292141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12215374215706105414861427 18323061323559158122292141)
                ·
                  refine ⟨6871147996334684295859553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18323061323559158122292141 6871147996334684295859553)
                  ·
                    refine ⟨5153360997251013221894665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6871147996334684295859553 5153360997251013221894665)
                    ·
                      refine ⟨3865020747938259916420999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153360997251013221894665 3865020747938259916420999)
                      ·
                        rfl

theorem cell23_7527101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_7527101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527101 prefixEnd_7527101 := by exact prefixLift 7527101
  have htrace : WordTrace (prefixWord ++ tailWord_7527101) baseStart_7527101 baseEnd_7527101 := by
    simpa [prefixWord, tailWord_7527101, baseEnd_7527101] using wordTrace_append hprefix tailTrace_7527101
  have hstable : (prefixWord ++ tailWord_7527101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527101).length < 2 ^ (prefixWord ++ tailWord_7527101).sum := by decide
  have hdescent : baseEnd_7527101 < baseStart_7527101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527160 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_7527160 : Nat := 118140960795 + 7527160 * 2 ^ 59
def prefixEnd_7527160 : Nat := 4983230072969 + 3 ^ 40 * 7527160 * 2
def baseEnd_7527160 : Nat := 3865051043296875185583227

theorem tailTrace_7527160 : CollatzResearch.WordTrace tailWord_7527160 prefixEnd_7527160 3865051043296875185583227 := by
  unfold tailWord_7527160
  simp only [CollatzResearch.WordTrace]
  refine ⟨137269039705196165713157467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183025386273594887617543289 137269039705196165713157467)
  ·
    refine ⟨205903559557794248569736201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137269039705196165713157467 205903559557794248569736201)
    ·
      refine ⟨154427669668345686427302151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205903559557794248569736201 154427669668345686427302151)
      ·
        refine ⟨231641504502518529640953227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154427669668345686427302151 231641504502518529640953227)
        ·
          refine ⟨347462256753777794461429841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231641504502518529640953227 347462256753777794461429841)
          ·
            refine ⟨260596692565333345846072381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347462256753777794461429841 260596692565333345846072381)
            ·
              refine ⟨97723759712000004692277143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260596692565333345846072381 97723759712000004692277143)
              ·
                refine ⟨146585639568000007038415715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97723759712000004692277143 146585639568000007038415715)
                ·
                  refine ⟨219878459352000010557623573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146585639568000007038415715 219878459352000010557623573)
                  ·
                    refine ⟨10306802782125000494888605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 219878459352000010557623573 10306802782125000494888605)
                    ·
                      refine ⟨3865051043296875185583227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10306802782125000494888605 3865051043296875185583227)
                      ·
                        rfl

theorem cell23_7527160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_7527160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527160 prefixEnd_7527160 := by exact prefixLift 7527160
  have htrace : WordTrace (prefixWord ++ tailWord_7527160) baseStart_7527160 baseEnd_7527160 := by
    simpa [prefixWord, tailWord_7527160, baseEnd_7527160] using wordTrace_append hprefix tailTrace_7527160
  have hstable : (prefixWord ++ tailWord_7527160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527160).length < 2 ^ (prefixWord ++ tailWord_7527160).sum := by decide
  have hdescent : baseEnd_7527160 < baseStart_7527160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527214 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_7527214 : Nat := 118140960795 + 7527214 * 2 ^ 59
def prefixEnd_7527214 : Nat := 4983230072969 + 3 ^ 40 * 7527214 * 2
def baseEnd_7527214 : Nat := 429453196805801997145331

theorem tailTrace_7527214 : CollatzResearch.WordTrace tailWord_7527214 prefixEnd_7527214 429453196805801997145331 := by
  unfold tailWord_7527214
  simp only [CollatzResearch.WordTrace]
  refine ⟨34317506119024587331097587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183026699301464465765853797 34317506119024587331097587)
  ·
    refine ⟨51476259178536880996646381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34317506119024587331097587 51476259178536880996646381)
    ·
      refine ⟨19303597191951330373742393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51476259178536880996646381 19303597191951330373742393)
      ·
        refine ⟨14477697893963497780306795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19303597191951330373742393 14477697893963497780306795)
        ·
          refine ⟨21716546840945246670460193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14477697893963497780306795 21716546840945246670460193)
          ·
            refine ⟨16287410130708935002845145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21716546840945246670460193 16287410130708935002845145)
            ·
              refine ⟨12215557598031701252133859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16287410130708935002845145 12215557598031701252133859)
              ·
                refine ⟨18323336397047551878200789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12215557598031701252133859 18323336397047551878200789)
                ·
                  refine ⟨429453196805801997145331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18323336397047551878200789 429453196805801997145331)
                  ·
                    rfl

theorem cell23_7527214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_7527214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527214 prefixEnd_7527214 := by exact prefixLift 7527214
  have htrace : WordTrace (prefixWord ++ tailWord_7527214) baseStart_7527214 baseEnd_7527214 := by
    simpa [prefixWord, tailWord_7527214, baseEnd_7527214] using wordTrace_append hprefix tailTrace_7527214
  have hstable : (prefixWord ++ tailWord_7527214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527214).length < 2 ^ (prefixWord ++ tailWord_7527214).sum := by decide
  have hdescent : baseEnd_7527214 < baseStart_7527214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527240 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_7527240 : Nat := 118140960795 + 7527240 * 2 ^ 59
def prefixEnd_7527240 : Nat := 4983230072969 + 3 ^ 40 * 7527240 * 2
def baseEnd_7527240 : Nat := 1288364040583078290860953

theorem tailTrace_7527240 : CollatzResearch.WordTrace tailWord_7527240 prefixEnd_7527240 1288364040583078290860953 := by
  unfold tailWord_7527240
  simp only [CollatzResearch.WordTrace]
  refine ⟨137270498625051252544613587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183027331500068336726151449 137270498625051252544613587)
  ·
    refine ⟨205905747937576878816920381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137270498625051252544613587 205905747937576878816920381)
    ·
      refine ⟨77214655476591329556345143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205905747937576878816920381 77214655476591329556345143)
      ·
        refine ⟨115821983214886994334517715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77214655476591329556345143 115821983214886994334517715)
        ·
          refine ⟨173732974822330491501776573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115821983214886994334517715 173732974822330491501776573)
          ·
            refine ⟨65149865558373934313166215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173732974822330491501776573 65149865558373934313166215)
            ·
              refine ⟨97724798337560901469749323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65149865558373934313166215 97724798337560901469749323)
              ·
                refine ⟨146587197506341352204623985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97724798337560901469749323 146587197506341352204623985)
                ·
                  refine ⟨109940398129756014153467989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146587197506341352204623985 109940398129756014153467989)
                  ·
                    refine ⟨1288364040583078290860953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109940398129756014153467989 1288364040583078290860953)
                    ·
                      rfl

theorem cell23_7527240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_7527240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527240 prefixEnd_7527240 := by exact prefixLift 7527240
  have htrace : WordTrace (prefixWord ++ tailWord_7527240) baseStart_7527240 baseEnd_7527240 := by
    simpa [prefixWord, tailWord_7527240, baseEnd_7527240] using wordTrace_append hprefix tailTrace_7527240
  have hstable : (prefixWord ++ tailWord_7527240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527240).length < 2 ^ (prefixWord ++ tailWord_7527240).sum := by decide
  have hdescent : baseEnd_7527240 < baseStart_7527240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527337 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_7527337 : Nat := 118140960795 + 7527337 * 2 ^ 59
def prefixEnd_7527337 : Nat := 4983230072969 + 3 ^ 40 * 7527337 * 2
def baseEnd_7527337 : Nat := 3865141929372720993069913

theorem tailTrace_7527337 : CollatzResearch.WordTrace tailWord_7527337 prefixEnd_7527337 3865141929372720993069913 := by
  unfold tailWord_7527337
  simp only [CollatzResearch.WordTrace]
  refine ⟨274544535130751090655508265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183029690087167393770338843 274544535130751090655508265)
  ·
    refine ⟨205908401348063317991631199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274544535130751090655508265 205908401348063317991631199)
    ·
      refine ⟨308862602022094976987446799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205908401348063317991631199 308862602022094976987446799)
      ·
        refine ⟨463293903033142465481170199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308862602022094976987446799 463293903033142465481170199)
        ·
          refine ⟨694940854549713698221755299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463293903033142465481170199 694940854549713698221755299)
          ·
            refine ⟨1042411281824570547332632949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694940854549713698221755299 1042411281824570547332632949)
            ·
              refine ⟨97726057671053488812434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1042411281824570547332632949 97726057671053488812434339)
              ·
                refine ⟨146589086506580233218651509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97726057671053488812434339 146589086506580233218651509)
                ·
                  refine ⟨13742726859991896864248579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146589086506580233218651509 13742726859991896864248579)
                  ·
                    refine ⟨20614090289987845296372869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13742726859991896864248579 20614090289987845296372869)
                    ·
                      refine ⟨3865141929372720993069913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20614090289987845296372869 3865141929372720993069913)
                      ·
                        rfl

theorem cell23_7527337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_7527337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527337 prefixEnd_7527337 := by exact prefixLift 7527337
  have htrace : WordTrace (prefixWord ++ tailWord_7527337) baseStart_7527337 baseEnd_7527337 := by
    simpa [prefixWord, tailWord_7527337, baseEnd_7527337] using wordTrace_append hprefix tailTrace_7527337
  have hstable : (prefixWord ++ tailWord_7527337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527337).length < 2 ^ (prefixWord ++ tailWord_7527337).sum := by decide
  have hdescent : baseEnd_7527337 < baseStart_7527337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527348 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_7527348 : Nat := 118140960795 + 7527348 * 2 ^ 59
def prefixEnd_7527348 : Nat := 4983230072969 + 3 ^ 40 * 7527348 * 2
def baseEnd_7527348 : Nat := 3865147577659920450032363

theorem tailTrace_7527348 : CollatzResearch.WordTrace tailWord_7527348 prefixEnd_7527348 3865147577659920450032363 := by
  unfold tailWord_7527348
  simp only [CollatzResearch.WordTrace]
  refine ⟨137272468166855619767079349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183029957555807493022772465 137272468166855619767079349)
  ·
    refine ⟨12869293890642714353163689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137272468166855619767079349 12869293890642714353163689)
    ·
      refine ⟨9651970417982035764872767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12869293890642714353163689 9651970417982035764872767)
      ·
        refine ⟨14477955626973053647309151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651970417982035764872767 14477955626973053647309151)
        ·
          refine ⟨21716933440459580470963727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14477955626973053647309151 21716933440459580470963727)
          ·
            refine ⟨32575400160689370706445591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21716933440459580470963727 32575400160689370706445591)
            ·
              refine ⟨48863100241034056059668387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32575400160689370706445591 48863100241034056059668387)
              ·
                refine ⟨73294650361551084089502581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48863100241034056059668387 73294650361551084089502581)
                ·
                  refine ⟨6871373471395414133390867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73294650361551084089502581 6871373471395414133390867)
                  ·
                    refine ⟨10307060207093121200086301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6871373471395414133390867 10307060207093121200086301)
                    ·
                      refine ⟨3865147577659920450032363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10307060207093121200086301 3865147577659920450032363)
                      ·
                        rfl

theorem cell23_7527348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_7527348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527348 prefixEnd_7527348 := by exact prefixLift 7527348
  have htrace : WordTrace (prefixWord ++ tailWord_7527348) baseStart_7527348 baseEnd_7527348 := by
    simpa [prefixWord, tailWord_7527348, baseEnd_7527348] using wordTrace_append hprefix tailTrace_7527348
  have hstable : (prefixWord ++ tailWord_7527348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527348).length < 2 ^ (prefixWord ++ tailWord_7527348).sum := by decide
  have hdescent : baseEnd_7527348 < baseStart_7527348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527354 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_7527354 : Nat := 118140960795 + 7527354 * 2 ^ 59
def prefixEnd_7527354 : Nat := 4983230072969 + 3 ^ 40 * 7527354 * 2
def baseEnd_7527354 : Nat := 3865150658543847426557335

theorem tailTrace_7527354 : CollatzResearch.WordTrace tailWord_7527354 prefixEnd_7527354 3865150658543847426557335 := by
  unfold tailWord_7527354
  simp only [CollatzResearch.WordTrace]
  refine ⟨68636288792922375639719279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183030103447793001705918077 68636288792922375639719279)
  ·
    refine ⟨102954433189383563459578919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68636288792922375639719279 102954433189383563459578919)
    ·
      refine ⟨154431649784075345189368379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102954433189383563459578919 154431649784075345189368379)
      ·
        refine ⟨231647474676113017784052569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154431649784075345189368379 231647474676113017784052569)
        ·
          refine ⟨173735606007084763338039427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231647474676113017784052569 173735606007084763338039427)
          ·
            refine ⟨260603409010627145007059141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173735606007084763338039427 260603409010627145007059141)
            ·
              refine ⟨48863139189492589688823589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260603409010627145007059141 48863139189492589688823589)
              ·
                refine ⟨9161838598029860566654423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48863139189492589688823589 9161838598029860566654423)
                ·
                  refine ⟨13742757897044790849981635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161838598029860566654423 13742757897044790849981635)
                  ·
                    refine ⟨20614136845567186274972453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13742757897044790849981635 20614136845567186274972453)
                    ·
                      refine ⟨3865150658543847426557335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20614136845567186274972453 3865150658543847426557335)
                      ·
                        rfl

theorem cell23_7527354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_7527354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527354 prefixEnd_7527354 := by exact prefixLift 7527354
  have htrace : WordTrace (prefixWord ++ tailWord_7527354) baseStart_7527354 baseEnd_7527354 := by
    simpa [prefixWord, tailWord_7527354, baseEnd_7527354] using wordTrace_append hprefix tailTrace_7527354
  have hstable : (prefixWord ++ tailWord_7527354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527354).length < 2 ^ (prefixWord ++ tailWord_7527354).sum := by decide
  have hdescent : baseEnd_7527354 < baseStart_7527354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527368 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 1, 5]
def baseStart_7527368 : Nat := 118140960795 + 7527368 * 2 ^ 59
def prefixEnd_7527368 : Nat := 4983230072969 + 3 ^ 40 * 7527368 * 2
def baseEnd_7527368 : Nat := 1288385949091003457260757

theorem tailTrace_7527368 : CollatzResearch.WordTrace tailWord_7527368 prefixEnd_7527368 1288385949091003457260757 := by
  unfold tailWord_7527368
  simp only [CollatzResearch.WordTrace]
  refine ⟨137272832896819391474943379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183030443862425855299924505 137272832896819391474943379)
  ·
    refine ⟨205909249345229087212415069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137272832896819391474943379 205909249345229087212415069)
    ·
      refine ⟨77215968504460907704655651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205909249345229087212415069 77215968504460907704655651)
      ·
        refine ⟨115823952756691361556983477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77215968504460907704655651 115823952756691361556983477)
        ·
          refine ⟨10858495570939815145967201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115823952756691361556983477 10858495570939815145967201)
          ·
            refine ⟨8143871678204861359475401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858495570939815145967201 8143871678204861359475401)
            ·
              refine ⟨6107903758653646019606551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143871678204861359475401 6107903758653646019606551)
              ·
                refine ⟨9161855637980469029409827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107903758653646019606551 9161855637980469029409827)
                ·
                  refine ⟨13742783456970703544114741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161855637980469029409827 13742783456970703544114741)
                  ·
                    refine ⟨1288385949091003457260757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13742783456970703544114741 1288385949091003457260757)
                    ·
                      rfl

theorem cell23_7527368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_7527368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527368 prefixEnd_7527368 := by exact prefixLift 7527368
  have htrace : WordTrace (prefixWord ++ tailWord_7527368) baseStart_7527368 baseEnd_7527368 := by
    simpa [prefixWord, tailWord_7527368, baseEnd_7527368] using wordTrace_append hprefix tailTrace_7527368
  have hstable : (prefixWord ++ tailWord_7527368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527368).length < 2 ^ (prefixWord ++ tailWord_7527368).sum := by decide
  have hdescent : baseEnd_7527368 < baseStart_7527368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527371 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 1, 1, 4]
def baseStart_7527371 : Nat := 118140960795 + 7527371 * 2 ^ 59
def prefixEnd_7527371 : Nat := 4983230072969 + 3 ^ 40 * 7527371 * 2
def baseEnd_7527371 : Nat := 3865159387714973860044757

theorem tailTrace_7527371 : CollatzResearch.WordTrace tailWord_7527371 prefixEnd_7527371 3865159387714973860044757 := by
  unfold tailWord_7527371
  simp only [CollatzResearch.WordTrace]
  refine ⟨274545775212627914462245967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183030516808418609641497311 274545775212627914462245967)
  ·
    refine ⟨411818662818941871693368951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274545775212627914462245967 411818662818941871693368951)
    ·
      refine ⟨617727994228412807540053427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411818662818941871693368951 617727994228412807540053427)
      ·
        refine ⟨926591991342619211310080141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617727994228412807540053427 926591991342619211310080141)
        ·
          refine ⟨347471996753482204241280053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 926591991342619211310080141 347471996753482204241280053)
          ·
            refine ⟨32575499695638956647620005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347471996753482204241280053 32575499695638956647620005)
            ·
              refine ⟨6107906192932304371428751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32575499695638956647620005 6107906192932304371428751)
              ·
                refine ⟨9161859289398456557143127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107906192932304371428751 9161859289398456557143127)
                ·
                  refine ⟨13742788934097684835714691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161859289398456557143127 13742788934097684835714691)
                  ·
                    refine ⟨20614183401146527253572037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13742788934097684835714691 20614183401146527253572037)
                    ·
                      refine ⟨3865159387714973860044757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20614183401146527253572037 3865159387714973860044757)
                      ·
                        rfl

theorem cell23_7527371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 1, 4].length) (baseStart_7527371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527371 prefixEnd_7527371 := by exact prefixLift 7527371
  have htrace : WordTrace (prefixWord ++ tailWord_7527371) baseStart_7527371 baseEnd_7527371 := by
    simpa [prefixWord, tailWord_7527371, baseEnd_7527371] using wordTrace_append hprefix tailTrace_7527371
  have hstable : (prefixWord ++ tailWord_7527371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527371).length < 2 ^ (prefixWord ++ tailWord_7527371).sum := by decide
  have hdescent : baseEnd_7527371 < baseStart_7527371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527381 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_7527381 : Nat := 118140960795 + 7527381 * 2 ^ 59
def prefixEnd_7527381 : Nat := 4983230072969 + 3 ^ 40 * 7527381 * 2
def baseEnd_7527381 : Nat := 1288388174173839606973237

theorem tailTrace_7527381 : CollatzResearch.WordTrace tailWord_7527381 prefixEnd_7527381 1288388174173839606973237 := by
  unfold tailWord_7527381
  simp only [CollatzResearch.WordTrace]
  refine ⟨274546139942591686170109997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183030759961727790780073331 274546139942591686170109997)
  ·
    refine ⟨102954802478471882313791249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274546139942591686170109997 102954802478471882313791249)
    ·
      refine ⟨77216101858853911735343437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102954802478471882313791249 77216101858853911735343437)
      ·
        refine ⟨28956038197070216900753789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77216101858853911735343437 28956038197070216900753789)
        ·
          refine ⟨10858514323901331337782671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28956038197070216900753789 10858514323901331337782671)
          ·
            refine ⟨16287771485851997006674007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10858514323901331337782671 16287771485851997006674007)
            ·
              refine ⟨24431657228777995510011011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16287771485851997006674007 24431657228777995510011011)
              ·
                refine ⟨36647485843166993265016517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24431657228777995510011011 36647485843166993265016517)
                ·
                  refine ⟨6871403595593811237190597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36647485843166993265016517 6871403595593811237190597)
                  ·
                    refine ⟨1288388174173839606973237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871403595593811237190597 1288388174173839606973237)
                    ·
                      rfl

theorem cell23_7527381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_7527381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527381 prefixEnd_7527381 := by exact prefixLift 7527381
  have htrace : WordTrace (prefixWord ++ tailWord_7527381) baseStart_7527381 baseEnd_7527381 := by
    simpa [prefixWord, tailWord_7527381, baseEnd_7527381] using wordTrace_append hprefix tailTrace_7527381
  have hstable : (prefixWord ++ tailWord_7527381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527381).length < 2 ^ (prefixWord ++ tailWord_7527381).sum := by decide
  have hdescent : baseEnd_7527381 < baseStart_7527381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527417 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_7527417 : Nat := 118140960795 + 7527417 * 2 ^ 59
def prefixEnd_7527417 : Nat := 4983230072969 + 3 ^ 40 * 7527417 * 2
def baseEnd_7527417 : Nat := 3865183007825080680069545

theorem tailTrace_7527417 : CollatzResearch.WordTrace tailWord_7527417 prefixEnd_7527417 3865183007825080680069545 := by
  unfold tailWord_7527417
  simp only [CollatzResearch.WordTrace]
  refine ⟨274547452970461264318420505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183031635313640842878947003 274547452970461264318420505)
  ·
    refine ⟨205910589727845948238815379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274547452970461264318420505 205910589727845948238815379)
    ·
      refine ⟨308865884591768922358223069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205910589727845948238815379 308865884591768922358223069)
      ·
        refine ⟨115824706721913345884333651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308865884591768922358223069 115824706721913345884333651)
        ·
          refine ⟨173737060082870018826500477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115824706721913345884333651 173737060082870018826500477)
          ·
            refine ⟨65151397531076257059937679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173737060082870018826500477 65151397531076257059937679)
            ·
              refine ⟨97727096296614385589906519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65151397531076257059937679 97727096296614385589906519)
              ·
                refine ⟨146590644444921578384859779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97727096296614385589906519 146590644444921578384859779)
                ·
                  refine ⟨219885966667382367577289669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146590644444921578384859779 219885966667382367577289669)
                  ·
                    refine ⟨41228618750134193920741813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219885966667382367577289669 41228618750134193920741813)
                    ·
                      refine ⟨3865183007825080680069545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41228618750134193920741813 3865183007825080680069545)
                      ·
                        rfl

theorem cell23_7527417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_7527417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527417 prefixEnd_7527417 := by exact prefixLift 7527417
  have htrace : WordTrace (prefixWord ++ tailWord_7527417) baseStart_7527417 baseEnd_7527417 := by
    simpa [prefixWord, tailWord_7527417, baseEnd_7527417] using wordTrace_append hprefix tailTrace_7527417
  have hstable : (prefixWord ++ tailWord_7527417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527417).length < 2 ^ (prefixWord ++ tailWord_7527417).sum := by decide
  have hdescent : baseEnd_7527417 < baseStart_7527417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527427 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_7527427 : Nat := 118140960795 + 7527427 * 2 ^ 59
def prefixEnd_7527427 : Nat := 4983230072969 + 3 ^ 40 * 7527427 * 2
def baseEnd_7527427 : Nat := 3865188142631625640944499

theorem tailTrace_7527427 : CollatzResearch.WordTrace tailWord_7527427 prefixEnd_7527427 3865188142631625640944499 := by
  unfold tailWord_7527427
  simp only [CollatzResearch.WordTrace]
  refine ⟨274547817700425036026284535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183031878466950024017523023 274547817700425036026284535)
  ·
    refine ⟨411821726550637554039426803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274547817700425036026284535 411821726550637554039426803)
    ·
      refine ⟨617732589825956331059140205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411821726550637554039426803 617732589825956331059140205)
      ·
        refine ⟨231649721184733624147177577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617732589825956331059140205 231649721184733624147177577)
        ·
          refine ⟨173737290888550218110383183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231649721184733624147177577 173737290888550218110383183)
          ·
            refine ⟨260605936332825327165574775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173737290888550218110383183 260605936332825327165574775)
            ·
              refine ⟨390908904499237990748362163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260605936332825327165574775 390908904499237990748362163)
              ·
                refine ⟨586363356748856986122543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390908904499237990748362163 586363356748856986122543245)
                ·
                  refine ⟨219886258780821369795953717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 586363356748856986122543245 219886258780821369795953717)
                  ·
                    refine ⟨20614336760702003418370661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 219886258780821369795953717 20614336760702003418370661)
                    ·
                      refine ⟨3865188142631625640944499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20614336760702003418370661 3865188142631625640944499)
                      ·
                        rfl

theorem cell23_7527427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_7527427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527427 prefixEnd_7527427 := by exact prefixLift 7527427
  have htrace : WordTrace (prefixWord ++ tailWord_7527427) baseStart_7527427 baseEnd_7527427 := by
    simpa [prefixWord, tailWord_7527427, baseEnd_7527427] using wordTrace_append hprefix tailTrace_7527427
  have hstable : (prefixWord ++ tailWord_7527427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527427).length < 2 ^ (prefixWord ++ tailWord_7527427).sum := by decide
  have hdescent : baseEnd_7527427 < baseStart_7527427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527455 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 2, 1, 3]
def baseStart_7527455 : Nat := 118140960795 + 7527455 * 2 ^ 59
def prefixEnd_7527455 : Nat := 4983230072969 + 3 ^ 40 * 7527455 * 2
def baseEnd_7527455 : Nat := 3865202520089951531394371

theorem tailTrace_7527455 : CollatzResearch.WordTrace tailWord_7527455 prefixEnd_7527455 3865202520089951531394371 := by
  unfold tailWord_7527455
  simp only [CollatzResearch.WordTrace]
  refine ⟨274548838944323596808303819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183032559296215731205535879 274548838944323596808303819)
  ·
    refine ⟨411823258416485395212455729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274548838944323596808303819 411823258416485395212455729)
    ·
      refine ⟨308867443812364046409341797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411823258416485395212455729 308867443812364046409341797)
      ·
        refine ⟨57912645714818258701751587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308867443812364046409341797 57912645714818258701751587)
        ·
          refine ⟨86868968572227388052627381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57912645714818258701751587 86868968572227388052627381)
          ·
            refine ⟨8143965803646317629933817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86868968572227388052627381 8143965803646317629933817)
            ·
              refine ⟨6107974352734738222450363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143965803646317629933817 6107974352734738222450363)
              ·
                refine ⟨9161961529102107333675545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107974352734738222450363 9161961529102107333675545)
                ·
                  refine ⟨6871471146826580500256659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161961529102107333675545 6871471146826580500256659)
                  ·
                    refine ⟨10307206720239870750384989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6871471146826580500256659 10307206720239870750384989)
                    ·
                      refine ⟨3865202520089951531394371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10307206720239870750384989 3865202520089951531394371)
                      ·
                        rfl

theorem cell23_7527455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_7527455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527455 prefixEnd_7527455 := by exact prefixLift 7527455
  have htrace : WordTrace (prefixWord ++ tailWord_7527455) baseStart_7527455 baseEnd_7527455 := by
    simpa [prefixWord, tailWord_7527455, baseEnd_7527455] using wordTrace_append hprefix tailTrace_7527455
  have hstable : (prefixWord ++ tailWord_7527455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527455).length < 2 ^ (prefixWord ++ tailWord_7527455).sum := by decide
  have hdescent : baseEnd_7527455 < baseStart_7527455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527461 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_7527461 : Nat := 118140960795 + 7527461 * 2 ^ 59
def prefixEnd_7527461 : Nat := 4983230072969 + 3 ^ 40 * 7527461 * 2
def baseEnd_7527461 : Nat := 3865205600973878507919343

theorem tailTrace_7527461 : CollatzResearch.WordTrace tailWord_7527461 prefixEnd_7527461 3865205600973878507919343 := by
  unfold tailWord_7527461
  simp only [CollatzResearch.WordTrace]
  refine ⟨274549057782301859833022237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183032705188201239888681491 274549057782301859833022237)
  ·
    refine ⟨102955896668363197437383339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274549057782301859833022237 102955896668363197437383339)
    ·
      refine ⟨154433845002544796156075009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102955896668363197437383339 154433845002544796156075009)
      ·
        refine ⟨115825383751908597117056257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154433845002544796156075009 115825383751908597117056257)
        ·
          refine ⟨86869037813931447837792193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115825383751908597117056257 86869037813931447837792193)
          ·
            refine ⟨65151778360448585878344145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86869037813931447837792193 65151778360448585878344145)
            ·
              refine ⟨48863833770336439408758109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65151778360448585878344145 48863833770336439408758109)
              ·
                refine ⟨18323937663876164778284291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48863833770336439408758109 18323937663876164778284291)
                ·
                  refine ⟨27485906495814247167426437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18323937663876164778284291 27485906495814247167426437)
                  ·
                    refine ⟨5153607467965171343892457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27485906495814247167426437 5153607467965171343892457)
                    ·
                      refine ⟨3865205600973878507919343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153607467965171343892457 3865205600973878507919343)
                      ·
                        rfl

theorem cell23_7527461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_7527461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527461 prefixEnd_7527461 := by exact prefixLift 7527461
  have htrace : WordTrace (prefixWord ++ tailWord_7527461) baseStart_7527461 baseEnd_7527461 := by
    simpa [prefixWord, tailWord_7527461, baseEnd_7527461] using wordTrace_append hprefix tailTrace_7527461
  have hstable : (prefixWord ++ tailWord_7527461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527461).length < 2 ^ (prefixWord ++ tailWord_7527461).sum := by decide
  have hdescent : baseEnd_7527461 < baseStart_7527461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527467 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 9]
def baseStart_7527467 : Nat := 118140960795 + 7527467 * 2 ^ 59
def prefixEnd_7527467 : Nat := 4983230072969 + 3 ^ 40 * 7527467 * 2
def baseEnd_7527467 : Nat := 429467631317533942716035

theorem tailTrace_7527467 : CollatzResearch.WordTrace tailWord_7527467 prefixEnd_7527467 429467631317533942716035 := by
  unfold tailWord_7527467
  simp only [CollatzResearch.WordTrace]
  refine ⟨274549276620280122857740655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183032851080186748571827103 274549276620280122857740655)
  ·
    refine ⟨411823914930420184286610983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274549276620280122857740655 411823914930420184286610983)
    ·
      refine ⟨617735872395630276429916475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411823914930420184286610983 617735872395630276429916475)
      ·
        refine ⟨926603808593445414644874713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617735872395630276429916475 926603808593445414644874713)
        ·
          refine ⟨694952856445084060983656035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926603808593445414644874713 694952856445084060983656035)
          ·
            refine ⟨1042429284667626091475484053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694952856445084060983656035 1042429284667626091475484053)
            ·
              refine ⟨48863872718794973037913315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1042429284667626091475484053 48863872718794973037913315)
              ·
                refine ⟨73295809078192459556869973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48863872718794973037913315 73295809078192459556869973)
                ·
                  refine ⟨429467631317533942716035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73295809078192459556869973 429467631317533942716035)
                  ·
                    rfl

theorem cell23_7527467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 9].length) (baseStart_7527467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527467 prefixEnd_7527467 := by exact prefixLift 7527467
  have htrace : WordTrace (prefixWord ++ tailWord_7527467) baseStart_7527467 baseEnd_7527467 := by
    simpa [prefixWord, tailWord_7527467, baseEnd_7527467] using wordTrace_append hprefix tailTrace_7527467
  have hstable : (prefixWord ++ tailWord_7527467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527467).length < 2 ^ (prefixWord ++ tailWord_7527467).sum := by decide
  have hdescent : baseEnd_7527467 < baseStart_7527467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527478 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7527478 : Nat := 118140960795 + 7527478 * 2 ^ 59
def prefixEnd_7527478 : Nat := 4983230072969 + 3 ^ 40 * 7527478 * 2
def baseEnd_7527478 : Nat := 3865214330145004941406765

theorem tailTrace_7527478 : CollatzResearch.WordTrace tailWord_7527478 prefixEnd_7527478 3865214330145004941406765 := by
  unfold tailWord_7527478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159354863952516983524443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183033118548826847824260725 17159354863952516983524443)
  ·
    refine ⟨25739032295928775475286665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17159354863952516983524443 25739032295928775475286665)
    ·
      refine ⟨19304274221946581606464999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25739032295928775475286665 19304274221946581606464999)
      ·
        refine ⟨28956411332919872409697499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19304274221946581606464999 28956411332919872409697499)
        ·
          refine ⟨43434616999379808614546249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28956411332919872409697499 43434616999379808614546249)
          ·
            refine ⟨32575962749534856460909687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43434616999379808614546249 32575962749534856460909687)
            ·
              refine ⟨48863944124302284691364531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32575962749534856460909687 48863944124302284691364531)
              ·
                refine ⟨73295916186453427037046797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48863944124302284691364531 73295916186453427037046797)
                ·
                  refine ⟨27485968569920035138892549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73295916186453427037046797 27485968569920035138892549)
                  ·
                    refine ⟨5153619106860006588542353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27485968569920035138892549 5153619106860006588542353)
                    ·
                      refine ⟨3865214330145004941406765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153619106860006588542353 3865214330145004941406765)
                      ·
                        rfl

theorem cell23_7527478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7527478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527478 prefixEnd_7527478 := by exact prefixLift 7527478
  have htrace : WordTrace (prefixWord ++ tailWord_7527478) baseStart_7527478 baseEnd_7527478 := by
    simpa [prefixWord, tailWord_7527478, baseEnd_7527478] using wordTrace_append hprefix tailTrace_7527478
  have hstable : (prefixWord ++ tailWord_7527478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527478).length < 2 ^ (prefixWord ++ tailWord_7527478).sum := by decide
  have hdescent : baseEnd_7527478 < baseStart_7527478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527495 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_7527495 : Nat := 118140960795 + 7527495 * 2 ^ 59
def prefixEnd_7527495 : Nat := 4983230072969 + 3 ^ 40 * 7527495 * 2
def baseEnd_7527495 : Nat := 3865223059316131374894187

theorem tailTrace_7527495 : CollatzResearch.WordTrace tailWord_7527495 prefixEnd_7527495 3865223059316131374894187 := by
  unfold tailWord_7527495
  simp only [CollatzResearch.WordTrace]
  refine ⟨274550297864178683639759939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183033531909452455759839959 274550297864178683639759939)
  ·
    refine ⟨411825446796268025459639909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274550297864178683639759939 411825446796268025459639909)
    ·
      refine ⟨77217271274300254773682483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411825446796268025459639909 77217271274300254773682483)
      ·
        refine ⟨115825906911450382160523725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77217271274300254773682483 115825906911450382160523725)
        ·
          refine ⟨43434715091793893310196397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115825906911450382160523725 43434715091793893310196397)
          ·
            refine ⟨16288018159422709991323649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43434715091793893310196397 16288018159422709991323649)
            ·
              refine ⟨12216013619567032493492737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16288018159422709991323649 12216013619567032493492737)
              ·
                refine ⟨9162010214675274370119553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12216013619567032493492737 9162010214675274370119553)
                ·
                  refine ⟨6871507661006455777589665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9162010214675274370119553 6871507661006455777589665)
                  ·
                    refine ⟨5153630745754841833192249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6871507661006455777589665 5153630745754841833192249)
                    ·
                      refine ⟨3865223059316131374894187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153630745754841833192249 3865223059316131374894187)
                      ·
                        rfl

theorem cell23_7527495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_7527495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527495 prefixEnd_7527495 := by exact prefixLift 7527495
  have htrace : WordTrace (prefixWord ++ tailWord_7527495) baseStart_7527495 baseEnd_7527495 := by
    simpa [prefixWord, tailWord_7527495, baseEnd_7527495] using wordTrace_append hprefix tailTrace_7527495
  have hstable : (prefixWord ++ tailWord_7527495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527495).length < 2 ^ (prefixWord ++ tailWord_7527495).sum := by decide
  have hdescent : baseEnd_7527495 < baseStart_7527495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527518 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7527518 : Nat := 118140960795 + 7527518 * 2 ^ 59
def prefixEnd_7527518 : Nat := 4983230072969 + 3 ^ 40 * 7527518 * 2
def baseEnd_7527518 : Nat := 429470541041242753878509

theorem tailTrace_7527518 : CollatzResearch.WordTrace tailWord_7527518 prefixEnd_7527518 429470541041242753878509 := by
  unfold tailWord_7527518
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318892092886919820980901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183034091162063572378564805 34318892092886919820980901)
  ·
    refine ⟨6434792267416297466433919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34318892092886919820980901 6434792267416297466433919)
    ·
      refine ⟨9652188401124446199650879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434792267416297466433919 9652188401124446199650879)
      ·
        refine ⟨14478282601686669299476319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652188401124446199650879 14478282601686669299476319)
        ·
          refine ⟨21717423902530003949214479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478282601686669299476319 21717423902530003949214479)
          ·
            refine ⟨32576135853795005923821719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717423902530003949214479 32576135853795005923821719)
            ·
              refine ⟨48864203780692508885732579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32576135853795005923821719 48864203780692508885732579)
              ·
                refine ⟨73296305671038763328598869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48864203780692508885732579 73296305671038763328598869)
                ·
                  refine ⟨429470541041242753878509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73296305671038763328598869 429470541041242753878509)
                  ·
                    rfl

theorem cell23_7527518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7527518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527518 prefixEnd_7527518 := by exact prefixLift 7527518
  have htrace : WordTrace (prefixWord ++ tailWord_7527518) baseStart_7527518 baseEnd_7527518 := by
    simpa [prefixWord, tailWord_7527518, baseEnd_7527518] using wordTrace_append hprefix tailTrace_7527518
  have hstable : (prefixWord ++ tailWord_7527518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527518).length < 2 ^ (prefixWord ++ tailWord_7527518).sum := by decide
  have hdescent : baseEnd_7527518 < baseStart_7527518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527561 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_7527561 : Nat := 118140960795 + 7527561 * 2 ^ 59
def prefixEnd_7527561 : Nat := 4983230072969 + 3 ^ 40 * 7527561 * 2
def baseEnd_7527561 : Nat := 1288418983013109372222961

theorem tailTrace_7527561 : CollatzResearch.WordTrace tailWord_7527561 prefixEnd_7527561 1288418983013109372222961 := by
  unfold tailWord_7527561
  simp only [CollatzResearch.WordTrace]
  refine ⟨274552705081939576911662537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183035136721293051274441691 274552705081939576911662537)
  ·
    refine ⟨205914528811454682683746903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274552705081939576911662537 205914528811454682683746903)
    ·
      refine ⟨308871793217182024025620355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205914528811454682683746903 308871793217182024025620355)
      ·
        refine ⟨463307689825773036038430533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308871793217182024025620355 463307689825773036038430533)
        ·
          refine ⟨86870191842332444257205725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463307689825773036038430533 86870191842332444257205725)
          ·
            refine ⟨32576321940874666596452147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86870191842332444257205725 32576321940874666596452147)
            ·
              refine ⟨48864482911311999894678221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32576321940874666596452147 48864482911311999894678221)
              ·
                refine ⟨18324181091741999960504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48864482911311999894678221 18324181091741999960504333)
                ·
                  refine ⟨6871567909403249985189125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18324181091741999960504333 6871567909403249985189125)
                  ·
                    refine ⟨1288418983013109372222961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871567909403249985189125 1288418983013109372222961)
                    ·
                      rfl

theorem cell23_7527561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_7527561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527561 prefixEnd_7527561 := by exact prefixLift 7527561
  have htrace : WordTrace (prefixWord ++ tailWord_7527561) baseStart_7527561 baseEnd_7527561 := by
    simpa [prefixWord, tailWord_7527561, baseEnd_7527561] using wordTrace_append hprefix tailTrace_7527561
  have hstable : (prefixWord ++ tailWord_7527561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527561).length < 2 ^ (prefixWord ++ tailWord_7527561).sum := by decide
  have hdescent : baseEnd_7527561 < baseStart_7527561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527578 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_7527578 : Nat := 118140960795 + 7527578 * 2 ^ 59
def prefixEnd_7527578 : Nat := 4983230072969 + 3 ^ 40 * 7527578 * 2
def baseEnd_7527578 : Nat := 1288421892736818183385435

theorem tailTrace_7527578 : CollatzResearch.WordTrace tailWord_7527578 prefixEnd_7527578 1288421892736818183385435 := by
  unfold tailWord_7527578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68638331280719497203757847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183035550081918659210020925 68638331280719497203757847)
  ·
    refine ⟨102957496921079245805636771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68638331280719497203757847 102957496921079245805636771)
    ·
      refine ⟨154436245381618868708455157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102957496921079245805636771 154436245381618868708455157)
      ·
        refine ⟨14478398004526768941417671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154436245381618868708455157 14478398004526768941417671)
        ·
          refine ⟨21717597006790153412126507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478398004526768941417671 21717597006790153412126507)
          ·
            refine ⟨32576395510185230118189761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717597006790153412126507 32576395510185230118189761)
            ·
              refine ⟨24432296632638922588642321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32576395510185230118189761 24432296632638922588642321)
              ·
                refine ⟨18324222474479191941481741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24432296632638922588642321 18324222474479191941481741)
                ·
                  refine ⟨6871583427929696978055653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18324222474479191941481741 6871583427929696978055653)
                  ·
                    refine ⟨1288421892736818183385435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871583427929696978055653 1288421892736818183385435)
                    ·
                      rfl

theorem cell23_7527578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_7527578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527578 prefixEnd_7527578 := by exact prefixLift 7527578
  have htrace : WordTrace (prefixWord ++ tailWord_7527578) baseStart_7527578 baseEnd_7527578 := by
    simpa [prefixWord, tailWord_7527578, baseEnd_7527578] using wordTrace_append hprefix tailTrace_7527578
  have hstable : (prefixWord ++ tailWord_7527578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527578).length < 2 ^ (prefixWord ++ tailWord_7527578).sum := by decide
  have hdescent : baseEnd_7527578 < baseStart_7527578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527591 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 8]
def baseStart_7527591 : Nat := 118140960795 + 7527591 * 2 ^ 59
def prefixEnd_7527591 : Nat := 4983230072969 + 3 ^ 40 * 7527591 * 2
def baseEnd_7527591 : Nat := 429474705939884777699305

theorem tailTrace_7527591 : CollatzResearch.WordTrace tailWord_7527591 prefixEnd_7527591 429474705939884777699305 := by
  unfold tailWord_7527591
  simp only [CollatzResearch.WordTrace]
  refine ⟨274553799271830892035254627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183035866181220594690169751 274553799271830892035254627)
  ·
    refine ⟨411830698907746338052881941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274553799271830892035254627 411830698907746338052881941)
    ·
      refine ⟨19304564011300609596228841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 411830698907746338052881941 19304564011300609596228841)
      ·
        refine ⟨14478423008475457197171631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19304564011300609596228841 14478423008475457197171631)
        ·
          refine ⟨21717634512713185795757447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478423008475457197171631 21717634512713185795757447)
          ·
            refine ⟨32576451769069778693636171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717634512713185795757447 32576451769069778693636171)
            ·
              refine ⟨48864677653604668040454257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32576451769069778693636171 48864677653604668040454257)
              ·
                refine ⟨36648508240203501030340693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48864677653604668040454257 36648508240203501030340693)
                ·
                  refine ⟨429474705939884777699305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36648508240203501030340693 429474705939884777699305)
                  ·
                    rfl

theorem cell23_7527591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 8].length) (baseStart_7527591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527591 prefixEnd_7527591 := by exact prefixLift 7527591
  have htrace : WordTrace (prefixWord ++ tailWord_7527591) baseStart_7527591 baseEnd_7527591 := by
    simpa [prefixWord, tailWord_7527591, baseEnd_7527591] using wordTrace_append hprefix tailTrace_7527591
  have hstable : (prefixWord ++ tailWord_7527591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527591).length < 2 ^ (prefixWord ++ tailWord_7527591).sum := by decide
  have hdescent : baseEnd_7527591 < baseStart_7527591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527611 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 5, 2]
def baseStart_7527611 : Nat := 118140960795 + 7527611 * 2 ^ 59
def prefixEnd_7527611 : Nat := 4983230072969 + 3 ^ 40 * 7527611 * 2
def baseEnd_7527611 : Nat := 3865282623072052921043653

theorem tailTrace_7527611 : CollatzResearch.WordTrace tailWord_7527611 prefixEnd_7527611 3865282623072052921043653 := by
  unfold tailWord_7527611
  simp only [CollatzResearch.WordTrace]
  refine ⟨274554528731758435450982687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183036352487838956967321791 274554528731758435450982687)
  ·
    refine ⟨411831793097637653176474031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274554528731758435450982687 411831793097637653176474031)
    ·
      refine ⟨617747689646456479764711047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411831793097637653176474031 617747689646456479764711047)
      ·
        refine ⟨926621534469684719647066571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617747689646456479764711047 926621534469684719647066571)
        ·
          refine ⟨1389932301704527079470599857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926621534469684719647066571 1389932301704527079470599857)
          ·
            refine ⟨1042449226278395309602949893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389932301704527079470599857 1042449226278395309602949893)
            ·
              refine ⟨195459229927199120550553105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1042449226278395309602949893 195459229927199120550553105)
              ·
                refine ⟨146594422445399340412914829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195459229927199120550553105 146594422445399340412914829)
                ·
                  refine ⟨54972908417024752654843061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146594422445399340412914829 54972908417024752654843061)
                  ·
                    refine ⟨5153710164096070561391537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54972908417024752654843061 5153710164096070561391537)
                    ·
                      refine ⟨3865282623072052921043653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153710164096070561391537 3865282623072052921043653)
                      ·
                        rfl

theorem cell23_7527611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5, 2].length) (baseStart_7527611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527611 prefixEnd_7527611 := by exact prefixLift 7527611
  have htrace : WordTrace (prefixWord ++ tailWord_7527611) baseStart_7527611 baseEnd_7527611 := by
    simpa [prefixWord, tailWord_7527611, baseEnd_7527611] using wordTrace_append hprefix tailTrace_7527611
  have hstable : (prefixWord ++ tailWord_7527611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527611).length < 2 ^ (prefixWord ++ tailWord_7527611).sum := by decide
  have hdescent : baseEnd_7527611 < baseStart_7527611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527612 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_7527612 : Nat := 118140960795 + 7527612 * 2 ^ 59
def prefixEnd_7527612 : Nat := 4983230072969 + 3 ^ 40 * 7527612 * 2
def baseEnd_7527612 : Nat := 1288427712184235805710383

theorem tailTrace_7527612 : CollatzResearch.WordTrace tailWord_7527612 prefixEnd_7527612 1288427712184235805710383 := by
  unfold tailWord_7527612
  simp only [CollatzResearch.WordTrace]
  refine ⟨137277282602377406310884545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183036376803169875081179393 137277282602377406310884545)
  ·
    refine ⟨102957961951783054733163409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137277282602377406310884545 102957961951783054733163409)
    ·
      refine ⟨77218471463837291049872557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102957961951783054733163409 77218471463837291049872557)
      ·
        refine ⟨28956926798938984143702209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77218471463837291049872557 28956926798938984143702209)
        ·
          refine ⟨21717695099204238107776657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28956926798938984143702209 21717695099204238107776657)
          ·
            refine ⟨16288271324403178580832493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21717695099204238107776657 16288271324403178580832493)
            ·
              refine ⟨6108101746651191967812185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16288271324403178580832493 6108101746651191967812185)
              ·
                refine ⟨4581076309988393975859139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108101746651191967812185 4581076309988393975859139)
                ·
                  refine ⟨6871614464982590963788709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581076309988393975859139 6871614464982590963788709)
                  ·
                    refine ⟨1288427712184235805710383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871614464982590963788709 1288427712184235805710383)
                    ·
                      rfl

theorem cell23_7527612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_7527612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527612 prefixEnd_7527612 := by exact prefixLift 7527612
  have htrace : WordTrace (prefixWord ++ tailWord_7527612) baseStart_7527612 baseEnd_7527612 := by
    simpa [prefixWord, tailWord_7527612, baseEnd_7527612] using wordTrace_append hprefix tailTrace_7527612
  have hstable : (prefixWord ++ tailWord_7527612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527612).length < 2 ^ (prefixWord ++ tailWord_7527612).sum := by decide
  have hdescent : baseEnd_7527612 < baseStart_7527612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527681 : List Nat := [1, 2, 4, 1, 1, 3, 3, 8]
def baseStart_7527681 : Nat := 118140960795 + 7527681 * 2 ^ 59
def prefixEnd_7527681 : Nat := 4983230072969 + 3 ^ 40 * 7527681 * 2
def baseEnd_7527681 : Nat := 143159946915476579524753

theorem tailTrace_7527681 : CollatzResearch.WordTrace tailWord_7527681 prefixEnd_7527681 143159946915476579524753 := by
  unfold tailWord_7527681
  simp only [CollatzResearch.WordTrace]
  refine ⟨274557081841504837406030897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183038054561003224937353931 274557081841504837406030897)
  ·
    refine ⟨205917811381128628054523173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274557081841504837406030897 205917811381128628054523173)
    ·
      refine ⟨38609589633961617760223095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205917811381128628054523173 38609589633961617760223095)
      ·
        refine ⟨57914384450942426640334643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38609589633961617760223095 57914384450942426640334643)
        ·
          refine ⟨86871576676413639960501965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57914384450942426640334643 86871576676413639960501965)
          ·
            refine ⟨32576841253655114985188237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86871576676413639960501965 32576841253655114985188237)
            ·
              refine ⟨12216315470120668119445589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32576841253655114985188237 12216315470120668119445589)
              ·
                refine ⟨143159946915476579524753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12216315470120668119445589 143159946915476579524753)
                ·
                  rfl

theorem cell23_7527681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 8].length) (baseStart_7527681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527681 prefixEnd_7527681 := by exact prefixLift 7527681
  have htrace : WordTrace (prefixWord ++ tailWord_7527681) baseStart_7527681 baseEnd_7527681 := by
    simpa [prefixWord, tailWord_7527681, baseEnd_7527681] using wordTrace_append hprefix tailTrace_7527681
  have hstable : (prefixWord ++ tailWord_7527681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527681).length < 2 ^ (prefixWord ++ tailWord_7527681).sum := by decide
  have hdescent : baseEnd_7527681 < baseStart_7527681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527708 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_7527708 : Nat := 118140960795 + 7527708 * 2 ^ 59
def prefixEnd_7527708 : Nat := 4983230072969 + 3 ^ 40 * 7527708 * 2
def baseEnd_7527708 : Nat := 3865332430695539041530707

theorem tailTrace_7527708 : CollatzResearch.WordTrace tailWord_7527708 prefixEnd_7527708 3865332430695539041530707 := by
  unfold tailWord_7527708
  simp only [CollatzResearch.WordTrace]
  refine ⟨137279033306203510508631889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183038711074938014011509185 137279033306203510508631889)
  ·
    refine ⟨102959274979652632881473917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137279033306203510508631889 102959274979652632881473917)
    ·
      refine ⟨38609728117369737330552719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102959274979652632881473917 38609728117369737330552719)
      ·
        refine ⟨57914592176054605995829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38609728117369737330552719 57914592176054605995829079)
        ·
          refine ⟨86871888264081908993743619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57914592176054605995829079 86871888264081908993743619)
          ·
            refine ⟨130307832396122863490615429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86871888264081908993743619 130307832396122863490615429)
            ·
              refine ⟨24432718574273036904490393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130307832396122863490615429 24432718574273036904490393)
              ·
                refine ⟨18324538930704777678367795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24432718574273036904490393 18324538930704777678367795)
                ·
                  refine ⟨27486808396057166517551693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18324538930704777678367795 27486808396057166517551693)
                  ·
                    refine ⟨10307553148521437444081885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27486808396057166517551693 10307553148521437444081885)
                    ·
                      refine ⟨3865332430695539041530707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10307553148521437444081885 3865332430695539041530707)
                      ·
                        rfl

theorem cell23_7527708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_7527708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527708 prefixEnd_7527708 := by exact prefixLift 7527708
  have htrace : WordTrace (prefixWord ++ tailWord_7527708) baseStart_7527708 baseEnd_7527708 := by
    simpa [prefixWord, tailWord_7527708, baseEnd_7527708] using wordTrace_append hprefix tailTrace_7527708
  have hstable : (prefixWord ++ tailWord_7527708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527708).length < 2 ^ (prefixWord ++ tailWord_7527708).sum := by decide
  have hdescent : baseEnd_7527708 < baseStart_7527708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527709 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7527709 : Nat := 118140960795 + 7527709 * 2 ^ 59
def prefixEnd_7527709 : Nat := 4983230072969 + 3 ^ 40 * 7527709 * 2
def baseEnd_7527709 : Nat := 3865332944176193537618203

theorem tailTrace_7527709 : CollatzResearch.WordTrace tailWord_7527709 prefixEnd_7527709 3865332944176193537618203 := by
  unfold tailWord_7527709
  simp only [CollatzResearch.WordTrace]
  refine ⟨274558103085403398188050181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183038735390268932125366787 274558103085403398188050181)
  ·
    refine ⟨51479644328513137160259409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274558103085403398188050181 51479644328513137160259409)
    ·
      refine ⟨38609733246384852870194557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51479644328513137160259409 38609733246384852870194557)
      ·
        refine ⟨14478649967394319826322959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38609733246384852870194557 14478649967394319826322959)
        ·
          refine ⟨21717974951091479739484439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478649967394319826322959 21717974951091479739484439)
          ·
            refine ⟨32576962426637219609226659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717974951091479739484439 32576962426637219609226659)
            ·
              refine ⟨48865443639955829413839989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32576962426637219609226659 48865443639955829413839989)
              ·
                refine ⟨4581135341245859007547499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48865443639955829413839989 4581135341245859007547499)
                ·
                  refine ⟨6871703011868788511321249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581135341245859007547499 6871703011868788511321249)
                  ·
                    refine ⟨5153777258901591383490937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6871703011868788511321249 5153777258901591383490937)
                    ·
                      refine ⟨3865332944176193537618203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153777258901591383490937 3865332944176193537618203)
                      ·
                        rfl

theorem cell23_7527709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7527709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527709 prefixEnd_7527709 := by exact prefixLift 7527709
  have htrace : WordTrace (prefixWord ++ tailWord_7527709) baseStart_7527709 baseEnd_7527709 := by
    simpa [prefixWord, tailWord_7527709, baseEnd_7527709] using wordTrace_append hprefix tailTrace_7527709
  have hstable : (prefixWord ++ tailWord_7527709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527709).length < 2 ^ (prefixWord ++ tailWord_7527709).sum := by decide
  have hdescent : baseEnd_7527709 < baseStart_7527709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527781 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7527781 : Nat := 118140960795 + 7527781 * 2 ^ 59
def prefixEnd_7527781 : Nat := 4983230072969 + 3 ^ 40 * 7527781 * 2
def baseEnd_7527781 : Nat := 3865369914783317255917871

theorem tailTrace_7527781 : CollatzResearch.WordTrace tailWord_7527781 prefixEnd_7527781 3865369914783317255917871 := by
  unfold tailWord_7527781
  simp only [CollatzResearch.WordTrace]
  refine ⟨274560729141142554484671197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183040486094095036323114131 274560729141142554484671197)
  ·
    refine ⟨102960273427928457931751699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274560729141142554484671197 102960273427928457931751699)
    ·
      refine ⟨154440410141892686897627549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102960273427928457931751699 154440410141892686897627549)
      ·
        refine ⟨57915153803209757586610331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154440410141892686897627549 57915153803209757586610331)
        ·
          refine ⟨86872730704814636379915497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57915153803209757586610331 86872730704814636379915497)
          ·
            refine ⟨65154548028610977284936623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86872730704814636379915497 65154548028610977284936623)
            ·
              refine ⟨97731822042916465927404935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65154548028610977284936623 97731822042916465927404935)
              ·
                refine ⟨146597733064374698891107403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97731822042916465927404935 146597733064374698891107403)
                ·
                  refine ⟨219896599596562048336661105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146597733064374698891107403 219896599596562048336661105)
                  ·
                    refine ⟨164922449697421536252495829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219896599596562048336661105 164922449697421536252495829)
                    ·
                      refine ⟨3865369914783317255917871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164922449697421536252495829 3865369914783317255917871)
                      ·
                        rfl

theorem cell23_7527781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7527781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527781 prefixEnd_7527781 := by exact prefixLift 7527781
  have htrace : WordTrace (prefixWord ++ tailWord_7527781) baseStart_7527781 baseEnd_7527781 := by
    simpa [prefixWord, tailWord_7527781, baseEnd_7527781] using wordTrace_append hprefix tailTrace_7527781
  have hstable : (prefixWord ++ tailWord_7527781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527781).length < 2 ^ (prefixWord ++ tailWord_7527781).sum := by decide
  have hdescent : baseEnd_7527781 < baseStart_7527781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527788 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 7]
def baseStart_7527788 : Nat := 118140960795 + 7527788 * 2 ^ 59
def prefixEnd_7527788 : Nat := 4983230072969 + 3 ^ 40 * 7527788 * 2
def baseEnd_7527788 : Nat := 429485945460877636503371

theorem tailTrace_7527788 : CollatzResearch.WordTrace tailWord_7527788 prefixEnd_7527788 429485945460877636503371 := by
  unfold tailWord_7527788
  simp only [CollatzResearch.WordTrace]
  refine ⟨137280492226058597340088009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183040656301411463120117345 137280492226058597340088009)
  ·
    refine ⟨102960369169543948005066007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137280492226058597340088009 102960369169543948005066007)
    ·
      refine ⟨154440553754315922007599011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102960369169543948005066007 154440553754315922007599011)
      ·
        refine ⟨231660830631473883011398517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154440553754315922007599011 231660830631473883011398517)
        ·
          refine ⟨21718202871700676532318611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231660830631473883011398517 21718202871700676532318611)
          ·
            refine ⟨32577304307551014798477917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21718202871700676532318611 32577304307551014798477917)
            ·
              refine ⟨12216489115331630549429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32577304307551014798477917 12216489115331630549429219)
              ·
                refine ⟨18324733672997445824143829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12216489115331630549429219 18324733672997445824143829)
                ·
                  refine ⟨429485945460877636503371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18324733672997445824143829 429485945460877636503371)
                  ·
                    rfl

theorem cell23_7527788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_7527788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527788 prefixEnd_7527788 := by exact prefixLift 7527788
  have htrace : WordTrace (prefixWord ++ tailWord_7527788) baseStart_7527788 baseEnd_7527788 := by
    simpa [prefixWord, tailWord_7527788, baseEnd_7527788] using wordTrace_append hprefix tailTrace_7527788
  have hstable : (prefixWord ++ tailWord_7527788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527788).length < 2 ^ (prefixWord ++ tailWord_7527788).sum := by decide
  have hdescent : baseEnd_7527788 < baseStart_7527788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527801 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_7527801 : Nat := 118140960795 + 7527801 * 2 ^ 59
def prefixEnd_7527801 : Nat := 4983230072969 + 3 ^ 40 * 7527801 * 2
def baseEnd_7527801 : Nat := 1288460061465469059222593

theorem tailTrace_7527801 : CollatzResearch.WordTrace tailWord_7527801 prefixEnd_7527801 1288460061465469059222593 := by
  unfold tailWord_7527801
  simp only [CollatzResearch.WordTrace]
  refine ⟨274561458601070097900399257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183040972400713398600266171 274561458601070097900399257)
  ·
    refine ⟨205921093950802573425299443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274561458601070097900399257 205921093950802573425299443)
    ·
      refine ⟨308881640926203860137949165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205921093950802573425299443 308881640926203860137949165)
      ·
        refine ⟨115830615347326447551730937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308881640926203860137949165 115830615347326447551730937)
        ·
          refine ⟨86872961510494835663798203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115830615347326447551730937 86872961510494835663798203)
          ·
            refine ⟨130309442265742253495697305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86872961510494835663798203 130309442265742253495697305)
            ·
              refine ⟨97732081699306690121772979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130309442265742253495697305 97732081699306690121772979)
              ·
                refine ⟨146598122548960035182659469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97732081699306690121772979 146598122548960035182659469)
                ·
                  refine ⟨54974295955860013193497301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146598122548960035182659469 54974295955860013193497301)
                  ·
                    refine ⟨1288460061465469059222593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54974295955860013193497301 1288460061465469059222593)
                    ·
                      rfl

theorem cell23_7527801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_7527801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527801 prefixEnd_7527801 := by exact prefixLift 7527801
  have htrace : WordTrace (prefixWord ++ tailWord_7527801) baseStart_7527801 baseEnd_7527801 := by
    simpa [prefixWord, tailWord_7527801, baseEnd_7527801] using wordTrace_append hprefix tailTrace_7527801
  have hstable : (prefixWord ++ tailWord_7527801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527801).length < 2 ^ (prefixWord ++ tailWord_7527801).sum := by decide
  have hdescent : baseEnd_7527801 < baseStart_7527801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527875 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3]
def baseStart_7527875 : Nat := 118140960795 + 7527875 * 2 ^ 59
def prefixEnd_7527875 : Nat := 4983230072969 + 3 ^ 40 * 7527875 * 2
def baseEnd_7527875 : Nat := 3865418181964839888142439

theorem tailTrace_7527875 : CollatzResearch.WordTrace tailWord_7527875 prefixEnd_7527875 3865418181964839888142439 := by
  unfold tailWord_7527875
  simp only [CollatzResearch.WordTrace]
  refine ⟨274564157602802008538593079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183042771735201339025728719 274564157602802008538593079)
  ·
    refine ⟨411846236404203012807889619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274564157602802008538593079 411846236404203012807889619)
    ·
      refine ⟨617769354606304519211834429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411846236404203012807889619 617769354606304519211834429)
      ·
        refine ⟨231663507977364194704437911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617769354606304519211834429 231663507977364194704437911)
        ·
          refine ⟨347495261966046292056656867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231663507977364194704437911 347495261966046292056656867)
          ·
            refine ⟨521242892949069438084985301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347495261966046292056656867 521242892949069438084985301)
            ·
              refine ⟨12216630303493814955116843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 521242892949069438084985301 12216630303493814955116843)
              ·
                refine ⟨18324945455240722432675265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12216630303493814955116843 18324945455240722432675265)
                ·
                  refine ⟨13743709091430541824506449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18324945455240722432675265 13743709091430541824506449)
                  ·
                    refine ⟨10307781818572906368379837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13743709091430541824506449 10307781818572906368379837)
                    ·
                      refine ⟨3865418181964839888142439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10307781818572906368379837 3865418181964839888142439)
                      ·
                        rfl

theorem cell23_7527875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_7527875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527875 prefixEnd_7527875 := by exact prefixLift 7527875
  have htrace : WordTrace (prefixWord ++ tailWord_7527875) baseStart_7527875 baseEnd_7527875 := by
    simpa [prefixWord, tailWord_7527875, baseEnd_7527875] using wordTrace_append hprefix tailTrace_7527875
  have hstable : (prefixWord ++ tailWord_7527875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527875).length < 2 ^ (prefixWord ++ tailWord_7527875).sum := by decide
  have hdescent : baseEnd_7527875 < baseStart_7527875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527882 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_7527882 : Nat := 118140960795 + 7527882 * 2 ^ 59
def prefixEnd_7527882 : Nat := 4983230072969 + 3 ^ 40 * 7527882 * 2
def baseEnd_7527882 : Nat := 1288473925443140453584969

theorem tailTrace_7527882 : CollatzResearch.WordTrace tailWord_7527882 prefixEnd_7527882 1288473925443140453584969 := by
  unfold tailWord_7527882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68641103228444162183524475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183042941942517765822731933 68641103228444162183524475)
  ·
    refine ⟨102961654842666243275286713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68641103228444162183524475 102961654842666243275286713)
    ·
      refine ⟨77221241131999682456465035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102961654842666243275286713 77221241131999682456465035)
      ·
        refine ⟨115831861697999523684697553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77221241131999682456465035 115831861697999523684697553)
        ·
          refine ⟨86873896273499642763523165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115831861697999523684697553 86873896273499642763523165)
          ·
            refine ⟨32577711102562366036321187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86873896273499642763523165 32577711102562366036321187)
            ·
              refine ⟨48866566653843549054481781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32577711102562366036321187 48866566653843549054481781)
              ·
                refine ⟨4581240623797832723857667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48866566653843549054481781 4581240623797832723857667)
                ·
                  refine ⟨6871860935696749085786501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581240623797832723857667 6871860935696749085786501)
                  ·
                    refine ⟨1288473925443140453584969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871860935696749085786501 1288473925443140453584969)
                    ·
                      rfl

theorem cell23_7527882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_7527882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527882 prefixEnd_7527882 := by exact prefixLift 7527882
  have htrace : WordTrace (prefixWord ++ tailWord_7527882) baseStart_7527882 baseEnd_7527882 := by
    simpa [prefixWord, tailWord_7527882, baseEnd_7527882] using wordTrace_append hprefix tailTrace_7527882
  have hstable : (prefixWord ++ tailWord_7527882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527882).length < 2 ^ (prefixWord ++ tailWord_7527882).sum := by decide
  have hdescent : baseEnd_7527882 < baseStart_7527882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527898 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_7527898 : Nat := 118140960795 + 7527898 * 2 ^ 59
def prefixEnd_7527898 : Nat := 4983230072969 + 3 ^ 40 * 7527898 * 2
def baseEnd_7527898 : Nat := 3865429992019893298154833

theorem tailTrace_7527898 : CollatzResearch.WordTrace tailWord_7527898 prefixEnd_7527898 3865429992019893298154833 := by
  unfold tailWord_7527898
  simp only [CollatzResearch.WordTrace]
  refine ⟨68641249120429670866670087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183043330987812455644453565 68641249120429670866670087)
  ·
    refine ⟨102961873680644506300005131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68641249120429670866670087 102961873680644506300005131)
    ·
      refine ⟨154442810520966759450007697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102961873680644506300005131 154442810520966759450007697)
      ·
        refine ⟨115832107890725069587505773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154442810520966759450007697 115832107890725069587505773)
        ·
          refine ⟨43437040459021901095314665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115832107890725069587505773 43437040459021901095314665)
          ·
            refine ⟨32577780344266425821485999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43437040459021901095314665 32577780344266425821485999)
            ·
              refine ⟨48866670516399638732228999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32577780344266425821485999 48866670516399638732228999)
              ·
                refine ⟨73300005774599458098343499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48866670516399638732228999 73300005774599458098343499)
                ·
                  refine ⟨109950008661899187147515249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73300005774599458098343499 109950008661899187147515249)
                  ·
                    refine ⟨82462506496424390360636437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109950008661899187147515249 82462506496424390360636437)
                    ·
                      refine ⟨3865429992019893298154833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82462506496424390360636437 3865429992019893298154833)
                      ·
                        rfl

theorem cell23_7527898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_7527898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527898 prefixEnd_7527898 := by exact prefixLift 7527898
  have htrace : WordTrace (prefixWord ++ tailWord_7527898) baseStart_7527898 baseEnd_7527898 := by
    simpa [prefixWord, tailWord_7527898, baseEnd_7527898] using wordTrace_append hprefix tailTrace_7527898
  have hstable : (prefixWord ++ tailWord_7527898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527898).length < 2 ^ (prefixWord ++ tailWord_7527898).sum := by decide
  have hdescent : baseEnd_7527898 < baseStart_7527898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527908 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_7527908 : Nat := 118140960795 + 7527908 * 2 ^ 59
def prefixEnd_7527908 : Nat := 4983230072969 + 3 ^ 40 * 7527908 * 2
def baseEnd_7527908 : Nat := 1288478375608812753009929

theorem tailTrace_7527908 : CollatzResearch.WordTrace tailWord_7527908 prefixEnd_7527908 1288478375608812753009929 := by
  unfold tailWord_7527908
  simp only [CollatzResearch.WordTrace]
  refine ⟨137282680605841227587272189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183043574141121636783029585 137282680605841227587272189)
  ·
    refine ⟨51481005227190460345227071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137282680605841227587272189 51481005227190460345227071)
    ·
      refine ⟨77221507840785690517840607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51481005227190460345227071 77221507840785690517840607)
      ·
        refine ⟨115832261761178535776760911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77221507840785690517840607 115832261761178535776760911)
        ·
          refine ⟨173748392641767803665141367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115832261761178535776760911 173748392641767803665141367)
          ·
            refine ⟨260622588962651705497712051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173748392641767803665141367 260622588962651705497712051)
            ·
              refine ⟨390933883443977558246568077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260622588962651705497712051 390933883443977558246568077)
              ·
                refine ⟨146600206291491584342463029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390933883443977558246568077 146600206291491584342463029)
                ·
                  refine ⟨13743769339827336032105909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146600206291491584342463029 13743769339827336032105909)
                  ·
                    refine ⟨1288478375608812753009929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13743769339827336032105909 1288478375608812753009929)
                    ·
                      rfl

theorem cell23_7527908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_7527908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527908 prefixEnd_7527908 := by exact prefixLift 7527908
  have htrace : WordTrace (prefixWord ++ tailWord_7527908) baseStart_7527908 baseEnd_7527908 := by
    simpa [prefixWord, tailWord_7527908, baseEnd_7527908] using wordTrace_append hprefix tailTrace_7527908
  have hstable : (prefixWord ++ tailWord_7527908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527908).length < 2 ^ (prefixWord ++ tailWord_7527908).sum := by decide
  have hdescent : baseEnd_7527908 < baseStart_7527908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527915 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 6, 3, 2]
def baseStart_7527915 : Nat := 118140960795 + 7527915 * 2 ^ 59
def prefixEnd_7527915 : Nat := 4983230072969 + 3 ^ 40 * 7527915 * 2
def baseEnd_7527915 : Nat := 3865438721191019731642255

theorem tailTrace_7527915 : CollatzResearch.WordTrace tailWord_7527915 prefixEnd_7527915 3865438721191019731642255 := by
  unfold tailWord_7527915
  simp only [CollatzResearch.WordTrace]
  refine ⟨274565616522657095370049199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183043744348438063580032799 274565616522657095370049199)
  ·
    refine ⟨411848424783985643055073799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274565616522657095370049199 411848424783985643055073799)
    ·
      refine ⟨617772637175978464582610699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411848424783985643055073799 617772637175978464582610699)
      ·
        refine ⟨926658955763967696873916049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617772637175978464582610699 926658955763967696873916049)
        ·
          refine ⟨694994216822975772655437037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926658955763967696873916049 694994216822975772655437037)
          ·
            refine ⟨260622831308615914745788889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694994216822975772655437037 260622831308615914745788889)
            ·
              refine ⟨195467123481461936059341667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260622831308615914745788889 195467123481461936059341667)
              ·
                refine ⟨293200685222192904089012501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195467123481461936059341667 293200685222192904089012501)
                ·
                  refine ⟨13743782119790292379172461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293200685222192904089012501 13743782119790292379172461)
                  ·
                    refine ⟨5153918294921359642189673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13743782119790292379172461 5153918294921359642189673)
                    ·
                      refine ⟨3865438721191019731642255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5153918294921359642189673 3865438721191019731642255)
                      ·
                        rfl

theorem cell23_7527915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3, 2].length) (baseStart_7527915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527915 prefixEnd_7527915 := by exact prefixLift 7527915
  have htrace : WordTrace (prefixWord ++ tailWord_7527915) baseStart_7527915 baseEnd_7527915 := by
    simpa [prefixWord, tailWord_7527915, baseEnd_7527915] using wordTrace_append hprefix tailTrace_7527915
  have hstable : (prefixWord ++ tailWord_7527915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527915).length < 2 ^ (prefixWord ++ tailWord_7527915).sum := by decide
  have hdescent : baseEnd_7527915 < baseStart_7527915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527945 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_7527945 : Nat := 118140960795 + 7527945 * 2 ^ 59
def prefixEnd_7527945 : Nat := 4983230072969 + 3 ^ 40 * 7527945 * 2
def baseEnd_7527945 : Nat := 3865454125610654614267117

theorem tailTrace_7527945 : CollatzResearch.WordTrace tailWord_7527945 prefixEnd_7527945 3865454125610654614267117 := by
  unfold tailWord_7527945
  simp only [CollatzResearch.WordTrace]
  refine ⟨274566710712548410493641289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183044473808365606995760859 274566710712548410493641289)
  ·
    refine ⟨205925033034411307870230967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274566710712548410493641289 205925033034411307870230967)
    ·
      refine ⟨308887549551616961805346451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205925033034411307870230967 308887549551616961805346451)
      ·
        refine ⟨463331324327425442708019677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308887549551616961805346451 463331324327425442708019677)
        ·
          refine ⟨173749246622784541015507379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463331324327425442708019677 173749246622784541015507379)
          ·
            refine ⟨260623869934176811523261069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173749246622784541015507379 260623869934176811523261069)
            ·
              refine ⟨97733951225316304321222901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260623869934176811523261069 97733951225316304321222901)
              ·
                refine ⟨9162557927373403530114647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97733951225316304321222901 9162557927373403530114647)
                ·
                  refine ⟨13743836891060105295171971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9162557927373403530114647 13743836891060105295171971)
                  ·
                    refine ⟨20615755336590157942757957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13743836891060105295171971 20615755336590157942757957)
                    ·
                      refine ⟨3865454125610654614267117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20615755336590157942757957 3865454125610654614267117)
                      ·
                        rfl

theorem cell23_7527945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_7527945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527945 prefixEnd_7527945 := by exact prefixLift 7527945
  have htrace : WordTrace (prefixWord ++ tailWord_7527945) baseStart_7527945 baseEnd_7527945 := by
    simpa [prefixWord, tailWord_7527945, baseEnd_7527945] using wordTrace_append hprefix tailTrace_7527945
  have hstable : (prefixWord ++ tailWord_7527945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527945).length < 2 ^ (prefixWord ++ tailWord_7527945).sum := by decide
  have hdescent : baseEnd_7527945 < baseStart_7527945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527955 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 4, 4]
def baseStart_7527955 : Nat := 118140960795 + 7527955 * 2 ^ 59
def prefixEnd_7527955 : Nat := 4983230072969 + 3 ^ 40 * 7527955 * 2
def baseEnd_7527955 : Nat := 1288486420139066525047357

theorem tailTrace_7527955 : CollatzResearch.WordTrace tailWord_7527955 prefixEnd_7527955 1288486420139066525047357 := by
  unfold tailWord_7527955
  simp only [CollatzResearch.WordTrace]
  refine ⟨274567075442512182201505319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183044716961674788134336879 274567075442512182201505319)
  ·
    refine ⟨411850613163768273302257979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274567075442512182201505319 411850613163768273302257979)
    ·
      refine ⟨617775919745652409953386969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411850613163768273302257979 617775919745652409953386969)
      ·
        refine ⟨463331939809239307465040227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617775919745652409953386969 463331939809239307465040227)
        ·
          refine ⟨694997909713858961197560341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463331939809239307465040227 694997909713858961197560341)
          ·
            refine ⟨32578027017837138806135641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 694997909713858961197560341 32578027017837138806135641)
            ·
              refine ⟨24433520263377854104601731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32578027017837138806135641 24433520263377854104601731)
              ·
                refine ⟨36650280395066781156902597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24433520263377854104601731 36650280395066781156902597)
                ·
                  refine ⟨6871927574075021466919237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36650280395066781156902597 6871927574075021466919237)
                  ·
                    refine ⟨1288486420139066525047357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871927574075021466919237 1288486420139066525047357)
                    ·
                      rfl

theorem cell23_7527955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 4].length) (baseStart_7527955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527955 prefixEnd_7527955 := by exact prefixLift 7527955
  have htrace : WordTrace (prefixWord ++ tailWord_7527955) baseStart_7527955 baseEnd_7527955 := by
    simpa [prefixWord, tailWord_7527955, baseEnd_7527955] using wordTrace_append hprefix tailTrace_7527955
  have hstable : (prefixWord ++ tailWord_7527955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527955).length < 2 ^ (prefixWord ++ tailWord_7527955).sum := by decide
  have hdescent : baseEnd_7527955 < baseStart_7527955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527965 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_7527965 : Nat := 118140960795 + 7527965 * 2 ^ 59
def prefixEnd_7527965 : Nat := 4983230072969 + 3 ^ 40 * 7527965 * 2
def baseEnd_7527965 : Nat := 3865464395223744536017025

theorem tailTrace_7527965 : CollatzResearch.WordTrace tailWord_7527965 prefixEnd_7527965 3865464395223744536017025 := by
  unfold tailWord_7527965
  simp only [CollatzResearch.WordTrace]
  refine ⟨274567440172475953909369349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183044960114983969272912899 274567440172475953909369349)
  ·
    refine ⟨51481395032339241358006753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274567440172475953909369349 51481395032339241358006753)
    ·
      refine ⟨38611046274254431018505065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51481395032339241358006753 38611046274254431018505065)
      ·
        refine ⟨28958284705690823263878799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38611046274254431018505065 28958284705690823263878799)
        ·
          refine ⟨43437427058536234895818199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28958284705690823263878799 43437427058536234895818199)
          ·
            refine ⟨65156140587804352343727299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43437427058536234895818199 65156140587804352343727299)
            ·
              refine ⟨97734210881706528515590949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65156140587804352343727299 97734210881706528515590949)
              ·
                refine ⟨18325164540319974096673303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97734210881706528515590949 18325164540319974096673303)
                ·
                  refine ⟨27487746810479961145009955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18325164540319974096673303 27487746810479961145009955)
                  ·
                    refine ⟨41231620215719941717514933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27487746810479961145009955 41231620215719941717514933)
                    ·
                      refine ⟨3865464395223744536017025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41231620215719941717514933 3865464395223744536017025)
                      ·
                        rfl

theorem cell23_7527965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_7527965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527965 prefixEnd_7527965 := by exact prefixLift 7527965
  have htrace : WordTrace (prefixWord ++ tailWord_7527965) baseStart_7527965 baseEnd_7527965 := by
    simpa [prefixWord, tailWord_7527965, baseEnd_7527965] using wordTrace_append hprefix tailTrace_7527965
  have hstable : (prefixWord ++ tailWord_7527965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527965).length < 2 ^ (prefixWord ++ tailWord_7527965).sum := by decide
  have hdescent : baseEnd_7527965 < baseStart_7527965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527976 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 1, 5]
def baseStart_7527976 : Nat := 118140960795 + 7527976 * 2 ^ 59
def prefixEnd_7527976 : Nat := 4983230072969 + 3 ^ 40 * 7527976 * 2
def baseEnd_7527976 : Nat := 1288490014503647997659825

theorem tailTrace_7527976 : CollatzResearch.WordTrace tailWord_7527976 prefixEnd_7527976 1288490014503647997659825 := by
  unfold tailWord_7527976
  simp only [CollatzResearch.WordTrace]
  refine ⟨137283920687718051394009891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183045227583624068525346521 137283920687718051394009891)
  ·
    refine ⟨205925881031577077091014837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137283920687718051394009891 205925881031577077091014837)
    ·
      refine ⟨19305551346710350977282641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205925881031577077091014837 19305551346710350977282641)
      ·
        refine ⟨14479163510032763232961981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19305551346710350977282641 14479163510032763232961981)
        ·
          refine ⟨5429686316262286212360743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14479163510032763232961981 5429686316262286212360743)
          ·
            refine ⟨8144529474393429318541115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429686316262286212360743 8144529474393429318541115)
            ·
              refine ⟨12216794211590143977811673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144529474393429318541115 12216794211590143977811673)
              ·
                refine ⟨9162595658692607983358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12216794211590143977811673 9162595658692607983358755)
                ·
                  refine ⟨13743893488038911975038133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9162595658692607983358755 13743893488038911975038133)
                  ·
                    refine ⟨1288490014503647997659825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13743893488038911975038133 1288490014503647997659825)
                    ·
                      rfl

theorem cell23_7527976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_7527976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527976 prefixEnd_7527976 := by exact prefixLift 7527976
  have htrace : WordTrace (prefixWord ++ tailWord_7527976) baseStart_7527976 baseEnd_7527976 := by
    simpa [prefixWord, tailWord_7527976, baseEnd_7527976] using wordTrace_append hprefix tailTrace_7527976
  have hstable : (prefixWord ++ tailWord_7527976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527976).length < 2 ^ (prefixWord ++ tailWord_7527976).sum := by decide
  have hdescent : baseEnd_7527976 < baseStart_7527976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7527999 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 1, 2, 3]
def baseStart_7527999 : Nat := 118140960795 + 7527999 * 2 ^ 59
def prefixEnd_7527999 : Nat := 4983230072969 + 3 ^ 40 * 7527999 * 2
def baseEnd_7527999 : Nat := 3865481853565997402991869

theorem tailTrace_7527999 : CollatzResearch.WordTrace tailWord_7527999 prefixEnd_7527999 3865481853565997402991869 := by
  unfold tailWord_7527999
  simp only [CollatzResearch.WordTrace]
  refine ⟨274568680254352777716107051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183045786836235185144071367 274568680254352777716107051)
  ·
    refine ⟨411853020381529166574160577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274568680254352777716107051 411853020381529166574160577)
    ·
      refine ⟨308889765286146874930620433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411853020381529166574160577 308889765286146874930620433)
      ·
        refine ⟨231667323964610156197965325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308889765286146874930620433 231667323964610156197965325)
        ·
          refine ⟨86875246486728808574236997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231667323964610156197965325 86875246486728808574236997)
          ·
            refine ⟨16289108716261651607669437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86875246486728808574236997 16289108716261651607669437)
            ·
              refine ⟨6108415768598119352876039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16289108716261651607669437 6108415768598119352876039)
              ·
                refine ⟨9162623652897179029314059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108415768598119352876039 9162623652897179029314059)
                ·
                  refine ⟨13743935479345768543971089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9162623652897179029314059 13743935479345768543971089)
                  ·
                    refine ⟨10307951609509326407978317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13743935479345768543971089 10307951609509326407978317)
                    ·
                      refine ⟨3865481853565997402991869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10307951609509326407978317 3865481853565997402991869)
                      ·
                        rfl

theorem cell23_7527999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_7527999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7527999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7527999 prefixEnd_7527999 := by exact prefixLift 7527999
  have htrace : WordTrace (prefixWord ++ tailWord_7527999) baseStart_7527999 baseEnd_7527999 := by
    simpa [prefixWord, tailWord_7527999, baseEnd_7527999] using wordTrace_append hprefix tailTrace_7527999
  have hstable : (prefixWord ++ tailWord_7527999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7527999).length < 2 ^ (prefixWord ++ tailWord_7527999).sum := by decide
  have hdescent : baseEnd_7527999 < baseStart_7527999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7527999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528008 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_7528008 : Nat := 118140960795 + 7528008 * 2 ^ 59
def prefixEnd_7528008 : Nat := 4983230072969 + 3 ^ 40 * 7528008 * 2
def baseEnd_7528008 : Nat := 3865486474891887867779327

theorem tailTrace_7528008 : CollatzResearch.WordTrace tailWord_7528008 prefixEnd_7528008 3865486474891887867779327 := by
  unfold tailWord_7528008
  simp only [CollatzResearch.WordTrace]
  refine ⟨137284504255660086126592339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183046005674213448168789785 137284504255660086126592339)
  ·
    refine ⟨205926756383490129189888509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137284504255660086126592339 205926756383490129189888509)
    ·
      refine ⟨77222533643808798446208191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205926756383490129189888509 77222533643808798446208191)
      ·
        refine ⟨115833800465713197669312287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77222533643808798446208191 115833800465713197669312287)
        ·
          refine ⟨173750700698569796503968431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115833800465713197669312287 173750700698569796503968431)
          ·
            refine ⟨260626051047854694755952647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173750700698569796503968431 260626051047854694755952647)
            ·
              refine ⟨390939076571782042133928971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260626051047854694755952647 390939076571782042133928971)
              ·
                refine ⟨586408614857673063200893457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390939076571782042133928971 586408614857673063200893457)
                ·
                  refine ⟨439806461143254797400670093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586408614857673063200893457 439806461143254797400670093)
                  ·
                    refine ⟨164927422928720549025251285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439806461143254797400670093 164927422928720549025251285)
                    ·
                      refine ⟨3865486474891887867779327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164927422928720549025251285 3865486474891887867779327)
                      ·
                        rfl

theorem cell23_7528008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_7528008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528008 prefixEnd_7528008 := by exact prefixLift 7528008
  have htrace : WordTrace (prefixWord ++ tailWord_7528008) baseStart_7528008 baseEnd_7528008 := by
    simpa [prefixWord, tailWord_7528008, baseEnd_7528008] using wordTrace_append hprefix tailTrace_7528008
  have hstable : (prefixWord ++ tailWord_7528008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528008).length < 2 ^ (prefixWord ++ tailWord_7528008).sum := by decide
  have hdescent : baseEnd_7528008 < baseStart_7528008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528069 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_7528069 : Nat := 118140960795 + 7528069 * 2 ^ 59
def prefixEnd_7528069 : Nat := 4983230072969 + 3 ^ 40 * 7528069 * 2
def baseEnd_7528069 : Nat := 3865517797211812129116547

theorem tailTrace_7528069 : CollatzResearch.WordTrace tailWord_7528069 prefixEnd_7528069 3865517797211812129116547 := by
  unfold tailWord_7528069
  simp only [CollatzResearch.WordTrace]
  refine ⟨274571233364099179671155261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183047488909399453114103507 274571233364099179671155261)
  ·
    refine ⟨102964212511537192376683223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274571233364099179671155261 102964212511537192376683223)
    ·
      refine ⟨154446318767305788565024835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102964212511537192376683223 154446318767305788565024835)
      ·
        refine ⟨231669478150958682847537253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154446318767305788565024835 231669478150958682847537253)
        ·
          refine ⟨43438027153304753033913235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231669478150958682847537253 43438027153304753033913235)
          ·
            refine ⟨65157040729957129550869853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43438027153304753033913235 65157040729957129550869853)
            ·
              refine ⟨24433890273733923581576195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65157040729957129550869853 24433890273733923581576195)
              ·
                refine ⟨36650835410600885372364293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24433890273733923581576195 36650835410600885372364293)
                ·
                  refine ⟨6872031639487666007318305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36650835410600885372364293 6872031639487666007318305)
                  ·
                    refine ⟨5154023729615749505488729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872031639487666007318305 5154023729615749505488729)
                    ·
                      refine ⟨3865517797211812129116547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154023729615749505488729 3865517797211812129116547)
                      ·
                        rfl

theorem cell23_7528069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_7528069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528069 prefixEnd_7528069 := by exact prefixLift 7528069
  have htrace : WordTrace (prefixWord ++ tailWord_7528069) baseStart_7528069 baseEnd_7528069 := by
    simpa [prefixWord, tailWord_7528069, baseEnd_7528069] using wordTrace_append hprefix tailTrace_7528069
  have hstable : (prefixWord ++ tailWord_7528069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528069).length < 2 ^ (prefixWord ++ tailWord_7528069).sum := by decide
  have hdescent : baseEnd_7528069 < baseStart_7528069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528075 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 7]
def baseStart_7528075 : Nat := 118140960795 + 7528075 * 2 ^ 59
def prefixEnd_7528075 : Nat := 4983230072969 + 3 ^ 40 * 7528075 * 2
def baseEnd_7528075 : Nat := 429502319788415456182391

theorem tailTrace_7528075 : CollatzResearch.WordTrace tailWord_7528075 prefixEnd_7528075 429502319788415456182391 := by
  unfold tailWord_7528075
  simp only [CollatzResearch.WordTrace]
  refine ⟨274571452202077442695873679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183047634801384961797249119 274571452202077442695873679)
  ·
    refine ⟨411857178303116164043810519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274571452202077442695873679 411857178303116164043810519)
    ·
      refine ⟨617785767454674246065715779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411857178303116164043810519 617785767454674246065715779)
      ·
        refine ⟨926678651182011369098573669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617785767454674246065715779 926678651182011369098573669)
        ·
          refine ⟨173752247096627131705982563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 926678651182011369098573669 173752247096627131705982563)
          ·
            refine ⟨260628370644940697558973845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173752247096627131705982563 260628370644940697558973845)
            ·
              refine ⟨12216954873981595198076899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260628370644940697558973845 12216954873981595198076899)
              ·
                refine ⟨18325432310972392797115349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12216954873981595198076899 18325432310972392797115349)
                ·
                  refine ⟨429502319788415456182391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18325432310972392797115349 429502319788415456182391)
                  ·
                    rfl

theorem cell23_7528075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 7].length) (baseStart_7528075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528075 prefixEnd_7528075 := by exact prefixLift 7528075
  have htrace : WordTrace (prefixWord ++ tailWord_7528075) baseStart_7528075 baseEnd_7528075 := by
    simpa [prefixWord, tailWord_7528075, baseEnd_7528075] using wordTrace_append hprefix tailTrace_7528075
  have hstable : (prefixWord ++ tailWord_7528075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528075).length < 2 ^ (prefixWord ++ tailWord_7528075).sum := by decide
  have hdescent : baseEnd_7528075 < baseStart_7528075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528115 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_7528115 : Nat := 118140960795 + 7528115 * 2 ^ 59
def prefixEnd_7528115 : Nat := 4983230072969 + 3 ^ 40 * 7528115 * 2
def baseEnd_7528115 : Nat := 3865541417321918949141335

theorem tailTrace_7528115 : CollatzResearch.WordTrace tailWord_7528115 prefixEnd_7528115 3865541417321918949141335 := by
  unfold tailWord_7528115
  simp only [CollatzResearch.WordTrace]
  refine ⟨274572911121932529527329799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183048607414621686351553199 274572911121932529527329799)
  ·
    refine ⟨411859366682898794290994699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274572911121932529527329799 411859366682898794290994699)
    ·
      refine ⟨617789050024348191436492049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411859366682898794290994699 617789050024348191436492049)
      ·
        refine ⟨463341787518261143577369037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617789050024348191436492049 463341787518261143577369037)
        ·
          refine ⟨173753170319347928841513389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463341787518261143577369037 173753170319347928841513389)
          ·
            refine ⟨65157438869755473315567521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173753170319347928841513389 65157438869755473315567521)
            ·
              refine ⟨48868079152316604986675641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65157438869755473315567521 48868079152316604986675641)
              ·
                refine ⟨36651059364237453740006731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48868079152316604986675641 36651059364237453740006731)
                ·
                  refine ⟨54976589046356180610010097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36651059364237453740006731 54976589046356180610010097)
                  ·
                    refine ⟨41232441784767135457507573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54976589046356180610010097 41232441784767135457507573)
                    ·
                      refine ⟨3865541417321918949141335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41232441784767135457507573 3865541417321918949141335)
                      ·
                        rfl

theorem cell23_7528115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_7528115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528115 prefixEnd_7528115 := by exact prefixLift 7528115
  have htrace : WordTrace (prefixWord ++ tailWord_7528115) baseStart_7528115 baseEnd_7528115 := by
    simpa [prefixWord, tailWord_7528115, baseEnd_7528115] using wordTrace_append hprefix tailTrace_7528115
  have hstable : (prefixWord ++ tailWord_7528115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528115).length < 2 ^ (prefixWord ++ tailWord_7528115).sum := by decide
  have hdescent : baseEnd_7528115 < baseStart_7528115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528122 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_7528122 : Nat := 118140960795 + 7528122 * 2 ^ 59
def prefixEnd_7528122 : Nat := 4983230072969 + 3 ^ 40 * 7528122 * 2
def baseEnd_7528122 : Nat := 1288515003895500140584601

theorem tailTrace_7528122 : CollatzResearch.WordTrace tailWord_7528122 prefixEnd_7528122 1288515003895500140584601 := by
  unfold tailWord_7528122
  simp only [CollatzResearch.WordTrace]
  refine ⟨68643291608226792430708655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183048777621938113148556413 68643291608226792430708655)
  ·
    refine ⟨102964937412340188646062983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68643291608226792430708655 102964937412340188646062983)
    ·
      refine ⟨154447406118510282969094475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102964937412340188646062983 154447406118510282969094475)
      ·
        refine ⟨231671109177765424453641713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154447406118510282969094475 231671109177765424453641713)
        ·
          refine ⟨173753331883324068340231285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231671109177765424453641713 173753331883324068340231285)
          ·
            refine ⟨16289374864061631406896683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173753331883324068340231285 16289374864061631406896683)
            ·
              refine ⟨24434062296092447110345025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16289374864061631406896683 24434062296092447110345025)
              ·
                refine ⟨18325546722069335332758769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24434062296092447110345025 18325546722069335332758769)
                ·
                  refine ⟨13744160041552001499569077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18325546722069335332758769 13744160041552001499569077)
                  ·
                    refine ⟨1288515003895500140584601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13744160041552001499569077 1288515003895500140584601)
                    ·
                      rfl

theorem cell23_7528122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_7528122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528122 prefixEnd_7528122 := by exact prefixLift 7528122
  have htrace : WordTrace (prefixWord ++ tailWord_7528122) baseStart_7528122 baseEnd_7528122 := by
    simpa [prefixWord, tailWord_7528122, baseEnd_7528122] using wordTrace_append hprefix tailTrace_7528122
  have hstable : (prefixWord ++ tailWord_7528122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528122).length < 2 ^ (prefixWord ++ tailWord_7528122).sum := by decide
  have hdescent : baseEnd_7528122 < baseStart_7528122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528126 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_7528126 : Nat := 118140960795 + 7528126 * 2 ^ 59
def prefixEnd_7528126 : Nat := 4983230072969 + 3 ^ 40 * 7528126 * 2
def baseEnd_7528126 : Nat := 429505229512124267344865

theorem tailTrace_7528126 : CollatzResearch.WordTrace tailWord_7528126 prefixEnd_7528126 429505229512124267344865 := by
  unfold tailWord_7528126
  simp only [CollatzResearch.WordTrace]
  refine ⟨34321664040611584800747529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183048874883261785603986821 34321664040611584800747529)
  ·
    refine ⟨25741248030458688600560647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34321664040611584800747529 25741248030458688600560647)
    ·
      refine ⟨38611872045688032900840971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25741248030458688600560647 38611872045688032900840971)
      ·
        refine ⟨57917808068532049351261457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38611872045688032900840971 57917808068532049351261457)
        ·
          refine ⟨43438356051399037013446093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57917808068532049351261457 43438356051399037013446093)
          ·
            refine ⟨16289383519274638880042285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43438356051399037013446093 16289383519274638880042285)
            ·
              refine ⟨6108518819727989580015857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16289383519274638880042285 6108518819727989580015857)
              ·
                refine ⟨4581389114795992185011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108518819727989580015857 4581389114795992185011893)
                ·
                  refine ⟨429505229512124267344865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581389114795992185011893 429505229512124267344865)
                  ·
                    rfl

theorem cell23_7528126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_7528126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528126 prefixEnd_7528126 := by exact prefixLift 7528126
  have htrace : WordTrace (prefixWord ++ tailWord_7528126) baseStart_7528126 baseEnd_7528126 := by
    simpa [prefixWord, tailWord_7528126, baseEnd_7528126] using wordTrace_append hprefix tailTrace_7528126
  have hstable : (prefixWord ++ tailWord_7528126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528126).length < 2 ^ (prefixWord ++ tailWord_7528126).sum := by decide
  have hdescent : baseEnd_7528126 < baseStart_7528126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528132 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7528132 : Nat := 118140960795 + 7528132 * 2 ^ 59
def prefixEnd_7528132 : Nat := 4983230072969 + 3 ^ 40 * 7528132 * 2
def baseEnd_7528132 : Nat := 3865550146493045382628757

theorem tailTrace_7528132 : CollatzResearch.WordTrace tailWord_7528132 prefixEnd_7528132 3865550146493045382628757 := by
  unfold tailWord_7528132
  simp only [CollatzResearch.WordTrace]
  refine ⟨137286765581435470715349325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183049020775247294287132433 137286765581435470715349325)
  ·
    refine ⟨51482537093038301518255997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137286765581435470715349325 51482537093038301518255997)
    ·
      refine ⟨19305951409889363069345999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51482537093038301518255997 19305951409889363069345999)
      ·
        refine ⟨28958927114834044604018999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19305951409889363069345999 28958927114834044604018999)
        ·
          refine ⟨43438390672251066906028499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28958927114834044604018999 43438390672251066906028499)
          ·
            refine ⟨65157586008376600359042749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43438390672251066906028499 65157586008376600359042749)
            ·
              refine ⟨24434094753141225134641031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65157586008376600359042749 24434094753141225134641031)
              ·
                refine ⟨36651142129711837701961547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24434094753141225134641031 36651142129711837701961547)
                ·
                  refine ⟨54976713194567756552942321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36651142129711837701961547 54976713194567756552942321)
                  ·
                    refine ⟨41232534895925817414706741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54976713194567756552942321 41232534895925817414706741)
                    ·
                      refine ⟨3865550146493045382628757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41232534895925817414706741 3865550146493045382628757)
                      ·
                        rfl

theorem cell23_7528132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7528132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528132 prefixEnd_7528132 := by exact prefixLift 7528132
  have htrace : WordTrace (prefixWord ++ tailWord_7528132) baseStart_7528132 baseEnd_7528132 := by
    simpa [prefixWord, tailWord_7528132, baseEnd_7528132] using wordTrace_append hprefix tailTrace_7528132
  have hstable : (prefixWord ++ tailWord_7528132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528132).length < 2 ^ (prefixWord ++ tailWord_7528132).sum := by decide
  have hdescent : baseEnd_7528132 < baseStart_7528132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528142 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7528142 : Nat := 118140960795 + 7528142 * 2 ^ 59
def prefixEnd_7528142 : Nat := 4983230072969 + 3 ^ 40 * 7528142 * 2
def baseEnd_7528142 : Nat := 3865555281299590343503711

theorem tailTrace_7528142 : CollatzResearch.WordTrace tailWord_7528142 prefixEnd_7528142 3865555281299590343503711 := by
  unfold tailWord_7528142
  simp only [CollatzResearch.WordTrace]
  refine ⟨34321736986604339142320335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183049263928556475425708453 34321736986604339142320335)
  ·
    refine ⟨51482605479906508713480503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34321736986604339142320335 51482605479906508713480503)
    ·
      refine ⟨77223908219859763070220755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51482605479906508713480503 77223908219859763070220755)
      ·
        refine ⟨115835862329789644605331133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77223908219859763070220755 115835862329789644605331133)
        ·
          refine ⟨43438448373671116726999175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115835862329789644605331133 43438448373671116726999175)
          ·
            refine ⟨65157672560506675090498763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43438448373671116726999175 65157672560506675090498763)
            ·
              refine ⟨97736508840760012635748145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65157672560506675090498763 97736508840760012635748145)
              ·
                refine ⟨73302381630570009476811109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97736508840760012635748145 73302381630570009476811109)
                ·
                  refine ⟨13744196555731876776902083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73302381630570009476811109 13744196555731876776902083)
                  ·
                    refine ⟨20616294833597815165353125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13744196555731876776902083 20616294833597815165353125)
                    ·
                      refine ⟨3865555281299590343503711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20616294833597815165353125 3865555281299590343503711)
                      ·
                        rfl

theorem cell23_7528142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7528142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528142 prefixEnd_7528142 := by exact prefixLift 7528142
  have htrace : WordTrace (prefixWord ++ tailWord_7528142) baseStart_7528142 baseEnd_7528142 := by
    simpa [prefixWord, tailWord_7528142, baseEnd_7528142] using wordTrace_append hprefix tailTrace_7528142
  have hstable : (prefixWord ++ tailWord_7528142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528142).length < 2 ^ (prefixWord ++ tailWord_7528142).sum := by decide
  have hdescent : baseEnd_7528142 < baseStart_7528142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528152 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_7528152 : Nat := 118140960795 + 7528152 * 2 ^ 59
def prefixEnd_7528152 : Nat := 4983230072969 + 3 ^ 40 * 7528152 * 2
def baseEnd_7528152 : Nat := 1288520138702045101459555

theorem tailTrace_7528152 : CollatzResearch.WordTrace tailWord_7528152 prefixEnd_7528152 1288520138702045101459555 := by
  unfold tailWord_7528152
  simp only [CollatzResearch.WordTrace]
  refine ⟨137287130311399242423213355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183049507081865656564284473 137287130311399242423213355)
  ·
    refine ⟨205930695467098863634820033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137287130311399242423213355 205930695467098863634820033)
    ·
      refine ⟨154448021600324147726115025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205930695467098863634820033 154448021600324147726115025)
      ·
        refine ⟨115836016200243110794586269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154448021600324147726115025 115836016200243110794586269)
        ·
          refine ⟨43438506075091166547969851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115836016200243110794586269 43438506075091166547969851)
          ·
            refine ⟨65157759112636749821954777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43438506075091166547969851 65157759112636749821954777)
            ·
              refine ⟨48868319334477562366466083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65157759112636749821954777 48868319334477562366466083)
              ·
                refine ⟨73302479001716343549699125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48868319334477562366466083 73302479001716343549699125)
                ·
                  refine ⟨6872107406410907207784293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73302479001716343549699125 6872107406410907207784293)
                  ·
                    refine ⟨1288520138702045101459555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872107406410907207784293 1288520138702045101459555)
                    ·
                      rfl

theorem cell23_7528152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_7528152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528152 prefixEnd_7528152 := by exact prefixLift 7528152
  have htrace : WordTrace (prefixWord ++ tailWord_7528152) baseStart_7528152 baseEnd_7528152 := by
    simpa [prefixWord, tailWord_7528152, baseEnd_7528152] using wordTrace_append hprefix tailTrace_7528152
  have hstable : (prefixWord ++ tailWord_7528152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528152).length < 2 ^ (prefixWord ++ tailWord_7528152).sum := by decide
  have hdescent : baseEnd_7528152 < baseStart_7528152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528156 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7528156 : Nat := 118140960795 + 7528156 * 2 ^ 59
def prefixEnd_7528156 : Nat := 4983230072969 + 3 ^ 40 * 7528156 * 2
def baseEnd_7528156 : Nat := 1288520823342917762909549

theorem tailTrace_7528156 : CollatzResearch.WordTrace tailWord_7528156 prefixEnd_7528156 1288520823342917762909549 := by
  unfold tailWord_7528156
  simp only [CollatzResearch.WordTrace]
  refine ⟨137287203257391996764786161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183049604343189329019714881 137287203257391996764786161)
  ·
    refine ⟨102965402443043997573589621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137287203257391996764786161 102965402443043997573589621)
    ·
      refine ⟨9653006479035374772524027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102965402443043997573589621 9653006479035374772524027)
      ·
        refine ⟨14479509718553062158786041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9653006479035374772524027 14479509718553062158786041)
        ·
          refine ⟨10859632288914796619089531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14479509718553062158786041 10859632288914796619089531)
          ·
            refine ⟨16289448433372194928634297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10859632288914796619089531 16289448433372194928634297)
            ·
              refine ⟨12217086325029146196475723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16289448433372194928634297 12217086325029146196475723)
              ·
                refine ⟨18325629487543719294713585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12217086325029146196475723 18325629487543719294713585)
                ·
                  refine ⟨13744222115657789471035189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18325629487543719294713585 13744222115657789471035189)
                  ·
                    refine ⟨1288520823342917762909549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13744222115657789471035189 1288520823342917762909549)
                    ·
                      rfl

theorem cell23_7528156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7528156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528156 prefixEnd_7528156 := by exact prefixLift 7528156
  have htrace : WordTrace (prefixWord ++ tailWord_7528156) baseStart_7528156 baseEnd_7528156 := by
    simpa [prefixWord, tailWord_7528156, baseEnd_7528156] using wordTrace_append hprefix tailTrace_7528156
  have hstable : (prefixWord ++ tailWord_7528156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528156).length < 2 ^ (prefixWord ++ tailWord_7528156).sum := by decide
  have hdescent : baseEnd_7528156 < baseStart_7528156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528169 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 1, 4]
def baseStart_7528169 : Nat := 118140960795 + 7528169 * 2 ^ 59
def prefixEnd_7528169 : Nat := 4983230072969 + 3 ^ 40 * 7528169 * 2
def baseEnd_7528169 : Nat := 1288523048425753912622029

theorem tailTrace_7528169 : CollatzResearch.WordTrace tailWord_7528169 prefixEnd_7528169 1288523048425753912622029 := by
  unfold tailWord_7528169
  simp only [CollatzResearch.WordTrace]
  refine ⟨274574880663736896749795561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183049920442491264499863707 274574880663736896749795561)
  ·
    refine ⟨205931160497802672562346671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274574880663736896749795561 205931160497802672562346671)
    ·
      refine ⟨308896740746704008843520007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205931160497802672562346671 308896740746704008843520007)
      ·
        refine ⟨463345111120056013265280011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308896740746704008843520007 463345111120056013265280011)
        ·
          refine ⟨695017666680084019897920017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463345111120056013265280011 695017666680084019897920017)
          ·
            refine ⟨521263250010063014923440013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695017666680084019897920017 521263250010063014923440013)
            ·
              refine ⟨195473718753773630596290005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521263250010063014923440013 195473718753773630596290005)
              ·
                refine ⟨4581415283291569467100547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195473718753773630596290005 4581415283291569467100547)
                ·
                  refine ⟨6872122924937354200650821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581415283291569467100547 6872122924937354200650821)
                  ·
                    refine ⟨1288523048425753912622029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872122924937354200650821 1288523048425753912622029)
                    ·
                      rfl

theorem cell23_7528169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 4].length) (baseStart_7528169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528169 prefixEnd_7528169 := by exact prefixLift 7528169
  have htrace : WordTrace (prefixWord ++ tailWord_7528169) baseStart_7528169 baseEnd_7528169 := by
    simpa [prefixWord, tailWord_7528169, baseEnd_7528169] using wordTrace_append hprefix tailTrace_7528169
  have hstable : (prefixWord ++ tailWord_7528169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528169).length < 2 ^ (prefixWord ++ tailWord_7528169).sum := by decide
  have hdescent : baseEnd_7528169 < baseStart_7528169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528229 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_7528229 : Nat := 118140960795 + 7528229 * 2 ^ 59
def prefixEnd_7528229 : Nat := 4983230072969 + 3 ^ 40 * 7528229 * 2
def baseEnd_7528229 : Nat := 1288533318038843834371937

theorem tailTrace_7528229 : CollatzResearch.WordTrace tailWord_7528229 prefixEnd_7528229 1288533318038843834371937 := by
  unfold tailWord_7528229
  simp only [CollatzResearch.WordTrace]
  refine ⟨274577069043519526996979741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183051379362346351331319827 274577069043519526996979741)
  ·
    refine ⟨102966400891319822623867403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274577069043519526996979741 102966400891319822623867403)
    ·
      refine ⟨154449601336979733935801105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102966400891319822623867403 154449601336979733935801105)
      ·
        refine ⟨115837201002734800451850829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154449601336979733935801105 115837201002734800451850829)
        ·
          refine ⟨43438950376025550169444061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115837201002734800451850829 43438950376025550169444061)
          ·
            refine ⟨16289606391009581313541523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43438950376025550169444061 16289606391009581313541523)
            ·
              refine ⟨24434409586514371970312285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16289606391009581313541523 24434409586514371970312285)
              ·
                refine ⟨9162903594942889488867107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24434409586514371970312285 9162903594942889488867107)
                ·
                  refine ⟨13744355392414334233300661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9162903594942889488867107 13744355392414334233300661)
                  ·
                    refine ⟨1288533318038843834371937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13744355392414334233300661 1288533318038843834371937)
                    ·
                      rfl

theorem cell23_7528229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_7528229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528229 prefixEnd_7528229 := by exact prefixLift 7528229
  have htrace : WordTrace (prefixWord ++ tailWord_7528229) baseStart_7528229 baseEnd_7528229 := by
    simpa [prefixWord, tailWord_7528229, baseEnd_7528229] using wordTrace_append hprefix tailTrace_7528229
  have hstable : (prefixWord ++ tailWord_7528229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528229).length < 2 ^ (prefixWord ++ tailWord_7528229).sum := by decide
  have hdescent : baseEnd_7528229 < baseStart_7528229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528252 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7528252 : Nat := 118140960795 + 7528252 * 2 ^ 59
def prefixEnd_7528252 : Nat := 4983230072969 + 3 ^ 40 * 7528252 * 2
def baseEnd_7528252 : Nat := 3865611764171584913128205

theorem tailTrace_7528252 : CollatzResearch.WordTrace tailWord_7528252 prefixEnd_7528252 3865611764171584913128205 := by
  unfold tailWord_7528252
  simp only [CollatzResearch.WordTrace]
  refine ⟨137288953961218100962533505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183051938614957467950044673 137288953961218100962533505)
  ·
    refine ⟨102966715470913575721900129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137288953961218100962533505 102966715470913575721900129)
    ·
      refine ⟨77225036603185181791425097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102966715470913575721900129 77225036603185181791425097)
      ·
        refine ⟨57918777452388886343568823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77225036603185181791425097 57918777452388886343568823)
        ·
          refine ⟨86878166178583329515353235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57918777452388886343568823 86878166178583329515353235)
          ·
            refine ⟨130317249267874994273029853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86878166178583329515353235 130317249267874994273029853)
            ·
              refine ⟨48868968475453122852386195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130317249267874994273029853 48868968475453122852386195)
              ·
                refine ⟨73303452713179684278579293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48868968475453122852386195 73303452713179684278579293)
                ·
                  refine ⟨27488794767442381604467235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73303452713179684278579293 27488794767442381604467235)
                  ·
                    refine ⟨41233192151163572406700853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27488794767442381604467235 41233192151163572406700853)
                    ·
                      refine ⟨3865611764171584913128205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41233192151163572406700853 3865611764171584913128205)
                      ·
                        rfl

theorem cell23_7528252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7528252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528252 prefixEnd_7528252 := by exact prefixLift 7528252
  have htrace : WordTrace (prefixWord ++ tailWord_7528252) baseStart_7528252 baseEnd_7528252 := by
    simpa [prefixWord, tailWord_7528252, baseEnd_7528252] using wordTrace_append hprefix tailTrace_7528252
  have hstable : (prefixWord ++ tailWord_7528252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528252).length < 2 ^ (prefixWord ++ tailWord_7528252).sum := by decide
  have hdescent : baseEnd_7528252 < baseStart_7528252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528259 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 1, 6]
def baseStart_7528259 : Nat := 118140960795 + 7528259 * 2 ^ 59
def prefixEnd_7528259 : Nat := 4983230072969 + 3 ^ 40 * 7528259 * 2
def baseEnd_7528259 : Nat := 1288538452845388795246891

theorem tailTrace_7528259 : CollatzResearch.WordTrace tailWord_7528259 prefixEnd_7528259 1288538452845388795246891 := by
  unfold tailWord_7528259
  simp only [CollatzResearch.WordTrace]
  refine ⟨274578163233410842120571831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183052108822273894747047887 274578163233410842120571831)
  ·
    refine ⟨411867244850116263180857747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274578163233410842120571831 411867244850116263180857747)
    ·
      refine ⟨617800867275174394771286621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411867244850116263180857747 617800867275174394771286621)
      ·
        refine ⟨231675325228190398039232483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617800867275174394771286621 231675325228190398039232483)
        ·
          refine ⟨347512987842285597058848725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231675325228190398039232483 347512987842285597058848725)
          ·
            refine ⟨8144835652553568681066767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 347512987842285597058848725 8144835652553568681066767)
            ·
              refine ⟨12217253478830353021600151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144835652553568681066767 12217253478830353021600151)
              ·
                refine ⟨18325880218245529532400227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12217253478830353021600151 18325880218245529532400227)
                ·
                  refine ⟨27488820327368294298600341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18325880218245529532400227 27488820327368294298600341)
                  ·
                    refine ⟨1288538452845388795246891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27488820327368294298600341 1288538452845388795246891)
                    ·
                      rfl

theorem cell23_7528259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 6].length) (baseStart_7528259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528259 prefixEnd_7528259 := by exact prefixLift 7528259
  have htrace : WordTrace (prefixWord ++ tailWord_7528259) baseStart_7528259 baseEnd_7528259 := by
    simpa [prefixWord, tailWord_7528259, baseEnd_7528259] using wordTrace_append hprefix tailTrace_7528259
  have hstable : (prefixWord ++ tailWord_7528259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528259).length < 2 ^ (prefixWord ++ tailWord_7528259).sum := by decide
  have hdescent : baseEnd_7528259 < baseStart_7528259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528266 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_7528266 : Nat := 118140960795 + 7528266 * 2 ^ 59
def prefixEnd_7528266 : Nat := 4983230072969 + 3 ^ 40 * 7528266 * 2
def baseEnd_7528266 : Nat := 3865618952900747858353141

theorem tailTrace_7528266 : CollatzResearch.WordTrace tailWord_7528266 prefixEnd_7528266 3865618952900747858353141 := by
  unfold tailWord_7528266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68644604636096370579019163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183052279029590321544051101 68644604636096370579019163)
  ·
    refine ⟨102966906954144555868528745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68644604636096370579019163 102966906954144555868528745)
    ·
      refine ⟨77225180215608416901396559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102966906954144555868528745 77225180215608416901396559)
      ·
        refine ⟨115837770323412625352094839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77225180215608416901396559 115837770323412625352094839)
        ·
          refine ⟨173756655485118938028142259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115837770323412625352094839 173756655485118938028142259)
          ·
            refine ⟨260634983227678407042213389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173756655485118938028142259 260634983227678407042213389)
            ·
              refine ⟨97738118710379402640830021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260634983227678407042213389 97738118710379402640830021)
              ·
                refine ⟨18325897258196137995155629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97738118710379402640830021 18325897258196137995155629)
                ·
                  refine ⟨6872211471823551748183361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18325897258196137995155629 6872211471823551748183361)
                  ·
                    refine ⟨5154158603867663811137521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872211471823551748183361 5154158603867663811137521)
                    ·
                      refine ⟨3865618952900747858353141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154158603867663811137521 3865618952900747858353141)
                      ·
                        rfl

theorem cell23_7528266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_7528266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528266 prefixEnd_7528266 := by exact prefixLift 7528266
  have htrace : WordTrace (prefixWord ++ tailWord_7528266) baseStart_7528266 baseEnd_7528266 := by
    simpa [prefixWord, tailWord_7528266, baseEnd_7528266] using wordTrace_append hprefix tailTrace_7528266
  have hstable : (prefixWord ++ tailWord_7528266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528266).length < 2 ^ (prefixWord ++ tailWord_7528266).sum := by decide
  have hdescent : baseEnd_7528266 < baseStart_7528266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528332 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_7528332 : Nat := 118140960795 + 7528332 * 2 ^ 59
def prefixEnd_7528332 : Nat := 4983230072969 + 3 ^ 40 * 7528332 * 2
def baseEnd_7528332 : Nat := 1288550947541314866709279

theorem tailTrace_7528332 : CollatzResearch.WordTrace tailWord_7528332 prefixEnd_7528332 1288550947541314866709279 := by
  unfold tailWord_7528332
  simp only [CollatzResearch.WordTrace]
  refine ⟨137290412881073187793989625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183053883841430917058652833 137290412881073187793989625)
  ·
    refine ⟨102967809660804890845492219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137290412881073187793989625 102967809660804890845492219)
    ·
      refine ⟨154451714491207336268238329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102967809660804890845492219 154451714491207336268238329)
      ·
        refine ⟨115838785868405502201178747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154451714491207336268238329 115838785868405502201178747)
        ·
          refine ⟨173758178802608253301768121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115838785868405502201178747 173758178802608253301768121)
          ·
            refine ⟨130318634101956189976326091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173758178802608253301768121 130318634101956189976326091)
            ·
              refine ⟨195477951152934284964489137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130318634101956189976326091 195477951152934284964489137)
              ·
                refine ⟨146608463364700713723366853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195477951152934284964489137 146608463364700713723366853)
                ·
                  refine ⟨27489086880881383823131285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146608463364700713723366853 27489086880881383823131285)
                  ·
                    refine ⟨1288550947541314866709279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27489086880881383823131285 1288550947541314866709279)
                    ·
                      rfl

theorem cell23_7528332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_7528332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528332 prefixEnd_7528332 := by exact prefixLift 7528332
  have htrace : WordTrace (prefixWord ++ tailWord_7528332) baseStart_7528332 baseEnd_7528332 := by
    simpa [prefixWord, tailWord_7528332, baseEnd_7528332] using wordTrace_append hprefix tailTrace_7528332
  have hstable : (prefixWord ++ tailWord_7528332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528332).length < 2 ^ (prefixWord ++ tailWord_7528332).sum := by decide
  have hdescent : baseEnd_7528332 < baseStart_7528332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528352 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_7528352 : Nat := 118140960795 + 7528352 * 2 ^ 59
def prefixEnd_7528352 : Nat := 4983230072969 + 3 ^ 40 * 7528352 * 2
def baseEnd_7528352 : Nat := 3865663112237034521877745

theorem tailTrace_7528352 : CollatzResearch.WordTrace tailWord_7528352 prefixEnd_7528352 3865663112237034521877745 := by
  unfold tailWord_7528352
  simp only [CollatzResearch.WordTrace]
  refine ⟨137290777611036959501853655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183054370148049279335804873 137290777611036959501853655)
  ·
    refine ⟨205936166416555439252780483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137290777611036959501853655 205936166416555439252780483)
    ·
      refine ⟨308904249624833158879170725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205936166416555439252780483 308904249624833158879170725)
      ·
        refine ⟨57919546804656217289844511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308904249624833158879170725 57919546804656217289844511)
        ·
          refine ⟨86879320206984325934766767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57919546804656217289844511 86879320206984325934766767)
          ·
            refine ⟨130318980310476488902150151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86879320206984325934766767 130318980310476488902150151)
            ·
              refine ⟨195478470465714733353225227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130318980310476488902150151 195478470465714733353225227)
              ·
                refine ⟨293217705698572100029837841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195478470465714733353225227 293217705698572100029837841)
                ·
                  refine ⟨219913279273929075022378381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293217705698572100029837841 219913279273929075022378381)
                  ·
                    refine ⟨82467479727723403133391893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219913279273929075022378381 82467479727723403133391893)
                    ·
                      refine ⟨3865663112237034521877745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82467479727723403133391893 3865663112237034521877745)
                      ·
                        rfl

theorem cell23_7528352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_7528352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528352 prefixEnd_7528352 := by exact prefixLift 7528352
  have htrace : WordTrace (prefixWord ++ tailWord_7528352) baseStart_7528352 baseEnd_7528352 := by
    simpa [prefixWord, tailWord_7528352, baseEnd_7528352] using wordTrace_append hprefix tailTrace_7528352
  have hstable : (prefixWord ++ tailWord_7528352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528352).length < 2 ^ (prefixWord ++ tailWord_7528352).sum := by decide
  have hdescent : baseEnd_7528352 < baseStart_7528352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528369 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7528369 : Nat := 118140960795 + 7528369 * 2 ^ 59
def prefixEnd_7528369 : Nat := 4983230072969 + 3 ^ 40 * 7528369 * 2
def baseEnd_7528369 : Nat := 3865671841408160955365167

theorem tailTrace_7528369 : CollatzResearch.WordTrace tailWord_7528369 prefixEnd_7528369 3865671841408160955365167 := by
  unfold tailWord_7528369
  simp only [CollatzResearch.WordTrace]
  refine ⟨274582175263012330907076161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183054783508674887271384107 274582175263012330907076161)
  ·
    refine ⟨205936631447259248180307121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274582175263012330907076161 205936631447259248180307121)
    ·
      refine ⟨154452473585444436135230341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205936631447259248180307121 154452473585444436135230341)
      ·
        refine ⟨28959838797270831775355689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154452473585444436135230341 28959838797270831775355689)
        ·
          refine ⟨21719879097953123831516767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28959838797270831775355689 21719879097953123831516767)
          ·
            refine ⟨32579818646929685747275151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21719879097953123831516767 32579818646929685747275151)
            ·
              refine ⟨48869727970394528620912727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32579818646929685747275151 48869727970394528620912727)
              ·
                refine ⟨73304591955591792931369091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48869727970394528620912727 73304591955591792931369091)
                ·
                  refine ⟨109956887933387689397053637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73304591955591792931369091 109956887933387689397053637)
                  ·
                    refine ⟨20616916487510191761947557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109956887933387689397053637 20616916487510191761947557)
                    ·
                      refine ⟨3865671841408160955365167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20616916487510191761947557 3865671841408160955365167)
                      ·
                        rfl

theorem cell23_7528369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7528369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528369 prefixEnd_7528369 := by exact prefixLift 7528369
  have htrace : WordTrace (prefixWord ++ tailWord_7528369) baseStart_7528369 baseEnd_7528369 := by
    simpa [prefixWord, tailWord_7528369, baseEnd_7528369] using wordTrace_append hprefix tailTrace_7528369
  have hstable : (prefixWord ++ tailWord_7528369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528369).length < 2 ^ (prefixWord ++ tailWord_7528369).sum := by decide
  have hdescent : baseEnd_7528369 < baseStart_7528369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528373 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_7528373 : Nat := 118140960795 + 7528373 * 2 ^ 59
def prefixEnd_7528373 : Nat := 4983230072969 + 3 ^ 40 * 7528373 * 2
def baseEnd_7528373 : Nat := 3865673895330778939715149

theorem tailTrace_7528373 : CollatzResearch.WordTrace tailWord_7528373 prefixEnd_7528373 3865673895330778939715149 := by
  unfold tailWord_7528373
  simp only [CollatzResearch.WordTrace]
  refine ⟨274582321154997839590221773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183054880769998559726814515 274582321154997839590221773)
  ·
    refine ⟨102968370433124189846333165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274582321154997839590221773 102968370433124189846333165)
    ·
      refine ⟨38613138912421571192374937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102968370433124189846333165 38613138912421571192374937)
      ·
        refine ⟨28959854184316178394281203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38613138912421571192374937 28959854184316178394281203)
        ·
          refine ⟨43439781276474267591421805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28959854184316178394281203 43439781276474267591421805)
          ·
            refine ⟨16289917978677850346783177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43439781276474267591421805 16289917978677850346783177)
            ·
              refine ⟨12217438484008387760087383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16289917978677850346783177 12217438484008387760087383)
              ·
                refine ⟨18326157726012581640131075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12217438484008387760087383 18326157726012581640131075)
                ·
                  refine ⟨27489236589018872460196613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18326157726012581640131075 27489236589018872460196613)
                  ·
                    refine ⟨5154231860441038586286865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27489236589018872460196613 5154231860441038586286865)
                    ·
                      refine ⟨3865673895330778939715149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154231860441038586286865 3865673895330778939715149)
                      ·
                        rfl

theorem cell23_7528373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_7528373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528373 prefixEnd_7528373 := by exact prefixLift 7528373
  have htrace : WordTrace (prefixWord ++ tailWord_7528373) baseStart_7528373 baseEnd_7528373 := by
    simpa [prefixWord, tailWord_7528373, baseEnd_7528373] using wordTrace_append hprefix tailTrace_7528373
  have hstable : (prefixWord ++ tailWord_7528373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528373).length < 2 ^ (prefixWord ++ tailWord_7528373).sum := by decide
  have hdescent : baseEnd_7528373 < baseStart_7528373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528396 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 5]
def baseStart_7528396 : Nat := 118140960795 + 7528396 * 2 ^ 59
def prefixEnd_7528396 : Nat := 4983230072969 + 3 ^ 40 * 7528396 * 2
def baseEnd_7528396 : Nat := 429520633931759149969727

theorem tailTrace_7528396 : CollatzResearch.WordTrace tailWord_7528396 prefixEnd_7528396 429520633931759149969727 := by
  unfold tailWord_7528396
  simp only [CollatzResearch.WordTrace]
  refine ⟨137291580016957257259154521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183055440022609676345539361 137291580016957257259154521)
  ·
    refine ⟨102968685012717942944365891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137291580016957257259154521 102968685012717942944365891)
    ·
      refine ⟨154453027519076914416548837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102968685012717942944365891 154453027519076914416548837)
      ·
        refine ⟨28959942659826921453102907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154453027519076914416548837 28959942659826921453102907)
        ·
          refine ⟨43439913989740382179654361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28959942659826921453102907 43439913989740382179654361)
          ·
            refine ⟨32579935492305286634740771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43439913989740382179654361 32579935492305286634740771)
            ·
              refine ⟨48869903238457929952111157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32579935492305286634740771 48869903238457929952111157)
              ·
                refine ⟨4581553428605430933010421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48869903238457929952111157 4581553428605430933010421)
                ·
                  refine ⟨429520633931759149969727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581553428605430933010421 429520633931759149969727)
                  ·
                    rfl

theorem cell23_7528396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_7528396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528396 prefixEnd_7528396 := by exact prefixLift 7528396
  have htrace : WordTrace (prefixWord ++ tailWord_7528396) baseStart_7528396 baseEnd_7528396 := by
    simpa [prefixWord, tailWord_7528396, baseEnd_7528396] using wordTrace_append hprefix tailTrace_7528396
  have hstable : (prefixWord ++ tailWord_7528396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528396).length < 2 ^ (prefixWord ++ tailWord_7528396).sum := by decide
  have hdescent : baseEnd_7528396 < baseStart_7528396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528529 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_7528529 : Nat := 118140960795 + 7528529 * 2 ^ 59
def prefixEnd_7528529 : Nat := 4983230072969 + 3 ^ 40 * 7528529 * 2
def baseEnd_7528529 : Nat := 1288584666104293443121477

theorem tailTrace_7528529 : CollatzResearch.WordTrace tailWord_7528529 prefixEnd_7528529 1288584666104293443121477 := by
  unfold tailWord_7528529
  simp only [CollatzResearch.WordTrace]
  refine ⟨274588010942432678232900641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183058673961621785488600427 274588010942432678232900641)
  ·
    refine ⟨205941008206824508674675481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274588010942432678232900641 205941008206824508674675481)
    ·
      refine ⟨154455756155118381506006611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205941008206824508674675481 154455756155118381506006611)
      ·
        refine ⟨231683634232677572259009917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154455756155118381506006611 231683634232677572259009917)
        ·
          refine ⟨86881362837254089597128719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231683634232677572259009917 86881362837254089597128719)
          ·
            refine ⟨130322044255881134395693079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86881362837254089597128719 130322044255881134395693079)
            ·
              refine ⟨195483066383821701593539619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130322044255881134395693079 195483066383821701593539619)
              ·
                refine ⟨293224599575732552390309429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195483066383821701593539619 293224599575732552390309429)
                ·
                  refine ⟨27489806210224926786591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293224599575732552390309429 27489806210224926786591509)
                  ·
                    refine ⟨1288584666104293443121477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27489806210224926786591509 1288584666104293443121477)
                    ·
                      rfl

theorem cell23_7528529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_7528529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528529 prefixEnd_7528529 := by exact prefixLift 7528529
  have htrace : WordTrace (prefixWord ++ tailWord_7528529) baseStart_7528529 baseEnd_7528529 := by
    simpa [prefixWord, tailWord_7528529, baseEnd_7528529] using wordTrace_append hprefix tailTrace_7528529
  have hstable : (prefixWord ++ tailWord_7528529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528529).length < 2 ^ (prefixWord ++ tailWord_7528529).sum := by decide
  have hdescent : baseEnd_7528529 < baseStart_7528529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528536 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_7528536 : Nat := 118140960795 + 7528536 * 2 ^ 59
def prefixEnd_7528536 : Nat := 4983230072969 + 3 ^ 40 * 7528536 * 2
def baseEnd_7528536 : Nat := 3865757592677461801976899

theorem tailTrace_7528536 : CollatzResearch.WordTrace tailWord_7528536 prefixEnd_7528536 3865757592677461801976899 := by
  unfold tailWord_7528536
  simp only [CollatzResearch.WordTrace]
  refine ⟨137294133126703659214202731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183058844168938212285603641 137294133126703659214202731)
  ·
    refine ⟨205941199690055488821304097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137294133126703659214202731 205941199690055488821304097)
    ·
      refine ⟨154455899767541616615978073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205941199690055488821304097 154455899767541616615978073)
      ·
        refine ⟨115841924825656212461983555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154455899767541616615978073 115841924825656212461983555)
        ·
          refine ⟨173762887238484318692975333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115841924825656212461983555 173762887238484318692975333)
          ·
            refine ⟨32580541357215809754932875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173762887238484318692975333 32580541357215809754932875)
            ·
              refine ⟨48870812035823714632399313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32580541357215809754932875 48870812035823714632399313)
              ·
                refine ⟨36653109026867785974299485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48870812035823714632399313 36653109026867785974299485)
                ·
                  refine ⟨13744915885075419740362307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36653109026867785974299485 13744915885075419740362307)
                  ·
                    refine ⟨20617373827613129610543461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13744915885075419740362307 20617373827613129610543461)
                    ·
                      refine ⟨3865757592677461801976899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20617373827613129610543461 3865757592677461801976899)
                      ·
                        rfl

theorem cell23_7528536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_7528536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528536 prefixEnd_7528536 := by exact prefixLift 7528536
  have htrace : WordTrace (prefixWord ++ tailWord_7528536) baseStart_7528536 baseEnd_7528536 := by
    simpa [prefixWord, tailWord_7528536, baseEnd_7528536] using wordTrace_append hprefix tailTrace_7528536
  have hstable : (prefixWord ++ tailWord_7528536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528536).length < 2 ^ (prefixWord ++ tailWord_7528536).sum := by decide
  have hdescent : baseEnd_7528536 < baseStart_7528536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528600 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7528600 : Nat := 118140960795 + 7528600 * 2 ^ 59
def prefixEnd_7528600 : Nat := 4983230072969 + 3 ^ 40 * 7528600 * 2
def baseEnd_7528600 : Nat := 3865790455439349551576605

theorem tailTrace_7528600 : CollatzResearch.WordTrace tailWord_7528600 prefixEnd_7528600 3865790455439349551576605 := by
  unfold tailWord_7528600
  simp only [CollatzResearch.WordTrace]
  refine ⟨137295300262587728679367627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183060400350116971572490169 137295300262587728679367627)
  ·
    refine ⟨205942950393881593019051441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137295300262587728679367627 205942950393881593019051441)
    ·
      refine ⟨154457212795411194764288581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205942950393881593019051441 154457212795411194764288581)
      ·
        refine ⟨28960727399139599018304109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154457212795411194764288581 28960727399139599018304109)
        ·
          refine ⟨10860272774677349631864041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28960727399139599018304109 10860272774677349631864041)
          ·
            refine ⟨8145204581008012223898031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10860272774677349631864041 8145204581008012223898031)
            ·
              refine ⟨12217806871512018335847047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145204581008012223898031 12217806871512018335847047)
              ·
                refine ⟨18326710307268027503770571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12217806871512018335847047 18326710307268027503770571)
                ·
                  refine ⟨27490065460902041255655857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18326710307268027503770571 27490065460902041255655857)
                  ·
                    refine ⟨20617549095676530941741893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27490065460902041255655857 20617549095676530941741893)
                    ·
                      refine ⟨3865790455439349551576605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20617549095676530941741893 3865790455439349551576605)
                      ·
                        rfl

theorem cell23_7528600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7528600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528600 prefixEnd_7528600 := by exact prefixLift 7528600
  have htrace : WordTrace (prefixWord ++ tailWord_7528600) baseStart_7528600 baseEnd_7528600 := by
    simpa [prefixWord, tailWord_7528600, baseEnd_7528600] using wordTrace_append hprefix tailTrace_7528600
  have hstable : (prefixWord ++ tailWord_7528600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528600).length < 2 ^ (prefixWord ++ tailWord_7528600).sum := by decide
  have hdescent : baseEnd_7528600 < baseStart_7528600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528610 : List Nat := [3, 3, 1, 3, 1, 3, 2, 7]
def baseStart_7528610 : Nat := 118140960795 + 7528610 * 2 ^ 59
def prefixEnd_7528610 : Nat := 4983230072969 + 3 ^ 40 * 7528610 * 2
def baseEnd_7528610 : Nat := 143177614453551648609317

theorem tailTrace_7528610 : CollatzResearch.WordTrace tailWord_7528610 prefixEnd_7528610 143177614453551648609317 := by
  unfold tailWord_7528610
  simp only [CollatzResearch.WordTrace]
  refine ⟨68647741313784807266649821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183060643503426152711066189 68647741313784807266649821)
  ·
    refine ⟨25742902992669302724993683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68647741313784807266649821 25742902992669302724993683)
    ·
      refine ⟨38614354489003954087490525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25742902992669302724993683 38614354489003954087490525)
      ·
        refine ⟨14480382933376482782808947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38614354489003954087490525 14480382933376482782808947)
        ·
          refine ⟨21720574400064724174213421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14480382933376482782808947 21720574400064724174213421)
          ·
            refine ⟨8145215400024271565330033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21720574400064724174213421 8145215400024271565330033)
            ·
              refine ⟨6108911550018203673997525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145215400024271565330033 6108911550018203673997525)
              ·
                refine ⟨143177614453551648609317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6108911550018203673997525 143177614453551648609317)
                ·
                  rfl

theorem cell23_7528610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_7528610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528610 prefixEnd_7528610 := by exact prefixLift 7528610
  have htrace : WordTrace (prefixWord ++ tailWord_7528610) baseStart_7528610 baseEnd_7528610 := by
    simpa [prefixWord, tailWord_7528610, baseEnd_7528610] using wordTrace_append hprefix tailTrace_7528610
  have hstable : (prefixWord ++ tailWord_7528610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528610).length < 2 ^ (prefixWord ++ tailWord_7528610).sum := by decide
  have hdescent : baseEnd_7528610 < baseStart_7528610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528621 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_7528621 : Nat := 118140960795 + 7528621 * 2 ^ 59
def prefixEnd_7528621 : Nat := 4983230072969 + 3 ^ 40 * 7528621 * 2
def baseEnd_7528621 : Nat := 3865801238533093969414009

theorem tailTrace_7528621 : CollatzResearch.WordTrace tailWord_7528621 prefixEnd_7528621 3865801238533093969414009 := by
  unfold tailWord_7528621
  simp only [CollatzResearch.WordTrace]
  refine ⟨274591366458099377945249717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183060910972066251963499811 274591366458099377945249717)
  ·
    refine ⟨25742940605446816682367161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274591366458099377945249717 25742940605446816682367161)
    ·
      refine ⟨19307205454085112511775371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25742940605446816682367161 19307205454085112511775371)
      ·
        refine ⟨28960808181127668767663057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19307205454085112511775371 28960808181127668767663057)
        ·
          refine ⟨21720606135845751575747293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28960808181127668767663057 21720606135845751575747293)
          ·
            refine ⟨8145227300942156840905235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21720606135845751575747293 8145227300942156840905235)
            ·
              refine ⟨12217840951413235261357853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145227300942156840905235 12217840951413235261357853)
              ·
                refine ⟨4581690356779963223009195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12217840951413235261357853 4581690356779963223009195)
                ·
                  refine ⟨6872535535169944834513793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581690356779963223009195 6872535535169944834513793)
                  ·
                    refine ⟨5154401651377458625885345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872535535169944834513793 5154401651377458625885345)
                    ·
                      refine ⟨3865801238533093969414009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154401651377458625885345 3865801238533093969414009)
                      ·
                        rfl

theorem cell23_7528621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_7528621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528621 prefixEnd_7528621 := by exact prefixLift 7528621
  have htrace : WordTrace (prefixWord ++ tailWord_7528621) baseStart_7528621 baseEnd_7528621 := by
    simpa [prefixWord, tailWord_7528621, baseEnd_7528621] using wordTrace_append hprefix tailTrace_7528621
  have hstable : (prefixWord ++ tailWord_7528621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528621).length < 2 ^ (prefixWord ++ tailWord_7528621).sum := by decide
  have hdescent : baseEnd_7528621 < baseStart_7528621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528654 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_7528654 : Nat := 118140960795 + 7528654 * 2 ^ 59
def prefixEnd_7528654 : Nat := 4983230072969 + 3 ^ 40 * 7528654 * 2
def baseEnd_7528654 : Nat := 3865818183394692340301357

theorem tailTrace_7528654 : CollatzResearch.WordTrace tailWord_7528654 prefixEnd_7528654 3865818183394692340301357 := by
  unfold tailWord_7528654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34324071258372478072650127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183061713377986549720800677 34324071258372478072650127)
  ·
    refine ⟨51486106887558717108975191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34324071258372478072650127 51486106887558717108975191)
    ·
      refine ⟨77229160331338075663462787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51486106887558717108975191 77229160331338075663462787)
      ·
        refine ⟨115843740497007113495194181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77229160331338075663462787 115843740497007113495194181)
        ·
          refine ⟨21720701343188833780348909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115843740497007113495194181 21720701343188833780348909)
          ·
            refine ⟨8145263003695812667630841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21720701343188833780348909 8145263003695812667630841)
            ·
              refine ⟨6108947252771859500723131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145263003695812667630841 6108947252771859500723131)
              ·
                refine ⟨9163420879157789251084697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108947252771859500723131 9163420879157789251084697)
                ·
                  refine ⟨6872565659368341938313523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9163420879157789251084697 6872565659368341938313523)
                  ·
                    refine ⟨10308848489052512907470285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6872565659368341938313523 10308848489052512907470285)
                    ·
                      refine ⟨3865818183394692340301357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10308848489052512907470285 3865818183394692340301357)
                      ·
                        rfl

theorem cell23_7528654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_7528654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528654 prefixEnd_7528654 := by exact prefixLift 7528654
  have htrace : WordTrace (prefixWord ++ tailWord_7528654) baseStart_7528654 baseEnd_7528654 := by
    simpa [prefixWord, tailWord_7528654, baseEnd_7528654] using wordTrace_append hprefix tailTrace_7528654
  have hstable : (prefixWord ++ tailWord_7528654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528654).length < 2 ^ (prefixWord ++ tailWord_7528654).sum := by decide
  have hdescent : baseEnd_7528654 < baseStart_7528654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528666 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_7528666 : Nat := 118140960795 + 7528666 * 2 ^ 59
def prefixEnd_7528666 : Nat := 4983230072969 + 3 ^ 40 * 7528666 * 2
def baseEnd_7528666 : Nat := 429536038351394032594589

theorem tailTrace_7528666 : CollatzResearch.WordTrace tailWord_7528666 prefixEnd_7528666 429536038351394032594589 := by
  unfold tailWord_7528666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68648251935734087657659463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183062005161957567087091901 68648251935734087657659463)
  ·
    refine ⟨102972377903601131486489195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68648251935734087657659463 102972377903601131486489195)
    ·
      refine ⟨154458566855401697229733793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102972377903601131486489195 154458566855401697229733793)
      ·
        refine ⟨115843925141551272922300345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154458566855401697229733793 115843925141551272922300345)
        ·
          refine ⟨86882943856163454691725259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115843925141551272922300345 86882943856163454691725259)
          ·
            refine ⟨130324415784245182037587889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86882943856163454691725259 130324415784245182037587889)
            ·
              refine ⟨97743311838183886528190917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130324415784245182037587889 97743311838183886528190917)
              ·
                refine ⟨18326870969659478724035797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97743311838183886528190917 18326870969659478724035797)
                ·
                  refine ⟨429536038351394032594589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18326870969659478724035797 429536038351394032594589)
                  ·
                    rfl

theorem cell23_7528666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_7528666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528666 prefixEnd_7528666 := by exact prefixLift 7528666
  have htrace : WordTrace (prefixWord ++ tailWord_7528666) baseStart_7528666 baseEnd_7528666 := by
    simpa [prefixWord, tailWord_7528666, baseEnd_7528666] using wordTrace_append hprefix tailTrace_7528666
  have hstable : (prefixWord ++ tailWord_7528666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528666).length < 2 ^ (prefixWord ++ tailWord_7528666).sum := by decide
  have hdescent : baseEnd_7528666 < baseStart_7528666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528683 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 5]
def baseStart_7528683 : Nat := 118140960795 + 7528683 * 2 ^ 59
def prefixEnd_7528683 : Nat := 4983230072969 + 3 ^ 40 * 7528683 * 2
def baseEnd_7528683 : Nat := 429537008259296969648747

theorem tailTrace_7528683 : CollatzResearch.WordTrace tailWord_7528683 prefixEnd_7528683 429537008259296969648747 := by
  unfold tailWord_7528683
  simp only [CollatzResearch.WordTrace]
  refine ⟨274593627783874762534006703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183062418522583175022671135 274593627783874762534006703)
  ·
    refine ⟨411890441675812143801010055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274593627783874762534006703 411890441675812143801010055)
    ·
      refine ⟨617835662513718215701515083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411890441675812143801010055 617835662513718215701515083)
      ·
        refine ⟨926753493770577323552272625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617835662513718215701515083 926753493770577323552272625)
        ·
          refine ⟨695065120327932992664204469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926753493770577323552272625 695065120327932992664204469)
          ·
            refine ⟨65162355030743718062269169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 695065120327932992664204469 65162355030743718062269169)
            ·
              refine ⟨48871766273057788546701877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65162355030743718062269169 48871766273057788546701877)
              ·
                refine ⟨4581728088099167676253301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48871766273057788546701877 4581728088099167676253301)
                ·
                  refine ⟨429537008259296969648747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581728088099167676253301 429537008259296969648747)
                  ·
                    rfl

theorem cell23_7528683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 5].length) (baseStart_7528683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528683 prefixEnd_7528683 := by exact prefixLift 7528683
  have htrace : WordTrace (prefixWord ++ tailWord_7528683) baseStart_7528683 baseEnd_7528683 := by
    simpa [prefixWord, tailWord_7528683, baseEnd_7528683] using wordTrace_append hprefix tailTrace_7528683
  have hstable : (prefixWord ++ tailWord_7528683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528683).length < 2 ^ (prefixWord ++ tailWord_7528683).sum := by decide
  have hdescent : baseEnd_7528683 < baseStart_7528683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528700 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 5]
def baseStart_7528700 : Nat := 118140960795 + 7528700 * 2 ^ 59
def prefixEnd_7528700 : Nat := 4983230072969 + 3 ^ 40 * 7528700 * 2
def baseEnd_7528700 : Nat := 429537978167199906702905

theorem tailTrace_7528700 : CollatzResearch.WordTrace tailWord_7528700 prefixEnd_7528700 429537978167199906702905 := by
  unfold tailWord_7528700
  simp only [CollatzResearch.WordTrace]
  refine ⟨137297123912406587218687777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183062831883208782958250369 137297123912406587218687777)
  ·
    refine ⟨102972842934304940414015833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137297123912406587218687777 102972842934304940414015833)
    ·
      refine ⟨77229632200728705310511875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102972842934304940414015833 77229632200728705310511875)
      ·
        refine ⟨115844448301093057965767813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77229632200728705310511875 115844448301093057965767813)
        ·
          refine ⟨21720834056454948368581465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115844448301093057965767813 21720834056454948368581465)
          ·
            refine ⟨16290625542341211276436099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21720834056454948368581465 16290625542341211276436099)
            ·
              refine ⟨24435938313511816914654149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16290625542341211276436099 24435938313511816914654149)
              ·
                refine ⟨4581738433783465671497653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24435938313511816914654149 4581738433783465671497653)
                ·
                  refine ⟨429537978167199906702905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581738433783465671497653 429537978167199906702905)
                  ·
                    rfl

theorem cell23_7528700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_7528700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528700 prefixEnd_7528700 := by exact prefixLift 7528700
  have htrace : WordTrace (prefixWord ++ tailWord_7528700) baseStart_7528700 baseEnd_7528700 := by
    simpa [prefixWord, tailWord_7528700, baseEnd_7528700] using wordTrace_append hprefix tailTrace_7528700
  have hstable : (prefixWord ++ tailWord_7528700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528700).length < 2 ^ (prefixWord ++ tailWord_7528700).sum := by decide
  have hdescent : baseEnd_7528700 < baseStart_7528700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528703 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 7, 2]
def baseStart_7528703 : Nat := 118140960795 + 7528703 * 2 ^ 59
def prefixEnd_7528703 : Nat := 4983230072969 + 3 ^ 40 * 7528703 * 2
def baseEnd_7528703 : Nat := 3865843343946762648588631

theorem tailTrace_7528703 : CollatzResearch.WordTrace tailWord_7528703 prefixEnd_7528703 3865843343946762648588631 := by
  unfold tailWord_7528703
  simp only [CollatzResearch.WordTrace]
  refine ⟨274594357243802305949734763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183062904829201537299823175 274594357243802305949734763)
  ·
    refine ⟨411891535865703458924602145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274594357243802305949734763 411891535865703458924602145)
    ·
      refine ⟨308918651899277594193451609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411891535865703458924602145 308918651899277594193451609)
      ·
        refine ⟨231688988924458195645088707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308918651899277594193451609 231688988924458195645088707)
        ·
          refine ⟨347533483386687293467633061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231688988924458195645088707 347533483386687293467633061)
          ·
            refine ⟨65162528135003867525181199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347533483386687293467633061 65162528135003867525181199)
            ·
              refine ⟨97743792202505801287771799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65162528135003867525181199 97743792202505801287771799)
              ·
                refine ⟨146615688303758701931657699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97743792202505801287771799 146615688303758701931657699)
                ·
                  refine ⟨219923532455638052897486549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146615688303758701931657699 219923532455638052897486549)
                  ·
                    refine ⟨5154457791929016864784841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 219923532455638052897486549 5154457791929016864784841)
                    ·
                      refine ⟨3865843343946762648588631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154457791929016864784841 3865843343946762648588631)
                      ·
                        rfl

theorem cell23_7528703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_7528703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528703 prefixEnd_7528703 := by exact prefixLift 7528703
  have htrace : WordTrace (prefixWord ++ tailWord_7528703) baseStart_7528703 baseEnd_7528703 := by
    simpa [prefixWord, tailWord_7528703, baseEnd_7528703] using wordTrace_append hprefix tailTrace_7528703
  have hstable : (prefixWord ++ tailWord_7528703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528703).length < 2 ^ (prefixWord ++ tailWord_7528703).sum := by decide
  have hdescent : baseEnd_7528703 < baseStart_7528703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528734 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_7528734 : Nat := 118140960795 + 7528734 * 2 ^ 59
def prefixEnd_7528734 : Nat := 4983230072969 + 3 ^ 40 * 7528734 * 2
def baseEnd_7528734 : Nat := 429539917983005780811221

theorem tailTrace_7528734 : CollatzResearch.WordTrace tailWord_7528734 prefixEnd_7528734 429539917983005780811221 := by
  unfold tailWord_7528734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34324435988336249780514157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183063658604459998829408837 34324435988336249780514157)
  ·
    refine ⟨12871663495626093667692809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34324435988336249780514157 12871663495626093667692809)
    ·
      refine ⟨9653747621719570250769607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12871663495626093667692809 9653747621719570250769607)
      ·
        refine ⟨14480621432579355376154411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9653747621719570250769607 14480621432579355376154411)
        ·
          refine ⟨21720932148869033064231617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14480621432579355376154411 21720932148869033064231617)
          ·
            refine ⟨16290699111651774798173713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21720932148869033064231617 16290699111651774798173713)
            ·
              refine ⟨12218024333738831098630285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16290699111651774798173713 12218024333738831098630285)
              ·
                refine ⟨4581759125152061661986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218024333738831098630285 4581759125152061661986357)
                ·
                  refine ⟨429539917983005780811221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581759125152061661986357 429539917983005780811221)
                  ·
                    rfl

theorem cell23_7528734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_7528734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528734 prefixEnd_7528734 := by exact prefixLift 7528734
  have htrace : WordTrace (prefixWord ++ tailWord_7528734) baseStart_7528734 baseEnd_7528734 := by
    simpa [prefixWord, tailWord_7528734, baseEnd_7528734] using wordTrace_append hprefix tailTrace_7528734
  have hstable : (prefixWord ++ tailWord_7528734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528734).length < 2 ^ (prefixWord ++ tailWord_7528734).sum := by decide
  have hdescent : baseEnd_7528734 < baseStart_7528734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528840 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7528840 : Nat := 118140960795 + 7528840 * 2 ^ 59
def prefixEnd_7528840 : Nat := 4983230072969 + 3 ^ 40 * 7528840 * 2
def baseEnd_7528840 : Nat := 3865913690796428612575501

theorem tailTrace_7528840 : CollatzResearch.WordTrace tailWord_7528840 prefixEnd_7528840 3865913690796428612575501 := by
  unfold tailWord_7528840
  simp only [CollatzResearch.WordTrace]
  refine ⟨137299677022152989173735987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183066236029537318898314649 137299677022152989173735987)
  ·
    refine ⟨205949515533229483760603981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137299677022152989173735987 205949515533229483760603981)
    ·
      refine ⟨77231068324961056410226493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205949515533229483760603981 77231068324961056410226493)
      ·
        refine ⟨28961650621860396153834935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77231068324961056410226493 28961650621860396153834935)
        ·
          refine ⟨43442475932790594230752403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28961650621860396153834935 43442475932790594230752403)
          ·
            refine ⟨65163713899185891346128605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43442475932790594230752403 65163713899185891346128605)
            ·
              refine ⟨24436392712194709254798227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65163713899185891346128605 24436392712194709254798227)
              ·
                refine ⟨36654589068292063882197341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24436392712194709254798227 36654589068292063882197341)
                ·
                  refine ⟨13745470900609523955824003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36654589068292063882197341 13745470900609523955824003)
                  ·
                    refine ⟨20618206350914285933736005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13745470900609523955824003 20618206350914285933736005)
                    ·
                      refine ⟨3865913690796428612575501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20618206350914285933736005 3865913690796428612575501)
                      ·
                        rfl

theorem cell23_7528840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7528840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528840 prefixEnd_7528840 := by exact prefixLift 7528840
  have htrace : WordTrace (prefixWord ++ tailWord_7528840) baseStart_7528840 baseEnd_7528840 := by
    simpa [prefixWord, tailWord_7528840, baseEnd_7528840] using wordTrace_append hprefix tailTrace_7528840
  have hstable : (prefixWord ++ tailWord_7528840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528840).length < 2 ^ (prefixWord ++ tailWord_7528840).sum := by decide
  have hdescent : baseEnd_7528840 < baseStart_7528840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528857 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 1, 1, 4]
def baseStart_7528857 : Nat := 118140960795 + 7528857 * 2 ^ 59
def prefixEnd_7528857 : Nat := 4983230072969 + 3 ^ 40 * 7528857 * 2
def baseEnd_7528857 : Nat := 3865922419967555046062923

theorem tailTrace_7528857 : CollatzResearch.WordTrace tailWord_7528857 prefixEnd_7528857 3865922419967555046062923 := by
  unfold tailWord_7528857
  simp only [CollatzResearch.WordTrace]
  refine ⟨274599974085244390250840825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183066649390162926833893883 274599974085244390250840825)
  ·
    refine ⟨205949980563933292688130619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274599974085244390250840825 205949980563933292688130619)
    ·
      refine ⟨308924970845899939032195929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205949980563933292688130619 308924970845899939032195929)
      ·
        refine ⟨231693728134424954274146947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308924970845899939032195929 231693728134424954274146947)
        ·
          refine ⟨347540592201637431411220421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231693728134424954274146947 347540592201637431411220421)
          ·
            refine ⟨65163861037807018389603829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347540592201637431411220421 65163861037807018389603829)
            ·
              refine ⟨6109111972294407974025359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65163861037807018389603829 6109111972294407974025359)
              ·
                refine ⟨9163667958441611961038039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109111972294407974025359 9163667958441611961038039)
                ·
                  refine ⟨13745501937662417941557059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9163667958441611961038039 13745501937662417941557059)
                  ·
                    refine ⟨20618252906493626912335589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13745501937662417941557059 20618252906493626912335589)
                    ·
                      refine ⟨3865922419967555046062923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20618252906493626912335589 3865922419967555046062923)
                      ·
                        rfl

theorem cell23_7528857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_7528857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528857 prefixEnd_7528857 := by exact prefixLift 7528857
  have htrace : WordTrace (prefixWord ++ tailWord_7528857) baseStart_7528857 baseEnd_7528857 := by
    simpa [prefixWord, tailWord_7528857, baseEnd_7528857] using wordTrace_append hprefix tailTrace_7528857
  have hstable : (prefixWord ++ tailWord_7528857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528857).length < 2 ^ (prefixWord ++ tailWord_7528857).sum := by decide
  have hdescent : baseEnd_7528857 < baseStart_7528857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528867 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 2, 4]
def baseStart_7528867 : Nat := 118140960795 + 7528867 * 2 ^ 59
def prefixEnd_7528867 : Nat := 4983230072969 + 3 ^ 40 * 7528867 * 2
def baseEnd_7528867 : Nat := 1288642518258033335645959

theorem tailTrace_7528867 : CollatzResearch.WordTrace tailWord_7528867 prefixEnd_7528867 1288642518258033335645959 := by
  unfold tailWord_7528867
  simp only [CollatzResearch.WordTrace]
  refine ⟨274600338815208161958704855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183066892543472107972469903 274600338815208161958704855)
  ·
    refine ⟨411900508222812242938057283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274600338815208161958704855 411900508222812242938057283)
    ·
      refine ⟨617850762334218364407085925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411900508222812242938057283 617850762334218364407085925)
      ·
        refine ⟨115847017937665943326328611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617850762334218364407085925 115847017937665943326328611)
        ·
          refine ⟨173770526906498914989492917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115847017937665943326328611 173770526906498914989492917)
          ·
            refine ⟨16290986897484273280264961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173770526906498914989492917 16290986897484273280264961)
            ·
              refine ⟨12218240173113204960198721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16290986897484273280264961 12218240173113204960198721)
              ·
                refine ⟨9163680129834903720149041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12218240173113204960198721 9163680129834903720149041)
                ·
                  refine ⟨6872760097376177790111781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9163680129834903720149041 6872760097376177790111781)
                  ·
                    refine ⟨1288642518258033335645959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872760097376177790111781 1288642518258033335645959)
                    ·
                      rfl

theorem cell23_7528867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 4].length) (baseStart_7528867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528867 prefixEnd_7528867 := by exact prefixLift 7528867
  have htrace : WordTrace (prefixWord ++ tailWord_7528867) baseStart_7528867 baseEnd_7528867 := by
    simpa [prefixWord, tailWord_7528867, baseEnd_7528867] using wordTrace_append hprefix tailTrace_7528867
  have hstable : (prefixWord ++ tailWord_7528867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528867).length < 2 ^ (prefixWord ++ tailWord_7528867).sum := by decide
  have hdescent : baseEnd_7528867 < baseStart_7528867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528908 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7528908 : Nat := 118140960795 + 7528908 * 2 ^ 59
def prefixEnd_7528908 : Nat := 4983230072969 + 3 ^ 40 * 7528908 * 2
def baseEnd_7528908 : Nat := 3865948607480934346525189

theorem tailTrace_7528908 : CollatzResearch.WordTrace tailWord_7528908 prefixEnd_7528908 3865948607480934346525189 := by
  unfold tailWord_7528908
  simp only [CollatzResearch.WordTrace]
  refine ⟨137300917104029812980473689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183067889472039750640631585 137300917104029812980473689)
  ·
    refine ⟨102975687828022359735355267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137300917104029812980473689 102975687828022359735355267)
    ·
      refine ⟨154463531742033539603032901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102975687828022359735355267 154463531742033539603032901)
      ·
        refine ⟨28961912201631288675568669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154463531742033539603032901 28961912201631288675568669)
        ·
          refine ⟨10860717075611733253338251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28961912201631288675568669 10860717075611733253338251)
          ·
            refine ⟨16291075613417599880007377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860717075611733253338251 16291075613417599880007377)
            ·
              refine ⟨12218306710063199910005533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16291075613417599880007377 12218306710063199910005533)
              ·
                refine ⟨4581865016273699966252075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218306710063199910005533 4581865016273699966252075)
                ·
                  refine ⟨6872797524410549949378113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581865016273699966252075 6872797524410549949378113)
                  ·
                    refine ⟨5154598143307912462033585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872797524410549949378113 5154598143307912462033585)
                    ·
                      refine ⟨3865948607480934346525189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154598143307912462033585 3865948607480934346525189)
                      ·
                        rfl

theorem cell23_7528908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7528908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528908 prefixEnd_7528908 := by exact prefixLift 7528908
  have htrace : WordTrace (prefixWord ++ tailWord_7528908) baseStart_7528908 baseEnd_7528908 := by
    simpa [prefixWord, tailWord_7528908, baseEnd_7528908] using wordTrace_append hprefix tailTrace_7528908
  have hstable : (prefixWord ++ tailWord_7528908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528908).length < 2 ^ (prefixWord ++ tailWord_7528908).sum := by decide
  have hdescent : baseEnd_7528908 < baseStart_7528908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528967 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_7528967 : Nat := 118140960795 + 7528967 * 2 ^ 59
def prefixEnd_7528967 : Nat := 4983230072969 + 3 ^ 40 * 7528967 * 2
def baseEnd_7528967 : Nat := 3865978902839549615687417

theorem tailTrace_7528967 : CollatzResearch.WordTrace tailWord_7528967 prefixEnd_7528967 3865978902839549615687417 := by
  unfold tailWord_7528967
  simp only [CollatzResearch.WordTrace]
  refine ⟨274603986114845879037345155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183069324076563919358230103 274603986114845879037345155)
  ·
    refine ⟨411905979172268818556017733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274603986114845879037345155 411905979172268818556017733)
    ·
      refine ⟨77232371094800403479253325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411905979172268818556017733 77232371094800403479253325)
      ·
        refine ⟨28962139160550151304719997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77232371094800403479253325 28962139160550151304719997)
        ·
          refine ⟨10860802185206306739269999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28962139160550151304719997 10860802185206306739269999)
          ·
            refine ⟨16291203277809460108904999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860802185206306739269999 16291203277809460108904999)
            ·
              refine ⟨24436804916714190163357499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16291203277809460108904999 24436804916714190163357499)
              ·
                refine ⟨36655207375071285245036249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24436804916714190163357499 36655207375071285245036249)
                ·
                  refine ⟨27491405531303463933777187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36655207375071285245036249 27491405531303463933777187)
                  ·
                    refine ⟨41237108296955195900665781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27491405531303463933777187 41237108296955195900665781)
                    ·
                      refine ⟨3865978902839549615687417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41237108296955195900665781 3865978902839549615687417)
                      ·
                        rfl

theorem cell23_7528967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_7528967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7528967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7528967 prefixEnd_7528967 := by exact prefixLift 7528967
  have htrace : WordTrace (prefixWord ++ tailWord_7528967) baseStart_7528967 baseEnd_7528967 := by
    simpa [prefixWord, tailWord_7528967, baseEnd_7528967] using wordTrace_append hprefix tailTrace_7528967
  have hstable : (prefixWord ++ tailWord_7528967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528967).length < 2 ^ (prefixWord ++ tailWord_7528967).sum := by decide
  have hdescent : baseEnd_7528967 < baseStart_7528967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529017 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_7529017 : Nat := 118140960795 + 7529017 * 2 ^ 59
def prefixEnd_7529017 : Nat := 4983230072969 + 3 ^ 40 * 7529017 * 2
def baseEnd_7529017 : Nat := 1288668192290758140020729

theorem tailTrace_7529017 : CollatzResearch.WordTrace tailWord_7529017 prefixEnd_7529017 1288668192290758140020729 := by
  unfold tailWord_7529017
  simp only [CollatzResearch.WordTrace]
  refine ⟨274605809764664737576665305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183070539843109825051110203 274605809764664737576665305)
  ·
    refine ⟨205954357323498553182498979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274605809764664737576665305 205954357323498553182498979)
    ·
      refine ⟨308931535985247829773748469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205954357323498553182498979 308931535985247829773748469)
      ·
        refine ⟨28962331498616984041288919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308931535985247829773748469 28962331498616984041288919)
        ·
          refine ⟨43443497247925476061933379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28962331498616984041288919 43443497247925476061933379)
          ·
            refine ⟨65165245871888214092900069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43443497247925476061933379 65165245871888214092900069)
            ·
              refine ⟨12218483600979040142418763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65165245871888214092900069 12218483600979040142418763)
              ·
                refine ⟨18327725401468560213628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12218483600979040142418763 18327725401468560213628145)
                ·
                  refine ⟨13745794051101420160221109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18327725401468560213628145 13745794051101420160221109)
                  ·
                    refine ⟨1288668192290758140020729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13745794051101420160221109 1288668192290758140020729)
                    ·
                      rfl

theorem cell23_7529017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_7529017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529017 prefixEnd_7529017 := by exact prefixLift 7529017
  have htrace : WordTrace (prefixWord ++ tailWord_7529017) baseStart_7529017 baseEnd_7529017 := by
    simpa [prefixWord, tailWord_7529017, baseEnd_7529017] using wordTrace_append hprefix tailTrace_7529017
  have hstable : (prefixWord ++ tailWord_7529017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529017).length < 2 ^ (prefixWord ++ tailWord_7529017).sum := by decide
  have hdescent : baseEnd_7529017 < baseStart_7529017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529047 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 3, 4]
def baseStart_7529047 : Nat := 118140960795 + 7529047 * 2 ^ 59
def prefixEnd_7529047 : Nat := 4983230072969 + 3 ^ 40 * 7529047 * 2
def baseEnd_7529047 : Nat := 1288673327097303100895683

theorem tailTrace_7529047 : CollatzResearch.WordTrace tailWord_7529047 prefixEnd_7529047 1288673327097303100895683 := by
  unfold tailWord_7529047
  simp only [CollatzResearch.WordTrace]
  refine ⟨274606903954556052700257395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183071269303037368466838263 274606903954556052700257395)
  ·
    refine ⟨411910355931834079050386093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274606903954556052700257395 411910355931834079050386093)
    ·
      refine ⟨154466383474437779643894785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411910355931834079050386093 154466383474437779643894785)
      ·
        refine ⟨115849787605828334732921089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154466383474437779643894785 115849787605828334732921089)
        ·
          refine ⟨86887340704371251049690817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115849787605828334732921089 86887340704371251049690817)
          ·
            refine ⟨65165505528278438287268113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86887340704371251049690817 65165505528278438287268113)
            ·
              refine ⟨48874129146208828715451085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65165505528278438287268113 48874129146208828715451085)
              ·
                refine ⟨18327798429828310768294157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48874129146208828715451085 18327798429828310768294157)
                ·
                  refine ⟨6872924411185616538110309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18327798429828310768294157 6872924411185616538110309)
                  ·
                    refine ⟨1288673327097303100895683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872924411185616538110309 1288673327097303100895683)
                    ·
                      rfl

theorem cell23_7529047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_7529047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529047 prefixEnd_7529047 := by exact prefixLift 7529047
  have htrace : WordTrace (prefixWord ++ tailWord_7529047) baseStart_7529047 baseEnd_7529047 := by
    simpa [prefixWord, tailWord_7529047, baseEnd_7529047] using wordTrace_append hprefix tailTrace_7529047
  have hstable : (prefixWord ++ tailWord_7529047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529047).length < 2 ^ (prefixWord ++ tailWord_7529047).sum := by decide
  have hdescent : baseEnd_7529047 < baseStart_7529047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529050 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_7529050 : Nat := 118140960795 + 7529050 * 2 ^ 59
def prefixEnd_7529050 : Nat := 4983230072969 + 3 ^ 40 * 7529050 * 2
def baseEnd_7529050 : Nat := 3866021521733872790949535

theorem tailTrace_7529050 : CollatzResearch.WordTrace tailWord_7529050 prefixEnd_7529050 3866021521733872790949535 := by
  unfold tailWord_7529050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68651753343386296053154151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183071342249030122808411069 68651753343386296053154151)
  ·
    refine ⟨102977630015079444079731227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68651753343386296053154151 102977630015079444079731227)
    ·
      refine ⟨154466445022619166119596841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102977630015079444079731227 154466445022619166119596841)
      ·
        refine ⟨115849833766964374589697631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154466445022619166119596841 115849833766964374589697631)
        ·
          refine ⟨173774750650446561884546447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115849833766964374589697631 173774750650446561884546447)
          ·
            refine ⟨260662125975669842826819671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173774750650446561884546447 260662125975669842826819671)
            ·
              refine ⟨390993188963504764240229507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260662125975669842826819671 390993188963504764240229507)
              ·
                refine ⟨586489783445257146360344261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390993188963504764240229507 586489783445257146360344261)
                ·
                  refine ⟨109966834395985714942564549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 586489783445257146360344261 109966834395985714942564549)
                  ·
                    refine ⟨20618781449247321551730853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109966834395985714942564549 20618781449247321551730853)
                    ·
                      refine ⟨3866021521733872790949535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20618781449247321551730853 3866021521733872790949535)
                      ·
                        rfl

theorem cell23_7529050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_7529050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529050 prefixEnd_7529050 := by exact prefixLift 7529050
  have htrace : WordTrace (prefixWord ++ tailWord_7529050) baseStart_7529050 baseEnd_7529050 := by
    simpa [prefixWord, tailWord_7529050, baseEnd_7529050] using wordTrace_append hprefix tailTrace_7529050
  have hstable : (prefixWord ++ tailWord_7529050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529050).length < 2 ^ (prefixWord ++ tailWord_7529050).sum := by decide
  have hdescent : baseEnd_7529050 < baseStart_7529050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529074 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_7529074 : Nat := 118140960795 + 7529074 * 2 ^ 59
def prefixEnd_7529074 : Nat := 4983230072969 + 3 ^ 40 * 7529074 * 2
def baseEnd_7529074 : Nat := 3866033845269580697049425

theorem tailTrace_7529074 : CollatzResearch.WordTrace tailWord_7529074 prefixEnd_7529074 3866033845269580697049425 := by
  unfold tailWord_7529074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68651972181364559077872569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183071925816972157540993517 68651972181364559077872569)
  ·
    refine ⟨51488979136023419308404427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68651972181364559077872569 51488979136023419308404427)
    ·
      refine ⟨77233468704035128962606641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51488979136023419308404427 77233468704035128962606641)
      ·
        refine ⟨57925101528026346721954981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77233468704035128962606641 57925101528026346721954981)
        ·
          refine ⟨10860956536504940010366559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57925101528026346721954981 10860956536504940010366559)
          ·
            refine ⟨16291434804757410015549839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860956536504940010366559 16291434804757410015549839)
            ·
              refine ⟨24437152207136115023324759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16291434804757410015549839 24437152207136115023324759)
              ·
                refine ⟨36655728310704172534987139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24437152207136115023324759 36655728310704172534987139)
                ·
                  refine ⟨54983592466056258802480709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36655728310704172534987139 54983592466056258802480709)
                  ·
                    refine ⟨10309423587385548525465133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54983592466056258802480709 10309423587385548525465133)
                    ·
                      refine ⟨3866033845269580697049425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309423587385548525465133 3866033845269580697049425)
                      ·
                        rfl

theorem cell23_7529074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_7529074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529074 prefixEnd_7529074 := by exact prefixLift 7529074
  have htrace : WordTrace (prefixWord ++ tailWord_7529074) baseStart_7529074 baseEnd_7529074 := by
    simpa [prefixWord, tailWord_7529074, baseEnd_7529074] using wordTrace_append hprefix tailTrace_7529074
  have hstable : (prefixWord ++ tailWord_7529074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529074).length < 2 ^ (prefixWord ++ tailWord_7529074).sum := by decide
  have hdescent : baseEnd_7529074 < baseStart_7529074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529081 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 1, 4]
def baseStart_7529081 : Nat := 118140960795 + 7529081 * 2 ^ 59
def prefixEnd_7529081 : Nat := 4983230072969 + 3 ^ 40 * 7529081 * 2
def baseEnd_7529081 : Nat := 1288679146544720723220631

theorem tailTrace_7529081 : CollatzResearch.WordTrace tailWord_7529081 prefixEnd_7529081 1288679146544720723220631 := by
  unfold tailWord_7529081
  simp only [CollatzResearch.WordTrace]
  refine ⟨274608144036432876506995097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183072096024288584337996731 274608144036432876506995097)
  ·
    refine ⟨205956108027324657380246323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274608144036432876506995097 205956108027324657380246323)
    ·
      refine ⟨308934162040986986070369485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205956108027324657380246323 308934162040986986070369485)
      ·
        refine ⟨115850310765370119776388557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308934162040986986070369485 115850310765370119776388557)
        ·
          refine ⟨43443866537013794916145709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115850310765370119776388557 43443866537013794916145709)
          ·
            refine ⟨16291449951380173093554641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43443866537013794916145709 16291449951380173093554641)
            ·
              refine ⟨12218587463535129820165981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16291449951380173093554641 12218587463535129820165981)
              ·
                refine ⟨4581970298825673682562243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218587463535129820165981 4581970298825673682562243)
                ·
                  refine ⟨6872955448238510523843365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581970298825673682562243 6872955448238510523843365)
                  ·
                    refine ⟨1288679146544720723220631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872955448238510523843365 1288679146544720723220631)
                    ·
                      rfl

theorem cell23_7529081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 4].length) (baseStart_7529081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529081 prefixEnd_7529081 := by exact prefixLift 7529081
  have htrace : WordTrace (prefixWord ++ tailWord_7529081) baseStart_7529081 baseEnd_7529081 := by
    simpa [prefixWord, tailWord_7529081, baseEnd_7529081] using wordTrace_append hprefix tailTrace_7529081
  have hstable : (prefixWord ++ tailWord_7529081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529081).length < 2 ^ (prefixWord ++ tailWord_7529081).sum := by decide
  have hdescent : baseEnd_7529081 < baseStart_7529081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529100 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7529100 : Nat := 118140960795 + 7529100 * 2 ^ 59
def prefixEnd_7529100 : Nat := 4983230072969 + 3 ^ 40 * 7529100 * 2
def baseEnd_7529100 : Nat := 3866047195766597595324305

theorem tailTrace_7529100 : CollatzResearch.WordTrace tailWord_7529100 prefixEnd_7529100 3866047195766597595324305 := by
  unfold tailWord_7529100
  simp only [CollatzResearch.WordTrace]
  refine ⟨137304418511682021375968377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183072558015576028501291169 137304418511682021375968377)
  ·
    refine ⟨102978313883761516031976283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137304418511682021375968377 102978313883761516031976283)
    ·
      refine ⟨154467470825642274047964425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102978313883761516031976283 154467470825642274047964425)
      ·
        refine ⟨115850603119231705535973319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154467470825642274047964425 115850603119231705535973319)
        ·
          refine ⟨173775904678847558303959979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115850603119231705535973319 173775904678847558303959979)
          ·
            refine ⟨260663857018271337455939969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173775904678847558303959979 260663857018271337455939969)
            ·
              refine ⟨195497892763703503091954977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260663857018271337455939969 195497892763703503091954977)
              ·
                refine ⟨146623419572777627318966233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195497892763703503091954977 146623419572777627318966233)
                ·
                  refine ⟨109967564679583220489224675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146623419572777627318966233 109967564679583220489224675)
                  ·
                    refine ⟨164951347019374830733837013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109967564679583220489224675 164951347019374830733837013)
                    ·
                      refine ⟨3866047195766597595324305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164951347019374830733837013 3866047195766597595324305)
                      ·
                        rfl

theorem cell23_7529100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7529100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529100 prefixEnd_7529100 := by exact prefixLift 7529100
  have htrace : WordTrace (prefixWord ++ tailWord_7529100) baseStart_7529100 baseEnd_7529100 := by
    simpa [prefixWord, tailWord_7529100, baseEnd_7529100] using wordTrace_append hprefix tailTrace_7529100
  have hstable : (prefixWord ++ tailWord_7529100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529100).length < 2 ^ (prefixWord ++ tailWord_7529100).sum := by decide
  have hdescent : baseEnd_7529100 < baseStart_7529100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529124 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_7529124 : Nat := 118140960795 + 7529124 * 2 ^ 59
def prefixEnd_7529124 : Nat := 4983230072969 + 3 ^ 40 * 7529124 * 2
def baseEnd_7529124 : Nat := 1288686506434101833808065

theorem tailTrace_7529124 : CollatzResearch.WordTrace tailWord_7529124 prefixEnd_7529124 1288686506434101833808065 := by
  unfold tailWord_7529124
  simp only [CollatzResearch.WordTrace]
  refine ⟨137304856187638547425405213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183073141583518063233873617 137304856187638547425405213)
  ·
    refine ⟨51489321070364455284526955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137304856187638547425405213 51489321070364455284526955)
    ·
      refine ⟨77233981605546682926790433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51489321070364455284526955 77233981605546682926790433)
      ·
        refine ⟨57925486204160012195092825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77233981605546682926790433 57925486204160012195092825)
        ·
          refine ⟨43444114653120009146319619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57925486204160012195092825 43444114653120009146319619)
          ·
            refine ⟨65166171979680013719479429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43444114653120009146319619 65166171979680013719479429)
            ·
              refine ⟨12218657246190002572402393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65166171979680013719479429 12218657246190002572402393)
              ·
                refine ⟨9163992934642501929301795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12218657246190002572402393 9163992934642501929301795)
                ·
                  refine ⟨13745989401963752893952693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9163992934642501929301795 13745989401963752893952693)
                  ·
                    refine ⟨1288686506434101833808065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13745989401963752893952693 1288686506434101833808065)
                    ·
                      rfl

theorem cell23_7529124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_7529124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529124 prefixEnd_7529124 := by exact prefixLift 7529124
  have htrace : WordTrace (prefixWord ++ tailWord_7529124) baseStart_7529124 baseEnd_7529124 := by
    simpa [prefixWord, tailWord_7529124, baseEnd_7529124] using wordTrace_append hprefix tailTrace_7529124
  have hstable : (prefixWord ++ tailWord_7529124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529124).length < 2 ^ (prefixWord ++ tailWord_7529124).sum := by decide
  have hdescent : baseEnd_7529124 < baseStart_7529124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529147 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3]
def baseStart_7529147 : Nat := 118140960795 + 7529147 * 2 ^ 59
def prefixEnd_7529147 : Nat := 4983230072969 + 3 ^ 40 * 7529147 * 2
def baseEnd_7529147 : Nat := 3866071329357358911436589

theorem tailTrace_7529147 : CollatzResearch.WordTrace tailWord_7529147 prefixEnd_7529147 3866071329357358911436589 := by
  unfold tailWord_7529147
  simp only [CollatzResearch.WordTrace]
  refine ⟨274610551254193769778897695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183073700836129179852598463 274610551254193769778897695)
  ·
    refine ⟨411915826881290654668346543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274610551254193769778897695 411915826881290654668346543)
    ·
      refine ⟨617873740321935982002519815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411915826881290654668346543 617873740321935982002519815)
      ·
        refine ⟨926810610482903973003779723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617873740321935982002519815 926810610482903973003779723)
        ·
          refine ⟨1390215915724355959505669585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926810610482903973003779723 1390215915724355959505669585)
          ·
            refine ⟨1042661936793266969629252189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1390215915724355959505669585 1042661936793266969629252189)
            ·
              refine ⟨390998226297475113610969571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1042661936793266969629252189 390998226297475113610969571)
              ·
                refine ⟨586497339446212670416454357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390998226297475113610969571 586497339446212670416454357)
                ·
                  refine ⟨13746031393270609462885649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 586497339446212670416454357 13746031393270609462885649)
                  ·
                    refine ⟨10309523544952957097164237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746031393270609462885649 10309523544952957097164237)
                    ·
                      refine ⟨3866071329357358911436589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309523544952957097164237 3866071329357358911436589)
                      ·
                        rfl

theorem cell23_7529147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3].length) (baseStart_7529147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529147 prefixEnd_7529147 := by exact prefixLift 7529147
  have htrace : WordTrace (prefixWord ++ tailWord_7529147) baseStart_7529147 baseEnd_7529147 := by
    simpa [prefixWord, tailWord_7529147, baseEnd_7529147] using wordTrace_append hprefix tailTrace_7529147
  have hstable : (prefixWord ++ tailWord_7529147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529147).length < 2 ^ (prefixWord ++ tailWord_7529147).sum := by decide
  have hdescent : baseEnd_7529147 < baseStart_7529147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529164 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7529164 : Nat := 118140960795 + 7529164 * 2 ^ 59
def prefixEnd_7529164 : Nat := 4983230072969 + 3 ^ 40 * 7529164 * 2
def baseEnd_7529164 : Nat := 3866080058528485344924011

theorem tailTrace_7529164 : CollatzResearch.WordTrace tailWord_7529164 prefixEnd_7529164 3866080058528485344924011 := by
  unfold tailWord_7529164
  simp only [CollatzResearch.WordTrace]
  refine ⟨137305585647566090841133273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183074114196754787788177697 137305585647566090841133273)
  ·
    refine ⟨102979189235674568130849955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137305585647566090841133273 102979189235674568130849955)
    ·
      refine ⟨154468783853511852196274933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102979189235674568130849955 154468783853511852196274933)
      ·
        refine ⟨14481448486266736143400775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154468783853511852196274933 14481448486266736143400775)
        ·
          refine ⟨21722172729400104215101163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481448486266736143400775 21722172729400104215101163)
          ·
            refine ⟨32583259094100156322651745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722172729400104215101163 32583259094100156322651745)
            ·
              refine ⟨24437444320575117241988809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32583259094100156322651745 24437444320575117241988809)
              ·
                refine ⟨18328083240431337931491607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24437444320575117241988809 18328083240431337931491607)
                ·
                  refine ⟨27492124860647006897237411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18328083240431337931491607 27492124860647006897237411)
                  ·
                    refine ⟨41238187290970510345856117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27492124860647006897237411 41238187290970510345856117)
                    ·
                      refine ⟨3866080058528485344924011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41238187290970510345856117 3866080058528485344924011)
                      ·
                        rfl

theorem cell23_7529164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7529164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529164 prefixEnd_7529164 := by exact prefixLift 7529164
  have htrace : WordTrace (prefixWord ++ tailWord_7529164) baseStart_7529164 baseEnd_7529164 := by
    simpa [prefixWord, tailWord_7529164, baseEnd_7529164] using wordTrace_append hprefix tailTrace_7529164
  have hstable : (prefixWord ++ tailWord_7529164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529164).length < 2 ^ (prefixWord ++ tailWord_7529164).sum := by decide
  have hdescent : baseEnd_7529164 < baseStart_7529164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529198 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_7529198 : Nat := 118140960795 + 7529198 * 2 ^ 59
def prefixEnd_7529198 : Nat := 4983230072969 + 3 ^ 40 * 7529198 * 2
def baseEnd_7529198 : Nat := 3866097516870738211898855

theorem tailTrace_7529198 : CollatzResearch.WordTrace tailWord_7529198 prefixEnd_7529198 3866097516870738211898855 := by
  unfold tailWord_7529198
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326551422126125686125531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183074940918006003659336165 34326551422126125686125531)
  ·
    refine ⟨51489827133189188529188297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34326551422126125686125531 51489827133189188529188297)
    ·
      refine ⟨38617370349891891396891223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51489827133189188529188297 38617370349891891396891223)
      ·
        refine ⟨57926055524837837095336835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38617370349891891396891223 57926055524837837095336835)
        ·
          refine ⟨86889083287256755643005253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57926055524837837095336835 86889083287256755643005253)
          ·
            refine ⟨16291703116360641683063485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86889083287256755643005253 16291703116360641683063485)
            ·
              refine ⟨6109388668635240631148807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16291703116360641683063485 6109388668635240631148807)
              ·
                refine ⟨9164083002952860946723211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109388668635240631148807 9164083002952860946723211)
                ·
                  refine ⟨13746124504429291420084817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164083002952860946723211 13746124504429291420084817)
                  ·
                    refine ⟨10309593378321968565063613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746124504429291420084817 10309593378321968565063613)
                    ·
                      refine ⟨3866097516870738211898855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309593378321968565063613 3866097516870738211898855)
                      ·
                        rfl

theorem cell23_7529198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_7529198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529198 prefixEnd_7529198 := by exact prefixLift 7529198
  have htrace : WordTrace (prefixWord ++ tailWord_7529198) baseStart_7529198 baseEnd_7529198 := by
    simpa [prefixWord, tailWord_7529198, baseEnd_7529198] using wordTrace_append hprefix tailTrace_7529198
  have hstable : (prefixWord ++ tailWord_7529198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529198).length < 2 ^ (prefixWord ++ tailWord_7529198).sum := by decide
  have hdescent : baseEnd_7529198 < baseStart_7529198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529212 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_7529212 : Nat := 118140960795 + 7529212 * 2 ^ 59
def prefixEnd_7529212 : Nat := 4983230072969 + 3 ^ 40 * 7529212 * 2
def baseEnd_7529212 : Nat := 3866104705599901157123791

theorem tailTrace_7529212 : CollatzResearch.WordTrace tailWord_7529212 prefixEnd_7529212 3866104705599901157123791 := by
  unfold tailWord_7529212
  simp only [CollatzResearch.WordTrace]
  refine ⟨137306460999479142940006945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183075281332638857253342593 137306460999479142940006945)
  ·
    refine ⟨102979845749609357205005209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137306460999479142940006945 102979845749609357205005209)
    ·
      refine ⟨77234884312207017903753907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102979845749609357205005209 77234884312207017903753907)
      ·
        refine ⟨115852326468310526855630861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77234884312207017903753907 115852326468310526855630861)
        ·
          refine ⟨43444622425616447570861573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115852326468310526855630861 43444622425616447570861573)
          ·
            refine ⟨8145866704803083919536545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43444622425616447570861573 8145866704803083919536545)
            ·
              refine ⟨6109400028602312939652409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145866704803083919536545 6109400028602312939652409)
              ·
                refine ⟨4582050021451734704739307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109400028602312939652409 4582050021451734704739307)
                ·
                  refine ⟨6873075032177602057108961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582050021451734704739307 6873075032177602057108961)
                  ·
                    refine ⟨5154806274133201542831721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873075032177602057108961 5154806274133201542831721)
                    ·
                      refine ⟨3866104705599901157123791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154806274133201542831721 3866104705599901157123791)
                      ·
                        rfl

theorem cell23_7529212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_7529212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529212 prefixEnd_7529212 := by exact prefixLift 7529212
  have htrace : WordTrace (prefixWord ++ tailWord_7529212) baseStart_7529212 baseEnd_7529212 := by
    simpa [prefixWord, tailWord_7529212, baseEnd_7529212] using wordTrace_append hprefix tailTrace_7529212
  have hstable : (prefixWord ++ tailWord_7529212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529212).length < 2 ^ (prefixWord ++ tailWord_7529212).sum := by decide
  have hdescent : baseEnd_7529212 < baseStart_7529212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529214 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7529214 : Nat := 118140960795 + 7529214 * 2 ^ 59
def prefixEnd_7529214 : Nat := 4983230072969 + 3 ^ 40 * 7529214 * 2
def baseEnd_7529214 : Nat := 1288701910853736716432927

theorem tailTrace_7529214 : CollatzResearch.WordTrace tailWord_7529214 prefixEnd_7529214 1288701910853736716432927 := by
  unfold tailWord_7529214
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326624368118880027698337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183075329963300693481057797 34326624368118880027698337)
  ·
    refine ⟨25744968276089160020773753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34326624368118880027698337 25744968276089160020773753)
    ·
      refine ⟨19308726207066870015580315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25744968276089160020773753 19308726207066870015580315)
      ·
        refine ⟨28963089310600305023370473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19308726207066870015580315 28963089310600305023370473)
        ·
          refine ⟨21722316982950228767527855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28963089310600305023370473 21722316982950228767527855)
          ·
            refine ⟨32583475474425343151291783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722316982950228767527855 32583475474425343151291783)
            ·
              refine ⟨48875213211638014726937675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32583475474425343151291783 48875213211638014726937675)
              ·
                refine ⟨73312819817457022090406513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48875213211638014726937675 73312819817457022090406513)
                ·
                  refine ⟨54984614863092766567804885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73312819817457022090406513 54984614863092766567804885)
                  ·
                    refine ⟨1288701910853736716432927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54984614863092766567804885 1288701910853736716432927)
                    ·
                      rfl

theorem cell23_7529214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7529214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529214 prefixEnd_7529214 := by exact prefixLift 7529214
  have htrace : WordTrace (prefixWord ++ tailWord_7529214) baseStart_7529214 baseEnd_7529214 := by
    simpa [prefixWord, tailWord_7529214, baseEnd_7529214] using wordTrace_append hprefix tailTrace_7529214
  have hstable : (prefixWord ++ tailWord_7529214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529214).length < 2 ^ (prefixWord ++ tailWord_7529214).sum := by decide
  have hdescent : baseEnd_7529214 < baseStart_7529214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529251 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 4, 2, 2]
def baseStart_7529251 : Nat := 118140960795 + 7529251 * 2 ^ 59
def prefixEnd_7529251 : Nat := 4983230072969 + 3 ^ 40 * 7529251 * 2
def baseEnd_7529251 : Nat := 3866124731345426504536111

theorem tailTrace_7529251 : CollatzResearch.WordTrace tailWord_7529251 prefixEnd_7529251 3866124731345426504536111 := by
  unfold tailWord_7529251
  simp only [CollatzResearch.WordTrace]
  refine ⟨274614344445816995540683607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183076229630544663693789071 274614344445816995540683607)
  ·
    refine ⟨411921516668725493311025411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274614344445816995540683607 411921516668725493311025411)
    ·
      refine ⟨617882275003088239966538117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411921516668725493311025411 617882275003088239966538117)
      ·
        refine ⟨115852926563079044993725897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617882275003088239966538117 115852926563079044993725897)
        ·
          refine ⟨86889694922309283745294423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115852926563079044993725897 86889694922309283745294423)
          ·
            refine ⟨130334542383463925617941635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86889694922309283745294423 130334542383463925617941635)
            ·
              refine ⟨195501813575195888426912453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130334542383463925617941635 195501813575195888426912453)
              ·
                refine ⟨36656590045349229080046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195501813575195888426912453 36656590045349229080046085)
                ·
                  refine ⟨6873110633502980452508641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36656590045349229080046085 6873110633502980452508641)
                  ·
                    refine ⟨5154832975127235339381481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873110633502980452508641 5154832975127235339381481)
                    ·
                      refine ⟨3866124731345426504536111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154832975127235339381481 3866124731345426504536111)
                      ·
                        rfl

theorem cell23_7529251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_7529251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529251 prefixEnd_7529251 := by exact prefixLift 7529251
  have htrace : WordTrace (prefixWord ++ tailWord_7529251) baseStart_7529251 baseEnd_7529251 := by
    simpa [prefixWord, tailWord_7529251, baseEnd_7529251] using wordTrace_append hprefix tailTrace_7529251
  have hstable : (prefixWord ++ tailWord_7529251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529251).length < 2 ^ (prefixWord ++ tailWord_7529251).sum := by decide
  have hdescent : baseEnd_7529251 < baseStart_7529251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529308 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 5]
def baseStart_7529308 : Nat := 118140960795 + 7529308 * 2 ^ 59
def prefixEnd_7529308 : Nat := 4983230072969 + 3 ^ 40 * 7529308 * 2
def baseEnd_7529308 : Nat := 429572666638081420169261

theorem tailTrace_7529308 : CollatzResearch.WordTrace tailWord_7529308 prefixEnd_7529308 429572666638081420169261 := by
  unfold tailWord_7529308
  simp only [CollatzResearch.WordTrace]
  refine ⟨137308211703305247137754289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183077615604406996183672385 137308211703305247137754289)
  ·
    refine ⟨102981158777478935353315717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137308211703305247137754289 102981158777478935353315717)
    ·
      refine ⟨19308967270777300378746697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102981158777478935353315717 19308967270777300378746697)
      ·
        refine ⟨14481725453082975284060023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19308967270777300378746697 14481725453082975284060023)
        ·
          refine ⟨21722588179624462926090035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481725453082975284060023 21722588179624462926090035)
          ·
            refine ⟨32583882269436694389135053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722588179624462926090035 32583882269436694389135053)
            ·
              refine ⟨12218955851038760395925645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32583882269436694389135053 12218955851038760395925645)
              ·
                refine ⟨4582108444139535148472117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218955851038760395925645 4582108444139535148472117)
                ·
                  refine ⟨429572666638081420169261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582108444139535148472117 429572666638081420169261)
                  ·
                    rfl

theorem cell23_7529308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_7529308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529308 prefixEnd_7529308 := by exact prefixLift 7529308
  have htrace : WordTrace (prefixWord ++ tailWord_7529308) baseStart_7529308 baseEnd_7529308 := by
    simpa [prefixWord, tailWord_7529308, baseEnd_7529308] using wordTrace_append hprefix tailTrace_7529308
  have hstable : (prefixWord ++ tailWord_7529308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529308).length < 2 ^ (prefixWord ++ tailWord_7529308).sum := by decide
  have hdescent : baseEnd_7529308 < baseStart_7529308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529341 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_7529341 : Nat := 118140960795 + 7529341 * 2 ^ 59
def prefixEnd_7529341 : Nat := 4983230072969 + 3 ^ 40 * 7529341 * 2
def baseEnd_7529341 : Nat := 3866170944604331152410697

theorem tailTrace_7529341 : CollatzResearch.WordTrace tailWord_7529341 prefixEnd_7529341 3866170944604331152410697 := by
  unfold tailWord_7529341
  simp only [CollatzResearch.WordTrace]
  refine ⟨274617627015490940911459877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183078418010327293940973251 274617627015490940911459877)
  ·
    refine ⟨51490805065404551420898727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274617627015490940911459877 51490805065404551420898727)
    ·
      refine ⟨77236207598106827131348091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51490805065404551420898727 77236207598106827131348091)
      ·
        refine ⟨115854311397160240697022137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77236207598106827131348091 115854311397160240697022137)
        ·
          refine ⟨86890733547870180522766603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115854311397160240697022137 86890733547870180522766603)
          ·
            refine ⟨130336100321805270784149905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86890733547870180522766603 130336100321805270784149905)
            ·
              refine ⟨97752075241353953088112429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130336100321805270784149905 97752075241353953088112429)
              ·
                refine ⟨36657028215507732408042161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97752075241353953088112429 36657028215507732408042161)
                ·
                  refine ⟨27492771161630799306031621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36657028215507732408042161 27492771161630799306031621)
                  ·
                    refine ⟨5154894592805774869880929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27492771161630799306031621 5154894592805774869880929)
                    ·
                      refine ⟨3866170944604331152410697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5154894592805774869880929 3866170944604331152410697)
                      ·
                        rfl

theorem cell23_7529341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_7529341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529341 prefixEnd_7529341 := by exact prefixLift 7529341
  have htrace : WordTrace (prefixWord ++ tailWord_7529341) baseStart_7529341 baseEnd_7529341 := by
    simpa [prefixWord, tailWord_7529341, baseEnd_7529341] using wordTrace_append hprefix tailTrace_7529341
  have hstable : (prefixWord ++ tailWord_7529341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529341).length < 2 ^ (prefixWord ++ tailWord_7529341).sum := by decide
  have hdescent : baseEnd_7529341 < baseStart_7529341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529344 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_7529344 : Nat := 118140960795 + 7529344 * 2 ^ 59
def prefixEnd_7529344 : Nat := 4983230072969 + 3 ^ 40 * 7529344 * 2
def baseEnd_7529344 : Nat := 3866172485046294640673183

theorem tailTrace_7529344 : CollatzResearch.WordTrace tailWord_7529344 prefixEnd_7529344 3866172485046294640673183 := by
  unfold tailWord_7529344
  simp only [CollatzResearch.WordTrace]
  refine ⟨137308868217240036211909543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183078490956320048282546057 137308868217240036211909543)
  ·
    refine ⟨205963302325860054317864315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137308868217240036211909543 205963302325860054317864315)
    ·
      refine ⟨308944953488790081476796473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205963302325860054317864315 308944953488790081476796473)
      ·
        refine ⟨231708715116592561107597355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308944953488790081476796473 231708715116592561107597355)
        ·
          refine ⟨347563072674888841661396033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231708715116592561107597355 347563072674888841661396033)
          ·
            refine ⟨260672304506166631246047025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347563072674888841661396033 260672304506166631246047025)
            ·
              refine ⟨195504228379624973434535269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260672304506166631246047025 195504228379624973434535269)
              ·
                refine ⟨36657042821179682518975363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195504228379624973434535269 36657042821179682518975363)
                ·
                  refine ⟨54985564231769523778463045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36657042821179682518975363 54985564231769523778463045)
                  ·
                    refine ⟨10309793293456785708461821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54985564231769523778463045 10309793293456785708461821)
                    ·
                      refine ⟨3866172485046294640673183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309793293456785708461821 3866172485046294640673183)
                      ·
                        rfl

theorem cell23_7529344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_7529344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529344 prefixEnd_7529344 := by exact prefixLift 7529344
  have htrace : WordTrace (prefixWord ++ tailWord_7529344) baseStart_7529344 baseEnd_7529344 := by
    simpa [prefixWord, tailWord_7529344, baseEnd_7529344] using wordTrace_append hprefix tailTrace_7529344
  have hstable : (prefixWord ++ tailWord_7529344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529344).length < 2 ^ (prefixWord ++ tailWord_7529344).sum := by decide
  have hdescent : baseEnd_7529344 < baseStart_7529344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529378 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_7529378 : Nat := 118140960795 + 7529378 * 2 ^ 59
def prefixEnd_7529378 : Nat := 4983230072969 + 3 ^ 40 * 7529378 * 2
def baseEnd_7529378 : Nat := 3866189943388547507648027

theorem tailTrace_7529378 : CollatzResearch.WordTrace tailWord_7529378 prefixEnd_7529378 3866189943388547507648027 := by
  unfold tailWord_7529378
  simp only [CollatzResearch.WordTrace]
  refine ⟨68654744129089224057639197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183079317677571264153704525 68654744129089224057639197)
  ·
    refine ⟨25745529048408459021614699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68654744129089224057639197 25745529048408459021614699)
    ·
      refine ⟨38618293572612688532422049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25745529048408459021614699 38618293572612688532422049)
      ·
        refine ⟨28963720179459516399316537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38618293572612688532422049 28963720179459516399316537)
        ·
          refine ⟨21722790134594637299487403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28963720179459516399316537 21722790134594637299487403)
          ·
            refine ⟨32584185201891955949231105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722790134594637299487403 32584185201891955949231105)
            ·
              refine ⟨24438138901418966961923329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32584185201891955949231105 24438138901418966961923329)
              ·
                refine ⟨18328604176064225221442497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24438138901418966961923329 18328604176064225221442497)
                ·
                  refine ⟨13746453132048168916081873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18328604176064225221442497 13746453132048168916081873)
                  ·
                    refine ⟨10309839849036126687061405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746453132048168916081873 10309839849036126687061405)
                    ·
                      refine ⟨3866189943388547507648027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309839849036126687061405 3866189943388547507648027)
                      ·
                        rfl

theorem cell23_7529378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_7529378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529378 prefixEnd_7529378 := by exact prefixLift 7529378
  have htrace : WordTrace (prefixWord ++ tailWord_7529378) baseStart_7529378 baseEnd_7529378 := by
    simpa [prefixWord, tailWord_7529378, baseEnd_7529378] using wordTrace_append hprefix tailTrace_7529378
  have hstable : (prefixWord ++ tailWord_7529378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529378).length < 2 ^ (prefixWord ++ tailWord_7529378).sum := by decide
  have hdescent : baseEnd_7529378 < baseStart_7529378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529408 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3]
def baseStart_7529408 : Nat := 118140960795 + 7529408 * 2 ^ 59
def prefixEnd_7529408 : Nat := 4983230072969 + 3 ^ 40 * 7529408 * 2
def baseEnd_7529408 : Nat := 3866205347808182390272889

theorem tailTrace_7529408 : CollatzResearch.WordTrace tailWord_7529408 prefixEnd_7529408 3866205347808182390272889 := by
  unfold tailWord_7529408
  simp only [CollatzResearch.WordTrace]
  refine ⟨137310035353124105677074439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183080047137498807569432585 137310035353124105677074439)
  ·
    refine ⟨205965053029686158515611659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137310035353124105677074439 205965053029686158515611659)
    ·
      refine ⟨308947579544529237773417489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205965053029686158515611659 308947579544529237773417489)
      ·
        refine ⟨231710684658396928330063117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308947579544529237773417489 231710684658396928330063117)
        ·
          refine ⟨86891506746898848123773669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231710684658396928330063117 86891506746898848123773669)
          ·
            refine ⟨16292157515043534023207563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86891506746898848123773669 16292157515043534023207563)
            ·
              refine ⟨24438236272565301034811345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292157515043534023207563 24438236272565301034811345)
              ·
                refine ⟨18328677204423975776108509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24438236272565301034811345 18328677204423975776108509)
                ·
                  refine ⟨6873253951658990916040691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18328677204423975776108509 6873253951658990916040691)
                  ·
                    refine ⟨10309880927488486374061037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873253951658990916040691 10309880927488486374061037)
                    ·
                      refine ⟨3866205347808182390272889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309880927488486374061037 3866205347808182390272889)
                      ·
                        rfl

theorem cell23_7529408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_7529408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529408 prefixEnd_7529408 := by exact prefixLift 7529408
  have htrace : WordTrace (prefixWord ++ tailWord_7529408) baseStart_7529408 baseEnd_7529408 := by
    simpa [prefixWord, tailWord_7529408, baseEnd_7529408] using wordTrace_append hprefix tailTrace_7529408
  have hstable : (prefixWord ++ tailWord_7529408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529408).length < 2 ^ (prefixWord ++ tailWord_7529408).sum := by decide
  have hdescent : baseEnd_7529408 < baseStart_7529408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529412 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7529412 : Nat := 118140960795 + 7529412 * 2 ^ 59
def prefixEnd_7529412 : Nat := 4983230072969 + 3 ^ 40 * 7529412 * 2
def baseEnd_7529412 : Nat := 3866207401730800374622871

theorem tailTrace_7529412 : CollatzResearch.WordTrace tailWord_7529412 prefixEnd_7529412 3866207401730800374622871 := by
  unfold tailWord_7529412
  simp only [CollatzResearch.WordTrace]
  refine ⟨137310108299116860018647245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183080144398822480024862993 137310108299116860018647245)
  ·
    refine ⟨51491290612168822506992717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137310108299116860018647245 51491290612168822506992717)
    ·
      refine ⟨19309233979563308440122269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51491290612168822506992717 19309233979563308440122269)
      ·
        refine ⟨7240962742336240665045851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19309233979563308440122269 7240962742336240665045851)
        ·
          refine ⟨10861444113504360997568777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7240962742336240665045851 10861444113504360997568777)
          ·
            refine ⟨8146083085128270748176583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10861444113504360997568777 8146083085128270748176583)
            ·
              refine ⟨12219124627692406122264875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146083085128270748176583 12219124627692406122264875)
              ·
                refine ⟨18328686941538609183397313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12219124627692406122264875 18328686941538609183397313)
                ·
                  refine ⟨13746515206153956887547985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18328686941538609183397313 13746515206153956887547985)
                  ·
                    refine ⟨10309886404615467665660989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746515206153956887547985 10309886404615467665660989)
                    ·
                      refine ⟨3866207401730800374622871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309886404615467665660989 3866207401730800374622871)
                      ·
                        rfl

theorem cell23_7529412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7529412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529412 prefixEnd_7529412 := by exact prefixLift 7529412
  have htrace : WordTrace (prefixWord ++ tailWord_7529412) baseStart_7529412 baseEnd_7529412 := by
    simpa [prefixWord, tailWord_7529412, baseEnd_7529412] using wordTrace_append hprefix tailTrace_7529412
  have hstable : (prefixWord ++ tailWord_7529412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529412).length < 2 ^ (prefixWord ++ tailWord_7529412).sum := by decide
  have hdescent : baseEnd_7529412 < baseStart_7529412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529425 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 1, 1, 3]
def baseStart_7529425 : Nat := 118140960795 + 7529425 * 2 ^ 59
def prefixEnd_7529425 : Nat := 4983230072969 + 3 ^ 40 * 7529425 * 2
def baseEnd_7529425 : Nat := 3866214076979308823760311

theorem tailTrace_7529425 : CollatzResearch.WordTrace tailWord_7529425 prefixEnd_7529425 3866214076979308823760311 := by
  unfold tailWord_7529425
  simp only [CollatzResearch.WordTrace]
  refine ⟨274620690747186623257517729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183080460498124415505011819 274620690747186623257517729)
  ·
    refine ⟨205965518060389967443138297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274620690747186623257517729 205965518060389967443138297)
    ·
      refine ⟨154474138545292475582353723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205965518060389967443138297 154474138545292475582353723)
      ·
        refine ⟨231711207817938713373530585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154474138545292475582353723 231711207817938713373530585)
        ·
          refine ⟨173783405863454035030147939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231711207817938713373530585 173783405863454035030147939)
          ·
            refine ⟨260675108795181052545221909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173783405863454035030147939 260675108795181052545221909)
            ·
              refine ⟨12219145724774111838057277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260675108795181052545221909 12219145724774111838057277)
              ·
                refine ⟨4582179646790291939271479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12219145724774111838057277 4582179646790291939271479)
                ·
                  refine ⟨6873269470185437908907219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582179646790291939271479 6873269470185437908907219)
                  ·
                    refine ⟨10309904205278156863360829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873269470185437908907219 10309904205278156863360829)
                    ·
                      refine ⟨3866214076979308823760311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309904205278156863360829 3866214076979308823760311)
                      ·
                        rfl

theorem cell23_7529425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_7529425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529425 prefixEnd_7529425 := by exact prefixLift 7529425
  have htrace : WordTrace (prefixWord ++ tailWord_7529425) baseStart_7529425 baseEnd_7529425 := by
    simpa [prefixWord, tailWord_7529425, baseEnd_7529425] using wordTrace_append hprefix tailTrace_7529425
  have hstable : (prefixWord ++ tailWord_7529425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529425).length < 2 ^ (prefixWord ++ tailWord_7529425).sum := by decide
  have hdescent : baseEnd_7529425 < baseStart_7529425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529428 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_7529428 : Nat := 118140960795 + 7529428 * 2 ^ 59
def prefixEnd_7529428 : Nat := 4983230072969 + 3 ^ 40 * 7529428 * 2
def baseEnd_7529428 : Nat := 1288738539140424104007599

theorem tailTrace_7529428 : CollatzResearch.WordTrace tailWord_7529428 prefixEnd_7529428 1288738539140424104007599 := by
  unfold tailWord_7529428
  simp only [CollatzResearch.WordTrace]
  refine ⟨137310400083087877384938469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183080533444117169846584625 137310400083087877384938469)
  ·
    refine ⟨25745700015578977009675963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137310400083087877384938469 25745700015578977009675963)
    ·
      refine ⟨38618550023368465514513945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25745700015578977009675963 38618550023368465514513945)
      ·
        refine ⟨28963912517526349135885459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38618550023368465514513945 28963912517526349135885459)
        ·
          refine ⟨43445868776289523703828189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28963912517526349135885459 43445868776289523703828189)
          ·
            refine ⟨16292200791108571388935571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43445868776289523703828189 16292200791108571388935571)
            ·
              refine ⟨24438301186662857083403357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292200791108571388935571 24438301186662857083403357)
              ·
                refine ⟨9164362944998571406276259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24438301186662857083403357 9164362944998571406276259)
                ·
                  refine ⟨13746544417497857109414389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164362944998571406276259 13746544417497857109414389)
                  ·
                    refine ⟨1288738539140424104007599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13746544417497857109414389 1288738539140424104007599)
                    ·
                      rfl

theorem cell23_7529428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_7529428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529428 prefixEnd_7529428 := by exact prefixLift 7529428
  have htrace : WordTrace (prefixWord ++ tailWord_7529428) baseStart_7529428 baseEnd_7529428 := by
    simpa [prefixWord, tailWord_7529428, baseEnd_7529428] using wordTrace_append hprefix tailTrace_7529428
  have hstable : (prefixWord ++ tailWord_7529428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529428).length < 2 ^ (prefixWord ++ tailWord_7529428).sum := by decide
  have hdescent : baseEnd_7529428 < baseStart_7529428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529442 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7529442 : Nat := 118140960795 + 7529442 * 2 ^ 59
def prefixEnd_7529442 : Nat := 4983230072969 + 3 ^ 40 * 7529442 * 2
def baseEnd_7529442 : Nat := 3866222806150435257247733

theorem tailTrace_7529442 : CollatzResearch.WordTrace tailWord_7529442 prefixEnd_7529442 3866222806150435257247733 := by
  unfold tailWord_7529442
  simp only [CollatzResearch.WordTrace]
  refine ⟨68655327697031258790221645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183080873858750023440591053 68655327697031258790221645)
  ·
    refine ⟨25745747886386722046333117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68655327697031258790221645 25745747886386722046333117)
    ·
      refine ⟨9654655457395020767374919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25745747886386722046333117 9654655457395020767374919)
      ·
        refine ⟨14481983186092531151062379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654655457395020767374919 14481983186092531151062379)
        ·
          refine ⟨21722974779138796726593569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481983186092531151062379 21722974779138796726593569)
          ·
            refine ⟨16292231084354097544945177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21722974779138796726593569 16292231084354097544945177)
            ·
              refine ⟨12219173313265573158708883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16292231084354097544945177 12219173313265573158708883)
              ·
                refine ⟨18328759969898359738063325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12219173313265573158708883 18328759969898359738063325)
                ·
                  refine ⟨6873284988711884901773747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18328759969898359738063325 6873284988711884901773747)
                  ·
                    refine ⟨10309927483067827352660621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873284988711884901773747 10309927483067827352660621)
                    ·
                      refine ⟨3866222806150435257247733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309927483067827352660621 3866222806150435257247733)
                      ·
                        rfl

theorem cell23_7529442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7529442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529442 prefixEnd_7529442 := by exact prefixLift 7529442
  have htrace : WordTrace (prefixWord ++ tailWord_7529442) baseStart_7529442 baseEnd_7529442 := by
    simpa [prefixWord, tailWord_7529442, baseEnd_7529442] using wordTrace_append hprefix tailTrace_7529442
  have hstable : (prefixWord ++ tailWord_7529442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529442).length < 2 ^ (prefixWord ++ tailWord_7529442).sum := by decide
  have hdescent : baseEnd_7529442 < baseStart_7529442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529468 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_7529468 : Nat := 118140960795 + 7529468 * 2 ^ 59
def prefixEnd_7529468 : Nat := 4983230072969 + 3 ^ 40 * 7529468 * 2
def baseEnd_7529468 : Nat := 3866236156647452155522613

theorem tailTrace_7529468 : CollatzResearch.WordTrace tailWord_7529468 prefixEnd_7529468 3866236156647452155522613 := by
  unfold tailWord_7529468
  simp only [CollatzResearch.WordTrace]
  refine ⟨137311129543015420800666529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183081506057353894400888705 137311129543015420800666529)
  ·
    refine ⟨102983347157261565600499897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137311129543015420800666529 102983347157261565600499897)
    ·
      refine ⟨77237510367946174200374923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102983347157261565600499897 77237510367946174200374923)
      ·
        refine ⟨115856265551919261300562385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77237510367946174200374923 115856265551919261300562385)
        ·
          refine ⟨86892199163939445975421789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115856265551919261300562385 86892199163939445975421789)
          ·
            refine ⟨32584574686477292240783171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86892199163939445975421789 32584574686477292240783171)
            ·
              refine ⟨48876862029715938361174757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32584574686477292240783171 48876862029715938361174757)
              ·
                refine ⟨9164411630571738442720267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48876862029715938361174757 9164411630571738442720267)
                ·
                  refine ⟨13746617445857607664080401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164411630571738442720267 13746617445857607664080401)
                  ·
                    refine ⟨10309963084393205748060301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746617445857607664080401 10309963084393205748060301)
                    ·
                      refine ⟨3866236156647452155522613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309963084393205748060301 3866236156647452155522613)
                      ·
                        rfl

theorem cell23_7529468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_7529468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529468 prefixEnd_7529468 := by exact prefixLift 7529468
  have htrace : WordTrace (prefixWord ++ tailWord_7529468) baseStart_7529468 baseEnd_7529468 := by
    simpa [prefixWord, tailWord_7529468, baseEnd_7529468] using wordTrace_append hprefix tailTrace_7529468
  have hstable : (prefixWord ++ tailWord_7529468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529468).length < 2 ^ (prefixWord ++ tailWord_7529468).sum := by decide
  have hdescent : baseEnd_7529468 < baseStart_7529468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529481 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_7529481 : Nat := 118140960795 + 7529481 * 2 ^ 59
def prefixEnd_7529481 : Nat := 4983230072969 + 3 ^ 40 * 7529481 * 2
def baseEnd_7529481 : Nat := 3866242831895960604660053

theorem tailTrace_7529481 : CollatzResearch.WordTrace tailWord_7529481 prefixEnd_7529481 3866242831895960604660053 := by
  unfold tailWord_7529481
  simp only [CollatzResearch.WordTrace]
  refine ⟨274622733234983744821556297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183081822156655829881037531 274622733234983744821556297)
  ·
    refine ⟨205967049926237808616167223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274622733234983744821556297 205967049926237808616167223)
    ·
      refine ⟨308950574889356712924250835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205967049926237808616167223 308950574889356712924250835)
      ·
        refine ⟨463425862334035069386376253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308950574889356712924250835 463425862334035069386376253)
        ·
          refine ⟨173784698375263151019891095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463425862334035069386376253 173784698375263151019891095)
          ·
            refine ⟨260677047562894726529836643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173784698375263151019891095 260677047562894726529836643)
            ·
              refine ⟨391015571344342089794754965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260677047562894726529836643 391015571344342089794754965)
              ·
                refine ⟨18328854906766035459129139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391015571344342089794754965 18328854906766035459129139)
                ·
                  refine ⟨27493282360149053188693709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18328854906766035459129139 27493282360149053188693709)
                  ·
                    refine ⟨10309980885055894945760141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27493282360149053188693709 10309980885055894945760141)
                    ·
                      refine ⟨3866242831895960604660053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10309980885055894945760141 3866242831895960604660053)
                      ·
                        rfl

theorem cell23_7529481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_7529481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529481 prefixEnd_7529481 := by exact prefixLift 7529481
  have htrace : WordTrace (prefixWord ++ tailWord_7529481) baseStart_7529481 baseEnd_7529481 := by
    simpa [prefixWord, tailWord_7529481, baseEnd_7529481] using wordTrace_append hprefix tailTrace_7529481
  have hstable : (prefixWord ++ tailWord_7529481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529481).length < 2 ^ (prefixWord ++ tailWord_7529481).sum := by decide
  have hdescent : baseEnd_7529481 < baseStart_7529481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529498 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_7529498 : Nat := 118140960795 + 7529498 * 2 ^ 59
def prefixEnd_7529498 : Nat := 4983230072969 + 3 ^ 40 * 7529498 * 2
def baseEnd_7529498 : Nat := 3866251561067087038147475

theorem tailTrace_7529498 : CollatzResearch.WordTrace tailWord_7529498 prefixEnd_7529498 3866251561067087038147475 := by
  unfold tailWord_7529498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68655838318980539181231287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183082235517281437816616765 68655838318980539181231287)
  ·
    refine ⟨102983757478470808771846931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68655838318980539181231287 102983757478470808771846931)
    ·
      refine ⟨154475636217706213157770397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102983757478470808771846931 154475636217706213157770397)
      ·
        refine ⟨57928363581639829934163899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154475636217706213157770397 57928363581639829934163899)
        ·
          refine ⟨86892545372459744901245849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57928363581639829934163899 86892545372459744901245849)
          ·
            refine ⟨65169409029344808675934387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86892545372459744901245849 65169409029344808675934387)
            ·
              refine ⟨97754113544017213013901581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65169409029344808675934387 97754113544017213013901581)
              ·
                refine ⟨36657792579006454880213093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97754113544017213013901581 36657792579006454880213093)
                ·
                  refine ⟨6873336108563710290039955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36657792579006454880213093 6873336108563710290039955)
                  ·
                    refine ⟨10310004162845565435059933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873336108563710290039955 10310004162845565435059933)
                    ·
                      refine ⟨3866251561067087038147475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310004162845565435059933 3866251561067087038147475)
                      ·
                        rfl

theorem cell23_7529498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_7529498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529498 prefixEnd_7529498 := by exact prefixLift 7529498
  have htrace : WordTrace (prefixWord ++ tailWord_7529498) baseStart_7529498 baseEnd_7529498 := by
    simpa [prefixWord, tailWord_7529498, baseEnd_7529498] using wordTrace_append hprefix tailTrace_7529498
  have hstable : (prefixWord ++ tailWord_7529498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529498).length < 2 ^ (prefixWord ++ tailWord_7529498).sum := by decide
  have hdescent : baseEnd_7529498 < baseStart_7529498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529541 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_7529541 : Nat := 118140960795 + 7529541 * 2 ^ 59
def prefixEnd_7529541 : Nat := 4983230072969 + 3 ^ 40 * 7529541 * 2
def baseEnd_7529541 : Nat := 3866273640735230369909777

theorem tailTrace_7529541 : CollatzResearch.WordTrace tailWord_7529541 prefixEnd_7529541 3866273640735230369909777 := by
  unfold tailWord_7529541
  simp only [CollatzResearch.WordTrace]
  refine ⟨274624921614766375068740477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183083281076510916712493651 274624921614766375068740477)
  ·
    refine ⟨102984345605537390650777679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274624921614766375068740477 102984345605537390650777679)
    ·
      refine ⟨154476518408306085976166519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102984345605537390650777679 154476518408306085976166519)
      ·
        refine ⟨231714777612459128964249779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154476518408306085976166519 231714777612459128964249779)
        ·
          refine ⟨347572166418688693446374669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231714777612459128964249779 347572166418688693446374669)
          ·
            refine ⟨130339562407008260042390501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347572166418688693446374669 130339562407008260042390501)
            ·
              refine ⟨24438667951314048757948219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130339562407008260042390501 24438667951314048757948219)
              ·
                refine ⟨36658001926971073136922329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24438667951314048757948219 36658001926971073136922329)
                ·
                  refine ⟨27493501445228304852691747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36658001926971073136922329 27493501445228304852691747)
                  ·
                    refine ⟨41240252167842457279037621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27493501445228304852691747 41240252167842457279037621)
                    ·
                      refine ⟨3866273640735230369909777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41240252167842457279037621 3866273640735230369909777)
                      ·
                        rfl

theorem cell23_7529541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_7529541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529541 prefixEnd_7529541 := by exact prefixLift 7529541
  have htrace : WordTrace (prefixWord ++ tailWord_7529541) baseStart_7529541 baseEnd_7529541 := by
    simpa [prefixWord, tailWord_7529541, baseEnd_7529541] using wordTrace_append hprefix tailTrace_7529541
  have hstable : (prefixWord ++ tailWord_7529541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529541).length < 2 ^ (prefixWord ++ tailWord_7529541).sum := by decide
  have hdescent : baseEnd_7529541 < baseStart_7529541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529555 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 2, 2, 2]
def baseStart_7529555 : Nat := 118140960795 + 7529555 * 2 ^ 59
def prefixEnd_7529555 : Nat := 4983230072969 + 3 ^ 40 * 7529555 * 2
def baseEnd_7529555 : Nat := 3866280829464393315134713

theorem tailTrace_7529555 : CollatzResearch.WordTrace tailWord_7529555 prefixEnd_7529555 3866280829464393315134713 := by
  unfold tailWord_7529555
  simp only [CollatzResearch.WordTrace]
  refine ⟨274625432236715655459750119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183083621491143770306500079 274625432236715655459750119)
  ·
    refine ⟨411938148355073483189625179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274625432236715655459750119 411938148355073483189625179)
    ·
      refine ⟨617907222532610224784437769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411938148355073483189625179 617907222532610224784437769)
      ·
        refine ⟨463430416899457668588328327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617907222532610224784437769 463430416899457668588328327)
        ·
          refine ⟨695145625349186502882492491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463430416899457668588328327 695145625349186502882492491)
          ·
            refine ⟨1042718438023779754323738737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695145625349186502882492491 1042718438023779754323738737)
            ·
              refine ⟨782038828517834815742804053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042718438023779754323738737 782038828517834815742804053)
              ·
                refine ⟨9164517521693376746985985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 782038828517834815742804053 9164517521693376746985985)
                ·
                  refine ⟨6873388141270032560239489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164517521693376746985985 6873388141270032560239489)
                  ·
                    refine ⟨5155041105952524420179617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873388141270032560239489 5155041105952524420179617)
                    ·
                      refine ⟨3866280829464393315134713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155041105952524420179617 3866280829464393315134713)
                      ·
                        rfl

theorem cell23_7529555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 2, 2].length) (baseStart_7529555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529555 prefixEnd_7529555 := by exact prefixLift 7529555
  have htrace : WordTrace (prefixWord ++ tailWord_7529555) baseStart_7529555 baseEnd_7529555 := by
    simpa [prefixWord, tailWord_7529555, baseEnd_7529555] using wordTrace_append hprefix tailTrace_7529555
  have hstable : (prefixWord ++ tailWord_7529555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529555).length < 2 ^ (prefixWord ++ tailWord_7529555).sum := by decide
  have hdescent : baseEnd_7529555 < baseStart_7529555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529565 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7529565 : Nat := 118140960795 + 7529565 * 2 ^ 59
def prefixEnd_7529565 : Nat := 4983230072969 + 3 ^ 40 * 7529565 * 2
def baseEnd_7529565 : Nat := 1288761988090312758669889

theorem tailTrace_7529565 : CollatzResearch.WordTrace tailWord_7529565 prefixEnd_7529565 1288761988090312758669889 := by
  unfold tailWord_7529565
  simp only [CollatzResearch.WordTrace]
  refine ⟨274625796966679427167614149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183083864644452951445076099 274625796966679427167614149)
  ·
    refine ⟨51492336931252392593927653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274625796966679427167614149 51492336931252392593927653)
    ·
      refine ⟨9654813174609823611361435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51492336931252392593927653 9654813174609823611361435)
      ·
        refine ⟨14482219761914735417042153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654813174609823611361435 14482219761914735417042153)
        ·
          refine ⟨10861664821436051562781615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14482219761914735417042153 10861664821436051562781615)
          ·
            refine ⟨16292497232154077344172423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10861664821436051562781615 16292497232154077344172423)
            ·
              refine ⟨24438745848231116016258635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292497232154077344172423 24438745848231116016258635)
              ·
                refine ⟨36658118772346674024387953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24438745848231116016258635 36658118772346674024387953)
                ·
                  refine ⟨27493589079260005518290965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36658118772346674024387953 27493589079260005518290965)
                  ·
                    refine ⟨1288761988090312758669889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27493589079260005518290965 1288761988090312758669889)
                    ·
                      rfl

theorem cell23_7529565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7529565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529565 prefixEnd_7529565 := by exact prefixLift 7529565
  have htrace : WordTrace (prefixWord ++ tailWord_7529565) baseStart_7529565 baseEnd_7529565 := by
    simpa [prefixWord, tailWord_7529565, baseEnd_7529565] using wordTrace_append hprefix tailTrace_7529565
  have hstable : (prefixWord ++ tailWord_7529565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529565).length < 2 ^ (prefixWord ++ tailWord_7529565).sum := by decide
  have hdescent : baseEnd_7529565 < baseStart_7529565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529578 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_7529578 : Nat := 118140960795 + 7529578 * 2 ^ 59
def prefixEnd_7529578 : Nat := 4983230072969 + 3 ^ 40 * 7529578 * 2
def baseEnd_7529578 : Nat := 429588071057716302794123

theorem tailTrace_7529578 : CollatzResearch.WordTrace tailWord_7529578 prefixEnd_7529578 429588071057716302794123 := by
  unfold tailWord_7529578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68656567778908082596959347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183084180743754886925224925 68656567778908082596959347)
  ·
    refine ⟨102984851668362123895439021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68656567778908082596959347 102984851668362123895439021)
    ·
      refine ⟨38619319375635796460789633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102984851668362123895439021 38619319375635796460789633)
      ·
        refine ⟨28964489531726847345592225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38619319375635796460789633 28964489531726847345592225)
        ·
          refine ⟨21723367148795135509194169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28964489531726847345592225 21723367148795135509194169)
          ·
            refine ⟨16292525361596351631895627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21723367148795135509194169 16292525361596351631895627)
            ·
              refine ⟨24438788042394527447843441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292525361596351631895627 24438788042394527447843441)
              ·
                refine ⟨18329091031795895585882581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24438788042394527447843441 18329091031795895585882581)
                ·
                  refine ⟨429588071057716302794123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18329091031795895585882581 429588071057716302794123)
                  ·
                    rfl

theorem cell23_7529578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_7529578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529578 prefixEnd_7529578 := by exact prefixLift 7529578
  have htrace : WordTrace (prefixWord ++ tailWord_7529578) baseStart_7529578 baseEnd_7529578 := by
    simpa [prefixWord, tailWord_7529578, baseEnd_7529578] using wordTrace_append hprefix tailTrace_7529578
  have hstable : (prefixWord ++ tailWord_7529578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529578).length < 2 ^ (prefixWord ++ tailWord_7529578).sum := by decide
  have hdescent : baseEnd_7529578 < baseStart_7529578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529591 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 7]
def baseStart_7529591 : Nat := 118140960795 + 7529591 * 2 ^ 59
def prefixEnd_7529591 : Nat := 4983230072969 + 3 ^ 40 * 7529591 * 2
def baseEnd_7529591 : Nat := 1288766438255985058094849

theorem tailTrace_7529591 : CollatzResearch.WordTrace tailWord_7529591 prefixEnd_7529591 1288766438255985058094849 := by
  unfold tailWord_7529591
  simp only [CollatzResearch.WordTrace]
  refine ⟨274626745264585233608060627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183084496843056822405373751 274626745264585233608060627)
  ·
    refine ⟨411940117896877850412090941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274626745264585233608060627 411940117896877850412090941)
    ·
      refine ⟨154477544211329193904534103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411940117896877850412090941 154477544211329193904534103)
      ·
        refine ⟨231716316316993790856801155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154477544211329193904534103 231716316316993790856801155)
        ·
          refine ⟨347574474475490686285201733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231716316316993790856801155 347574474475490686285201733)
          ·
            refine ⟨65170213964154503678475325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347574474475490686285201733 65170213964154503678475325)
            ·
              refine ⟨24438830236557938879428247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65170213964154503678475325 24438830236557938879428247)
              ·
                refine ⟨36658245354836908319142371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24438830236557938879428247 36658245354836908319142371)
                ·
                  refine ⟨54987368032255362478713557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36658245354836908319142371 54987368032255362478713557)
                  ·
                    refine ⟨1288766438255985058094849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54987368032255362478713557 1288766438255985058094849)
                    ·
                      rfl

theorem cell23_7529591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_7529591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529591 prefixEnd_7529591 := by exact prefixLift 7529591
  have htrace : WordTrace (prefixWord ++ tailWord_7529591) baseStart_7529591 baseEnd_7529591 := by
    simpa [prefixWord, tailWord_7529591, baseEnd_7529591] using wordTrace_append hprefix tailTrace_7529591
  have hstable : (prefixWord ++ tailWord_7529591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529591).length < 2 ^ (prefixWord ++ tailWord_7529591).sum := by decide
  have hdescent : baseEnd_7529591 < baseStart_7529591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529628 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7529628 : Nat := 118140960795 + 7529628 * 2 ^ 59
def prefixEnd_7529628 : Nat := 4983230072969 + 3 ^ 40 * 7529628 * 2
def baseEnd_7529628 : Nat := 3866318313552171529521877

theorem tailTrace_7529628 : CollatzResearch.WordTrace tailWord_7529628 prefixEnd_7529628 3866318313552171529521877 := by
  unfold tailWord_7529628
  simp only [CollatzResearch.WordTrace]
  refine ⟨137314047382725594463578769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183085396510300792618105025 137314047382725594463578769)
  ·
    refine ⟨102985535537044195847684077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137314047382725594463578769 102985535537044195847684077)
    ·
      refine ⟨38619575826391573442881529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102985535537044195847684077 38619575826391573442881529)
      ·
        refine ⟨28964681869793680082161147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38619575826391573442881529 28964681869793680082161147)
        ·
          refine ⟨43447022804690520123241721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28964681869793680082161147 43447022804690520123241721)
          ·
            refine ⟨32585267103517890092431291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43447022804690520123241721 32585267103517890092431291)
            ·
              refine ⟨48877900655276835138646937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32585267103517890092431291 48877900655276835138646937)
              ·
                refine ⟨36658425491457626353985203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48877900655276835138646937 36658425491457626353985203)
                ·
                  refine ⟨54987638237186439530977805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36658425491457626353985203 54987638237186439530977805)
                  ·
                    refine ⟨20620364338944914824116677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54987638237186439530977805 20620364338944914824116677)
                    ·
                      refine ⟨3866318313552171529521877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20620364338944914824116677 3866318313552171529521877)
                      ·
                        rfl

theorem cell23_7529628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7529628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529628 prefixEnd_7529628 := by exact prefixLift 7529628
  have htrace : WordTrace (prefixWord ++ tailWord_7529628) baseStart_7529628 baseEnd_7529628 := by
    simpa [prefixWord, tailWord_7529628, baseEnd_7529628] using wordTrace_append hprefix tailTrace_7529628
  have hstable : (prefixWord ++ tailWord_7529628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529628).length < 2 ^ (prefixWord ++ tailWord_7529628).sum := by decide
  have hdescent : baseEnd_7529628 < baseStart_7529628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529651 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 8]
def baseStart_7529651 : Nat := 118140960795 + 7529651 * 2 ^ 59
def prefixEnd_7529651 : Nat := 4983230072969 + 3 ^ 40 * 7529651 * 2
def baseEnd_7529651 : Nat := 429592235956358326614919

theorem tailTrace_7529651 : CollatzResearch.WordTrace tailWord_7529651 prefixEnd_7529651 429592235956358326614919 := by
  unfold tailWord_7529651
  simp only [CollatzResearch.WordTrace]
  refine ⟨274628933644367863855244807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183085955762911909236829871 274628933644367863855244807)
  ·
    refine ⟨411943400466551795782867211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274628933644367863855244807 411943400466551795782867211)
    ·
      refine ⟨617915100699827693674300817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411943400466551795782867211 617915100699827693674300817)
      ·
        refine ⟨463436325524870770255725613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617915100699827693674300817 463436325524870770255725613)
        ·
          refine ⟨173788622071826538845897105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463436325524870770255725613 173788622071826538845897105)
          ·
            refine ⟨130341466553869904134422829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173788622071826538845897105 130341466553869904134422829)
            ·
              refine ⟨48878049957701214050408561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130341466553869904134422829 48878049957701214050408561)
              ·
                refine ⟨36658537468275910537806421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48878049957701214050408561 36658537468275910537806421)
                ·
                  refine ⟨429592235956358326614919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36658537468275910537806421 429592235956358326614919)
                  ·
                    rfl

theorem cell23_7529651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 8].length) (baseStart_7529651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529651 prefixEnd_7529651 := by exact prefixLift 7529651
  have htrace : WordTrace (prefixWord ++ tailWord_7529651) baseStart_7529651 baseEnd_7529651 := by
    simpa [prefixWord, tailWord_7529651, baseEnd_7529651] using wordTrace_append hprefix tailTrace_7529651
  have hstable : (prefixWord ++ tailWord_7529651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529651).length < 2 ^ (prefixWord ++ tailWord_7529651).sum := by decide
  have hdescent : baseEnd_7529651 < baseStart_7529651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529671 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_7529671 : Nat := 118140960795 + 7529671 * 2 ^ 59
def prefixEnd_7529671 : Nat := 4983230072969 + 3 ^ 40 * 7529671 * 2
def baseEnd_7529671 : Nat := 3866340393220314861284179

theorem tailTrace_7529671 : CollatzResearch.WordTrace tailWord_7529671 prefixEnd_7529671 3866340393220314861284179 := by
  unfold tailWord_7529671
  simp only [CollatzResearch.WordTrace]
  refine ⟨274629663104295407270972867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183086442069530271513981911 274629663104295407270972867)
  ·
    refine ⟨411944494656443110906459301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274629663104295407270972867 411944494656443110906459301)
    ·
      refine ⟨77239592748083083294961119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411944494656443110906459301 77239592748083083294961119)
      ·
        refine ⟨115859389122124624942441679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77239592748083083294961119 115859389122124624942441679)
        ·
          refine ⟨173789083683186937413662519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115859389122124624942441679 173789083683186937413662519)
          ·
            refine ⟨260683625524780406120493779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173789083683186937413662519 260683625524780406120493779)
            ·
              refine ⟨391025438287170609180740669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260683625524780406120493779 391025438287170609180740669)
              ·
                refine ⟨146634539357688978442777751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391025438287170609180740669 146634539357688978442777751)
                ·
                  refine ⟨219951809036533467664166627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146634539357688978442777751 219951809036533467664166627)
                  ·
                    refine ⟨329927713554800201496249941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219951809036533467664166627 329927713554800201496249941)
                    ·
                      refine ⟨3866340393220314861284179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 329927713554800201496249941 3866340393220314861284179)
                      ·
                        rfl

theorem cell23_7529671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_7529671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529671 prefixEnd_7529671 := by exact prefixLift 7529671
  have htrace : WordTrace (prefixWord ++ tailWord_7529671) baseStart_7529671 baseEnd_7529671 := by
    simpa [prefixWord, tailWord_7529671, baseEnd_7529671] using wordTrace_append hprefix tailTrace_7529671
  have hstable : (prefixWord ++ tailWord_7529671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529671).length < 2 ^ (prefixWord ++ tailWord_7529671).sum := by decide
  have hdescent : baseEnd_7529671 < baseStart_7529671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529681 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_7529681 : Nat := 118140960795 + 7529681 * 2 ^ 59
def prefixEnd_7529681 : Nat := 4983230072969 + 3 ^ 40 * 7529681 * 2
def baseEnd_7529681 : Nat := 1288781842675619940719711

theorem tailTrace_7529681 : CollatzResearch.WordTrace tailWord_7529681 prefixEnd_7529681 1288781842675619940719711 := by
  unfold tailWord_7529681
  simp only [CollatzResearch.WordTrace]
  refine ⟨274630027834259178978836897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183086685222839452652557931 274630027834259178978836897)
  ·
    refine ⟨205972520875694384234127673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274630027834259178978836897 205972520875694384234127673)
    ·
      refine ⟨154479390656770788175595755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205972520875694384234127673 154479390656770788175595755)
      ·
        refine ⟨231719085985156182263393633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154479390656770788175595755 231719085985156182263393633)
        ·
          refine ⟨173789314488867136697545225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231719085985156182263393633 173789314488867136697545225)
          ·
            refine ⟨130341985866650352523158919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173789314488867136697545225 130341985866650352523158919)
            ·
              refine ⟨195512978799975528784738379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130341985866650352523158919 195512978799975528784738379)
              ·
                refine ⟨293269468199963293177107569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195512978799975528784738379 293269468199963293177107569)
                ·
                  refine ⟨219952101149972469882830677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293269468199963293177107569 219952101149972469882830677)
                  ·
                    refine ⟨1288781842675619940719711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219952101149972469882830677 1288781842675619940719711)
                    ·
                      rfl

theorem cell23_7529681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_7529681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529681 prefixEnd_7529681 := by exact prefixLift 7529681
  have htrace : WordTrace (prefixWord ++ tailWord_7529681) baseStart_7529681 baseEnd_7529681 := by
    simpa [prefixWord, tailWord_7529681, baseEnd_7529681] using wordTrace_append hprefix tailTrace_7529681
  have hstable : (prefixWord ++ tailWord_7529681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529681).length < 2 ^ (prefixWord ++ tailWord_7529681).sum := by decide
  have hdescent : baseEnd_7529681 < baseStart_7529681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529685 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 6]
def baseStart_7529685 : Nat := 118140960795 + 7529685 * 2 ^ 59
def prefixEnd_7529685 : Nat := 4983230072969 + 3 ^ 40 * 7529685 * 2
def baseEnd_7529685 : Nat := 429594175772164200723235

theorem tailTrace_7529685 : CollatzResearch.WordTrace tailWord_7529685 prefixEnd_7529685 429594175772164200723235 := by
  unfold tailWord_7529685
  simp only [CollatzResearch.WordTrace]
  refine ⟨274630173726244687661982509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183086782484163125107988339 274630173726244687661982509)
  ·
    refine ⟨102986315147341757873243441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274630173726244687661982509 102986315147341757873243441)
    ·
      refine ⟨77239736360506318404932581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102986315147341757873243441 77239736360506318404932581)
      ·
        refine ⟨14482450567594934700924859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77239736360506318404932581 14482450567594934700924859)
        ·
          refine ⟨21723675851392402051387289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482450567594934700924859 21723675851392402051387289)
          ·
            refine ⟨16292756888544301538540467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21723675851392402051387289 16292756888544301538540467)
            ·
              refine ⟨24439135332816452307810701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292756888544301538540467 24439135332816452307810701)
              ·
                refine ⟨9164675749806169615429013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24439135332816452307810701 9164675749806169615429013)
                ·
                  refine ⟨429594175772164200723235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9164675749806169615429013 429594175772164200723235)
                  ·
                    rfl

theorem cell23_7529685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_7529685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529685 prefixEnd_7529685 := by exact prefixLift 7529685
  have htrace : WordTrace (prefixWord ++ tailWord_7529685) baseStart_7529685 baseEnd_7529685 := by
    simpa [prefixWord, tailWord_7529685, baseEnd_7529685] using wordTrace_append hprefix tailTrace_7529685
  have hstable : (prefixWord ++ tailWord_7529685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529685).length < 2 ^ (prefixWord ++ tailWord_7529685).sum := by decide
  have hdescent : baseEnd_7529685 < baseStart_7529685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529691 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_7529691 : Nat := 118140960795 + 7529691 * 2 ^ 59
def prefixEnd_7529691 : Nat := 4983230072969 + 3 ^ 40 * 7529691 * 2
def baseEnd_7529691 : Nat := 3866350662833404783034087

theorem tailTrace_7529691 : CollatzResearch.WordTrace tailWord_7529691 prefixEnd_7529691 3866350662833404783034087 := by
  unfold tailWord_7529691
  simp only [CollatzResearch.WordTrace]
  refine ⟨274630392564222950686700927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183086928376148633791133951 274630392564222950686700927)
  ·
    refine ⟨411945588846334426030051391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274630392564222950686700927 411945588846334426030051391)
    ·
      refine ⟨617918383269501639045077087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411945588846334426030051391 617918383269501639045077087)
      ·
        refine ⟨926877574904252458567615631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617918383269501639045077087 926877574904252458567615631)
        ·
          refine ⟨1390316362356378687851423447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926877574904252458567615631 1390316362356378687851423447)
          ·
            refine ⟨2085474543534568031777135171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390316362356378687851423447 2085474543534568031777135171)
            ·
              refine ⟨3128211815301852047665702757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085474543534568031777135171 3128211815301852047665702757)
              ·
                refine ⟨586539715369097258937319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3128211815301852047665702757 586539715369097258937319267)
                ·
                  refine ⟨879809573053645888405978901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586539715369097258937319267 879809573053645888405978901)
                  ·
                    refine ⟨41241073736889651019030261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 879809573053645888405978901 41241073736889651019030261)
                    ·
                      refine ⟨3866350662833404783034087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41241073736889651019030261 3866350662833404783034087)
                      ·
                        rfl

theorem cell23_7529691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_7529691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529691 prefixEnd_7529691 := by exact prefixLift 7529691
  have htrace : WordTrace (prefixWord ++ tailWord_7529691) baseStart_7529691 baseEnd_7529691 := by
    simpa [prefixWord, tailWord_7529691, baseEnd_7529691] using wordTrace_append hprefix tailTrace_7529691
  have hstable : (prefixWord ++ tailWord_7529691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529691).length < 2 ^ (prefixWord ++ tailWord_7529691).sum := by decide
  have hdescent : baseEnd_7529691 < baseStart_7529691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529695 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 3]
def baseStart_7529695 : Nat := 118140960795 + 7529695 * 2 ^ 59
def prefixEnd_7529695 : Nat := 4983230072969 + 3 ^ 40 * 7529695 * 2
def baseEnd_7529695 : Nat := 3866352716756022767384069

theorem tailTrace_7529695 : CollatzResearch.WordTrace tailWord_7529695 prefixEnd_7529695 3866352716756022767384069 := by
  unfold tailWord_7529695
  simp only [CollatzResearch.WordTrace]
  refine ⟨274630538456208459369846539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183087025637472306246564359 274630538456208459369846539)
  ·
    refine ⟨411945807684312689054769809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274630538456208459369846539 411945807684312689054769809)
    ·
      refine ⟨308959355763234516791077357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411945807684312689054769809 308959355763234516791077357)
      ·
        refine ⟨115859758411212943796654009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308959355763234516791077357 115859758411212943796654009)
        ·
          refine ⟨86894818808409707847490507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115859758411212943796654009 86894818808409707847490507)
          ·
            refine ⟨130342228212614561771235761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86894818808409707847490507 130342228212614561771235761)
            ·
              refine ⟨97756671159460921328426821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130342228212614561771235761 97756671159460921328426821)
              ·
                refine ⟨18329375842398922749080029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97756671159460921328426821 18329375842398922749080029)
                ·
                  refine ⟨6873515940899596030905011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18329375842398922749080029 6873515940899596030905011)
                  ·
                    refine ⟨10310273911349394046357517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873515940899596030905011 10310273911349394046357517)
                    ·
                      refine ⟨3866352716756022767384069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310273911349394046357517 3866352716756022767384069)
                      ·
                        rfl

theorem cell23_7529695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_7529695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529695 prefixEnd_7529695 := by exact prefixLift 7529695
  have htrace : WordTrace (prefixWord ++ tailWord_7529695) baseStart_7529695 baseEnd_7529695 := by
    simpa [prefixWord, tailWord_7529695, baseEnd_7529695] using wordTrace_append hprefix tailTrace_7529695
  have hstable : (prefixWord ++ tailWord_7529695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529695).length < 2 ^ (prefixWord ++ tailWord_7529695).sum := by decide
  have hdescent : baseEnd_7529695 < baseStart_7529695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529729 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_7529729 : Nat := 118140960795 + 7529729 * 2 ^ 59
def prefixEnd_7529729 : Nat := 4983230072969 + 3 ^ 40 * 7529729 * 2
def baseEnd_7529729 : Nat := 3866370175098275634358913

theorem tailTrace_7529729 : CollatzResearch.WordTrace tailWord_7529729 prefixEnd_7529729 3866370175098275634358913 := by
  unfold tailWord_7529729
  simp only [CollatzResearch.WordTrace]
  refine ⟨274631778538085283176584241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183087852358723522117722827 274631778538085283176584241)
  ·
    refine ⟨205973833903563962382438181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274631778538085283176584241 205973833903563962382438181)
    ·
      refine ⟨38620093856918242946707159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205973833903563962382438181 38620093856918242946707159)
      ·
        refine ⟨57930140785377364420060739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38620093856918242946707159 57930140785377364420060739)
        ·
          refine ⟨86895211178066046630091109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57930140785377364420060739 86895211178066046630091109)
          ·
            refine ⟨16292852095887383743142083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86895211178066046630091109 16292852095887383743142083)
            ·
              refine ⟨24439278143831075614713125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292852095887383743142083 24439278143831075614713125)
              ·
                refine ⟨4582364651968326677758711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24439278143831075614713125 4582364651968326677758711)
                ·
                  refine ⟨6873546977952490016638067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582364651968326677758711 6873546977952490016638067)
                  ·
                    refine ⟨10310320466928735024957101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873546977952490016638067 10310320466928735024957101)
                    ·
                      refine ⟨3866370175098275634358913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310320466928735024957101 3866370175098275634358913)
                      ·
                        rfl

theorem cell23_7529729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_7529729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529729 prefixEnd_7529729 := by exact prefixLift 7529729
  have htrace : WordTrace (prefixWord ++ tailWord_7529729) baseStart_7529729 baseEnd_7529729 := by
    simpa [prefixWord, tailWord_7529729, baseEnd_7529729] using wordTrace_append hprefix tailTrace_7529729
  have hstable : (prefixWord ++ tailWord_7529729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529729).length < 2 ^ (prefixWord ++ tailWord_7529729).sum := by decide
  have hdescent : baseEnd_7529729 < baseStart_7529729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529738 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_7529738 : Nat := 118140960795 + 7529738 * 2 ^ 59
def prefixEnd_7529738 : Nat := 4983230072969 + 3 ^ 40 * 7529738 * 2
def baseEnd_7529738 : Nat := 3866374796424166099146371

theorem tailTrace_7529738 : CollatzResearch.WordTrace tailWord_7529738 prefixEnd_7529738 3866374796424166099146371 := by
  unfold tailWord_7529738
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658026698763169428415467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183088071196701785142441245 68658026698763169428415467)
  ·
    refine ⟨102987040048144754142623201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658026698763169428415467 102987040048144754142623201)
    ·
      refine ⟨77240280036108565606967401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102987040048144754142623201 77240280036108565606967401)
      ·
        refine ⟨57930210027081424205225551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77240280036108565606967401 57930210027081424205225551)
        ·
          refine ⟨86895315040622136307838327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57930210027081424205225551 86895315040622136307838327)
          ·
            refine ⟨130342972560933204461757491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86895315040622136307838327 130342972560933204461757491)
            ·
              refine ⟨195514458841399806692636237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130342972560933204461757491 195514458841399806692636237)
              ·
                refine ⟨73317922065524927509738589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195514458841399806692636237 73317922065524927509738589)
                ·
                  refine ⟨27494220774571847816151971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73317922065524927509738589 27494220774571847816151971)
                  ·
                    refine ⟨41241331161857771724227957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27494220774571847816151971 41241331161857771724227957)
                    ·
                      refine ⟨3866374796424166099146371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41241331161857771724227957 3866374796424166099146371)
                      ·
                        rfl

theorem cell23_7529738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_7529738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529738 prefixEnd_7529738 := by exact prefixLift 7529738
  have htrace : WordTrace (prefixWord ++ tailWord_7529738) baseStart_7529738 baseEnd_7529738 := by
    simpa [prefixWord, tailWord_7529738, baseEnd_7529738] using wordTrace_append hprefix tailTrace_7529738
  have hstable : (prefixWord ++ tailWord_7529738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529738).length < 2 ^ (prefixWord ++ tailWord_7529738).sum := by decide
  have hdescent : baseEnd_7529738 < baseStart_7529738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529745 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_7529745 : Nat := 118140960795 + 7529745 * 2 ^ 59
def prefixEnd_7529745 : Nat := 4983230072969 + 3 ^ 40 * 7529745 * 2
def baseEnd_7529745 : Nat := 1288792796929582523919613

theorem tailTrace_7529745 : CollatzResearch.WordTrace tailWord_7529745 prefixEnd_7529745 1288792796929582523919613 := by
  unfold tailWord_7529745
  simp only [CollatzResearch.WordTrace]
  refine ⟨274632362106027317909166689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183088241404018211939444459 274632362106027317909166689)
  ·
    refine ⟨205974271579520488431875017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274632362106027317909166689 205974271579520488431875017)
    ·
      refine ⟨154480703684640366323906263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205974271579520488431875017 154480703684640366323906263)
      ·
        refine ⟨231721055526960549485859395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154480703684640366323906263 231721055526960549485859395)
        ·
          refine ⟨347581583290440824228789093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231721055526960549485859395 347581583290440824228789093)
          ·
            refine ⟨65171546866957654542897955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347581583290440824228789093 65171546866957654542897955)
            ·
              refine ⟨97757320300436481814346933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65171546866957654542897955 97757320300436481814346933)
              ·
                refine ⟨9164748778165920170095025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97757320300436481814346933 9164748778165920170095025)
                ·
                  refine ⟨6873561583624440127571269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164748778165920170095025 6873561583624440127571269)
                  ·
                    refine ⟨1288792796929582523919613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873561583624440127571269 1288792796929582523919613)
                    ·
                      rfl

theorem cell23_7529745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_7529745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529745 prefixEnd_7529745 := by exact prefixLift 7529745
  have htrace : WordTrace (prefixWord ++ tailWord_7529745) baseStart_7529745 baseEnd_7529745 := by
    simpa [prefixWord, tailWord_7529745, baseEnd_7529745] using wordTrace_append hprefix tailTrace_7529745
  have hstable : (prefixWord ++ tailWord_7529745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529745).length < 2 ^ (prefixWord ++ tailWord_7529745).sum := by decide
  have hdescent : baseEnd_7529745 < baseStart_7529745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529746 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7529746 : Nat := 118140960795 + 7529746 * 2 ^ 59
def prefixEnd_7529746 : Nat := 4983230072969 + 3 ^ 40 * 7529746 * 2
def baseEnd_7529746 : Nat := 3866378904269402067846335

theorem tailTrace_7529746 : CollatzResearch.WordTrace tailWord_7529746 prefixEnd_7529746 3866378904269402067846335 := by
  unfold tailWord_7529746
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658099644755923769988273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183088265719349130053302061 68658099644755923769988273)
  ·
    refine ⟨51493574733566942827491205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68658099644755923769988273 51493574733566942827491205)
    ·
      refine ⟨9655045262543801780154601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51493574733566942827491205 9655045262543801780154601)
      ·
        refine ⟨7241283946907851335115951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655045262543801780154601 7241283946907851335115951)
        ·
          refine ⟨10861925920361777002673927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241283946907851335115951 10861925920361777002673927)
          ·
            refine ⟨16292888880542665504010891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10861925920361777002673927 16292888880542665504010891)
            ·
              refine ⟨24439333320813998256016337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292888880542665504010891 24439333320813998256016337)
              ·
                refine ⟨18329499990610498692012253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24439333320813998256016337 18329499990610498692012253)
                ·
                  refine ⟨6873562496478937009504595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18329499990610498692012253 6873562496478937009504595)
                  ·
                    refine ⟨10310343744718405514256893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873562496478937009504595 10310343744718405514256893)
                    ·
                      refine ⟨3866378904269402067846335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310343744718405514256893 3866378904269402067846335)
                      ·
                        rfl

theorem cell23_7529746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7529746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529746 prefixEnd_7529746 := by exact prefixLift 7529746
  have htrace : WordTrace (prefixWord ++ tailWord_7529746) baseStart_7529746 baseEnd_7529746 := by
    simpa [prefixWord, tailWord_7529746, baseEnd_7529746] using wordTrace_append hprefix tailTrace_7529746
  have hstable : (prefixWord ++ tailWord_7529746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529746).length < 2 ^ (prefixWord ++ tailWord_7529746).sum := by decide
  have hdescent : baseEnd_7529746 < baseStart_7529746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529752 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_7529752 : Nat := 118140960795 + 7529752 * 2 ^ 59
def prefixEnd_7529752 : Nat := 4983230072969 + 3 ^ 40 * 7529752 * 2
def baseEnd_7529752 : Nat := 3866381985153329044371307

theorem tailTrace_7529752 : CollatzResearch.WordTrace tailWord_7529752 prefixEnd_7529752 3866381985153329044371307 := by
  unfold tailWord_7529752
  simp only [CollatzResearch.WordTrace]
  refine ⟨137316308708500979052335755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183088411611334638736447673 137316308708500979052335755)
  ·
    refine ⟨205974463062751468578503633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137316308708500979052335755 205974463062751468578503633)
    ·
      refine ⟨154480847297063601433877725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205974463062751468578503633 154480847297063601433877725)
      ·
        refine ⟨57930317736398850537704147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154480847297063601433877725 57930317736398850537704147)
        ·
          refine ⟨86895476604598275806556221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57930317736398850537704147 86895476604598275806556221)
          ·
            refine ⟨32585803726724353427458583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86895476604598275806556221 32585803726724353427458583)
            ·
              refine ⟨48878705590086530141187875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32585803726724353427458583 48878705590086530141187875)
              ·
                refine ⟨73318058385129795211781813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48878705590086530141187875 73318058385129795211781813)
                ·
                  refine ⟨6873567973605918301104545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73318058385129795211781813 6873567973605918301104545)
                  ·
                    refine ⟨5155175980204438725828409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873567973605918301104545 5155175980204438725828409)
                    ·
                      refine ⟨3866381985153329044371307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155175980204438725828409 3866381985153329044371307)
                      ·
                        rfl

theorem cell23_7529752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_7529752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529752 prefixEnd_7529752 := by exact prefixLift 7529752
  have htrace : WordTrace (prefixWord ++ tailWord_7529752) baseStart_7529752 baseEnd_7529752 := by
    simpa [prefixWord, tailWord_7529752, baseEnd_7529752] using wordTrace_append hprefix tailTrace_7529752
  have hstable : (prefixWord ++ tailWord_7529752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529752).length < 2 ^ (prefixWord ++ tailWord_7529752).sum := by decide
  have hdescent : baseEnd_7529752 < baseStart_7529752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529755 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 3]
def baseStart_7529755 : Nat := 118140960795 + 7529755 * 2 ^ 59
def prefixEnd_7529755 : Nat := 4983230072969 + 3 ^ 40 * 7529755 * 2
def baseEnd_7529755 : Nat := 3866383525595292532633793

theorem tailTrace_7529755 : CollatzResearch.WordTrace tailWord_7529755 prefixEnd_7529755 3866383525595292532633793 := by
  unfold tailWord_7529755
  simp only [CollatzResearch.WordTrace]
  refine ⟨274632726835991089617030719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183088484557327393078020479 274632726835991089617030719)
  ·
    refine ⟨411949090253986634425546079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274632726835991089617030719 411949090253986634425546079)
    ·
      refine ⟨617923635380979951638319119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411949090253986634425546079 617923635380979951638319119)
      ·
        refine ⟨926885453071469927457478679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617923635380979951638319119 926885453071469927457478679)
        ·
          refine ⟨1390328179607204891186218019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926885453071469927457478679 1390328179607204891186218019)
          ·
            refine ⟨2085492269410807336779327029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390328179607204891186218019 2085492269410807336779327029)
            ·
              refine ⟨195514900257263187823061909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2085492269410807336779327029 195514900257263187823061909)
              ·
                refine ⟨9164760949559211929206027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195514900257263187823061909 9164760949559211929206027)
                ·
                  refine ⟨13747141424338817893809041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164760949559211929206027 13747141424338817893809041)
                  ·
                    refine ⟨10310356068254113420356781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13747141424338817893809041 10310356068254113420356781)
                    ·
                      refine ⟨3866383525595292532633793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310356068254113420356781 3866383525595292532633793)
                      ·
                        rfl

theorem cell23_7529755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 3].length) (baseStart_7529755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529755 prefixEnd_7529755 := by exact prefixLift 7529755
  have htrace : WordTrace (prefixWord ++ tailWord_7529755) baseStart_7529755 baseEnd_7529755 := by
    simpa [prefixWord, tailWord_7529755, baseEnd_7529755] using wordTrace_append hprefix tailTrace_7529755
  have hstable : (prefixWord ++ tailWord_7529755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529755).length < 2 ^ (prefixWord ++ tailWord_7529755).sum := by decide
  have hdescent : baseEnd_7529755 < baseStart_7529755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529765 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_7529765 : Nat := 118140960795 + 7529765 * 2 ^ 59
def prefixEnd_7529765 : Nat := 4983230072969 + 3 ^ 40 * 7529765 * 2
def baseEnd_7529765 : Nat := 3866388660401837493508747

theorem tailTrace_7529765 : CollatzResearch.WordTrace tailWord_7529765 prefixEnd_7529765 3866388660401837493508747 := by
  unfold tailWord_7529765
  simp only [CollatzResearch.WordTrace]
  refine ⟨274633091565954861324894749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183088727710636574216596499 274633091565954861324894749)
  ·
    refine ⟨102987409337233072996835531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274633091565954861324894749 102987409337233072996835531)
    ·
      refine ⟨154481114005849609495253297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102987409337233072996835531 154481114005849609495253297)
      ·
        refine ⟨115860835504387207121439973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154481114005849609495253297 115860835504387207121439973)
        ·
          refine ⟨21723906657072601335269995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115860835504387207121439973 21723906657072601335269995)
          ·
            refine ⟨32585859985608902002904993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21723906657072601335269995 32585859985608902002904993)
            ·
              refine ⟨24439394989206676502178745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32585859985608902002904993 24439394989206676502178745)
              ·
                refine ⟨18329546241905007376634059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24439394989206676502178745 18329546241905007376634059)
                ·
                  refine ⟨27494319362857511064951089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18329546241905007376634059 27494319362857511064951089)
                  ·
                    refine ⟨20620739522143133298713317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27494319362857511064951089 20620739522143133298713317)
                    ·
                      refine ⟨3866388660401837493508747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20620739522143133298713317 3866388660401837493508747)
                      ·
                        rfl

theorem cell23_7529765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_7529765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529765 prefixEnd_7529765 := by exact prefixLift 7529765
  have htrace : WordTrace (prefixWord ++ tailWord_7529765) baseStart_7529765 baseEnd_7529765 := by
    simpa [prefixWord, tailWord_7529765, baseEnd_7529765] using wordTrace_append hprefix tailTrace_7529765
  have hstable : (prefixWord ++ tailWord_7529765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529765).length < 2 ^ (prefixWord ++ tailWord_7529765).sum := by decide
  have hdescent : baseEnd_7529765 < baseStart_7529765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529796 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7529796 : Nat := 118140960795 + 7529796 * 2 ^ 59
def prefixEnd_7529796 : Nat := 4983230072969 + 3 ^ 40 * 7529796 * 2
def baseEnd_7529796 : Nat := 1288801526100708957407035

theorem tailTrace_7529796 : CollatzResearch.WordTrace tailWord_7529796 prefixEnd_7529796 1288801526100708957407035 := by
  unfold tailWord_7529796
  simp only [CollatzResearch.WordTrace]
  refine ⟨137317111114421276809636621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183089481485895035746182161 137317111114421276809636621)
  ·
    refine ⟨51493916667907978803613733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137317111114421276809636621 51493916667907978803613733)
    ·
      refine ⟨9655109375232746025677575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51493916667907978803613733 9655109375232746025677575)
      ·
        refine ⟨14482664062849119038516363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9655109375232746025677575 14482664062849119038516363)
        ·
          refine ⟨21723996094273678557774545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482664062849119038516363 21723996094273678557774545)
          ·
            refine ⟨16292997070705258918330909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21723996094273678557774545 16292997070705258918330909)
            ·
              refine ⟨6109873901514472094374091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16292997070705258918330909 6109873901514472094374091)
              ·
                refine ⟨9164810852271708141561137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109873901514472094374091 9164810852271708141561137)
                ·
                  refine ⟨6873608139203781106170853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164810852271708141561137 6873608139203781106170853)
                  ·
                    refine ⟨1288801526100708957407035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873608139203781106170853 1288801526100708957407035)
                    ·
                      rfl

theorem cell23_7529796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7529796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529796 prefixEnd_7529796 := by exact prefixLift 7529796
  have htrace : WordTrace (prefixWord ++ tailWord_7529796) baseStart_7529796 baseEnd_7529796 := by
    simpa [prefixWord, tailWord_7529796, baseEnd_7529796] using wordTrace_append hprefix tailTrace_7529796
  have hstable : (prefixWord ++ tailWord_7529796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529796).length < 2 ^ (prefixWord ++ tailWord_7529796).sum := by decide
  have hdescent : baseEnd_7529796 < baseStart_7529796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529802 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_7529802 : Nat := 118140960795 + 7529802 * 2 ^ 59
def prefixEnd_7529802 : Nat := 4983230072969 + 3 ^ 40 * 7529802 * 2
def baseEnd_7529802 : Nat := 3866407659186053848746077

theorem tailTrace_7529802 : CollatzResearch.WordTrace tailWord_7529802 prefixEnd_7529802 3866407659186053848746077 := by
  unfold tailWord_7529802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658610266705204160997915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183089627377880544429327773 68658610266705204160997915)
  ·
    refine ⟨102987915400057806241496873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658610266705204160997915 102987915400057806241496873)
    ·
      refine ⟨77240936550043354681122655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102987915400057806241496873 77240936550043354681122655)
      ·
        refine ⟨115861404825065032021683983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77240936550043354681122655 115861404825065032021683983)
        ·
          refine ⟨173792107237597548032525975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115861404825065032021683983 173792107237597548032525975)
          ·
            refine ⟨260688160856396322048788963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173792107237597548032525975 260688160856396322048788963)
            ·
              refine ⟨391032241284594483073183445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260688160856396322048788963 391032241284594483073183445)
              ·
                refine ⟨9164818155107683197027737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 391032241284594483073183445 9164818155107683197027737)
                ·
                  refine ⟨6873613616330762397770803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164818155107683197027737 6873613616330762397770803)
                  ·
                    refine ⟨10310420424496143596656205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873613616330762397770803 10310420424496143596656205)
                    ·
                      refine ⟨3866407659186053848746077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310420424496143596656205 3866407659186053848746077)
                      ·
                        rfl

theorem cell23_7529802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_7529802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529802 prefixEnd_7529802 := by exact prefixLift 7529802
  have htrace : WordTrace (prefixWord ++ tailWord_7529802) baseStart_7529802 baseEnd_7529802 := by
    simpa [prefixWord, tailWord_7529802, baseEnd_7529802] using wordTrace_append hprefix tailTrace_7529802
  have hstable : (prefixWord ++ tailWord_7529802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529802).length < 2 ^ (prefixWord ++ tailWord_7529802).sum := by decide
  have hdescent : baseEnd_7529802 < baseStart_7529802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529814 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7529814 : Nat := 118140960795 + 7529814 * 2 ^ 59
def prefixEnd_7529814 : Nat := 4983230072969 + 3 ^ 40 * 7529814 * 2
def baseEnd_7529814 : Nat := 3866413820953907801796023

theorem tailTrace_7529814 : CollatzResearch.WordTrace tailWord_7529814 prefixEnd_7529814 3866413820953907801796023 := by
  unfold tailWord_7529814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164679921423583918339281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183089919161851561795618997 17164679921423583918339281)
  ·
    refine ⟨12873509941067687938754461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17164679921423583918339281 12873509941067687938754461)
    ·
      refine ⟨4827566227900382977032923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12873509941067687938754461 4827566227900382977032923)
      ·
        refine ⟨7241349341850574465549385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827566227900382977032923 7241349341850574465549385)
        ·
          refine ⟨5431012006387930849162039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7241349341850574465549385 5431012006387930849162039)
          ·
            refine ⟨8146518009581896273743059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431012006387930849162039 8146518009581896273743059)
            ·
              refine ⟨12219777014372844410614589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146518009581896273743059 12219777014372844410614589)
              ·
                refine ⟨4582416380389816653980471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12219777014372844410614589 4582416380389816653980471)
                ·
                  refine ⟨6873624570584724980970707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582416380389816653980471 6873624570584724980970707)
                  ·
                    refine ⟨10310436855877087471456061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873624570584724980970707 10310436855877087471456061)
                    ·
                      refine ⟨3866413820953907801796023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310436855877087471456061 3866413820953907801796023)
                      ·
                        rfl

theorem cell23_7529814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7529814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529814 prefixEnd_7529814 := by exact prefixLift 7529814
  have htrace : WordTrace (prefixWord ++ tailWord_7529814) baseStart_7529814 baseEnd_7529814 := by
    simpa [prefixWord, tailWord_7529814, baseEnd_7529814] using wordTrace_append hprefix tailTrace_7529814
  have hstable : (prefixWord ++ tailWord_7529814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529814).length < 2 ^ (prefixWord ++ tailWord_7529814).sum := by decide
  have hdescent : baseEnd_7529814 < baseStart_7529814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529818 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_7529818 : Nat := 118140960795 + 7529818 * 2 ^ 59
def prefixEnd_7529818 : Nat := 4983230072969 + 3 ^ 40 * 7529818 * 2
def baseEnd_7529818 : Nat := 1288805291625508595382001

theorem tailTrace_7529818 : CollatzResearch.WordTrace tailWord_7529818 prefixEnd_7529818 1288805291625508595382001 := by
  unfold tailWord_7529818
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658756158690712844143527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183090016423175234251049405 68658756158690712844143527)
  ·
    refine ⟨102988134238036069266215291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658756158690712844143527 102988134238036069266215291)
    ·
      refine ⟨154482201357054103899322937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102988134238036069266215291 154482201357054103899322937)
      ·
        refine ⟨115861651017790577924492203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154482201357054103899322937 115861651017790577924492203)
        ·
          refine ⟨173792476526685866886738305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115861651017790577924492203 173792476526685866886738305)
          ·
            refine ⟨130344357395014400165053729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173792476526685866886738305 130344357395014400165053729)
            ·
              refine ⟨97758268046260800123790297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130344357395014400165053729 97758268046260800123790297)
              ·
                refine ⟨73318701034695600092842723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97758268046260800123790297 73318701034695600092842723)
                ·
                  refine ⟨109978051552043400139264085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73318701034695600092842723 109978051552043400139264085)
                  ·
                    refine ⟨1288805291625508595382001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109978051552043400139264085 1288805291625508595382001)
                    ·
                      rfl

theorem cell23_7529818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_7529818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529818 prefixEnd_7529818 := by exact prefixLift 7529818
  have htrace : WordTrace (prefixWord ++ tailWord_7529818) baseStart_7529818 baseEnd_7529818 := by
    simpa [prefixWord, tailWord_7529818, baseEnd_7529818] using wordTrace_append hprefix tailTrace_7529818
  have hstable : (prefixWord ++ tailWord_7529818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529818).length < 2 ^ (prefixWord ++ tailWord_7529818).sum := by decide
  have hdescent : baseEnd_7529818 < baseStart_7529818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529882 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_7529882 : Nat := 118140960795 + 7529882 * 2 ^ 59
def prefixEnd_7529882 : Nat := 4983230072969 + 3 ^ 40 * 7529882 * 2
def baseEnd_7529882 : Nat := 429605415293157059527301

theorem tailTrace_7529882 : CollatzResearch.WordTrace tailWord_7529882 prefixEnd_7529882 429605415293157059527301 := by
  unfold tailWord_7529882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68659339726632747576725975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183091572604353993537935933 68659339726632747576725975)
  ·
    refine ⟨102989009589949121365088963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68659339726632747576725975 102989009589949121365088963)
    ·
      refine ⟨154483514384923682047633445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102989009589949121365088963 154483514384923682047633445)
      ·
        refine ⟨28965658947173190383931271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154483514384923682047633445 28965658947173190383931271)
        ·
          refine ⟨43448488420759785575896907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28965658947173190383931271 43448488420759785575896907)
          ·
            refine ⟨65172732631139678363845361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43448488420759785575896907 65172732631139678363845361)
            ·
              refine ⟨48879549473354758772884021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65172732631139678363845361 48879549473354758772884021)
              ·
                refine ⟨4582457763127008634957877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48879549473354758772884021 4582457763127008634957877)
                ·
                  refine ⟨429605415293157059527301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582457763127008634957877 429605415293157059527301)
                  ·
                    rfl

theorem cell23_7529882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_7529882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529882 prefixEnd_7529882 := by exact prefixLift 7529882
  have htrace : WordTrace (prefixWord ++ tailWord_7529882) baseStart_7529882 baseEnd_7529882 := by
    simpa [prefixWord, tailWord_7529882, baseEnd_7529882] using wordTrace_append hprefix tailTrace_7529882
  have hstable : (prefixWord ++ tailWord_7529882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529882).length < 2 ^ (prefixWord ++ tailWord_7529882).sum := by decide
  have hdescent : baseEnd_7529882 < baseStart_7529882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529905 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7529905 : Nat := 118140960795 + 7529905 * 2 ^ 59
def prefixEnd_7529905 : Nat := 4983230072969 + 3 ^ 40 * 7529905 * 2
def baseEnd_7529905 : Nat := 3866460547693466945758103

theorem tailTrace_7529905 : CollatzResearch.WordTrace tailWord_7529905 prefixEnd_7529905 3866460547693466945758103 := by
  unfold tailWord_7529905
  simp only [CollatzResearch.WordTrace]
  refine ⟨274638197785447665234991169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183092131856965110156660779 274638197785447665234991169)
  ·
    refine ⟨205978648339085748926243377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274638197785447665234991169 205978648339085748926243377)
    ·
      refine ⟨154483986254314311694682533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205978648339085748926243377 154483986254314311694682533)
      ·
        refine ⟨28965747422683933442752975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154483986254314311694682533 28965747422683933442752975)
        ·
          refine ⟨43448621134025900164129463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28965747422683933442752975 43448621134025900164129463)
          ·
            refine ⟨65172931701038850246194195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43448621134025900164129463 65172931701038850246194195)
            ·
              refine ⟨97759397551558275369291293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65172931701038850246194195 97759397551558275369291293)
              ·
                refine ⟨36659774081834353263484235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97759397551558275369291293 36659774081834353263484235)
                ·
                  refine ⟨54989661122751529895226353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36659774081834353263484235 54989661122751529895226353)
                  ·
                    refine ⟨41242245842063647421419765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54989661122751529895226353 41242245842063647421419765)
                    ·
                      refine ⟨3866460547693466945758103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41242245842063647421419765 3866460547693466945758103)
                      ·
                        rfl

theorem cell23_7529905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7529905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529905 prefixEnd_7529905 := by exact prefixLift 7529905
  have htrace : WordTrace (prefixWord ++ tailWord_7529905) baseStart_7529905 baseEnd_7529905 := by
    simpa [prefixWord, tailWord_7529905, baseEnd_7529905] using wordTrace_append hprefix tailTrace_7529905
  have hstable : (prefixWord ++ tailWord_7529905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529905).length < 2 ^ (prefixWord ++ tailWord_7529905).sum := by decide
  have hdescent : baseEnd_7529905 < baseStart_7529905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529932 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7529932 : Nat := 118140960795 + 7529932 * 2 ^ 59
def prefixEnd_7529932 : Nat := 4983230072969 + 3 ^ 40 * 7529932 * 2
def baseEnd_7529932 : Nat := 3866474411671138340120479

theorem tailTrace_7529932 : CollatzResearch.WordTrace tailWord_7529932 prefixEnd_7529932 3866474411671138340120479 := by
  unfold tailWord_7529932
  simp only [CollatzResearch.WordTrace]
  refine ⟨137319591278174924423112025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183092788370899899230816033 137319591278174924423112025)
  ·
    refine ⟨102989693458631193317334019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137319591278174924423112025 102989693458631193317334019)
    ·
      refine ⟨154484540187946789976001029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102989693458631193317334019 154484540187946789976001029)
      ·
        refine ⟨28965851285240023120500193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154484540187946789976001029 28965851285240023120500193)
        ·
          refine ⟨21724388463930017340375145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28965851285240023120500193 21724388463930017340375145)
          ·
            refine ⟨16293291347947513005281359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21724388463930017340375145 16293291347947513005281359)
            ·
              refine ⟨24439937021921269507922039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293291347947513005281359 24439937021921269507922039)
              ·
                refine ⟨36659905532881904261883059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24439937021921269507922039 36659905532881904261883059)
                ·
                  refine ⟨54989858299322856392824589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36659905532881904261883059 54989858299322856392824589)
                  ·
                    refine ⟨20621196862246071147309221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54989858299322856392824589 20621196862246071147309221)
                    ·
                      refine ⟨3866474411671138340120479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20621196862246071147309221 3866474411671138340120479)
                      ·
                        rfl

theorem cell23_7529932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7529932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529932 prefixEnd_7529932 := by exact prefixLift 7529932
  have htrace : WordTrace (prefixWord ++ tailWord_7529932) baseStart_7529932 baseEnd_7529932 := by
    simpa [prefixWord, tailWord_7529932, baseEnd_7529932] using wordTrace_append hprefix tailTrace_7529932
  have hstable : (prefixWord ++ tailWord_7529932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529932).length < 2 ^ (prefixWord ++ tailWord_7529932).sum := by decide
  have hdescent : baseEnd_7529932 < baseStart_7529932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529945 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_7529945 : Nat := 118140960795 + 7529945 * 2 ^ 59
def prefixEnd_7529945 : Nat := 4983230072969 + 3 ^ 40 * 7529945 * 2
def baseEnd_7529945 : Nat := 3866481086919646789257919

theorem tailTrace_7529945 : CollatzResearch.WordTrace tailWord_7529945 prefixEnd_7529945 3866481086919646789257919 := by
  unfold tailWord_7529945
  simp only [CollatzResearch.WordTrace]
  refine ⟨274639656705302752066447289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183093104470201834710964859 274639656705302752066447289)
  ·
    refine ⟨205979742528977064049835467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274639656705302752066447289 205979742528977064049835467)
    ·
      refine ⟨308969613793465596074753201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205979742528977064049835467 308969613793465596074753201)
      ·
        refine ⟨231727210345099197056064901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308969613793465596074753201 231727210345099197056064901)
        ·
          refine ⟨43448851939706099448012169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231727210345099197056064901 43448851939706099448012169)
          ·
            refine ⟨32586638954779574586009127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43448851939706099448012169 32586638954779574586009127)
            ·
              refine ⟨48879958432169361879013691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32586638954779574586009127 48879958432169361879013691)
              ·
                refine ⟨73319937648254042818520537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48879958432169361879013691 73319937648254042818520537)
                ·
                  refine ⟨54989953236190532113890403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73319937648254042818520537 54989953236190532113890403)
                  ·
                    refine ⟨82484929854285798170835605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54989953236190532113890403 82484929854285798170835605)
                    ·
                      refine ⟨3866481086919646789257919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82484929854285798170835605 3866481086919646789257919)
                      ·
                        rfl

theorem cell23_7529945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_7529945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529945 prefixEnd_7529945 := by exact prefixLift 7529945
  have htrace : WordTrace (prefixWord ++ tailWord_7529945) baseStart_7529945 baseEnd_7529945 := by
    simpa [prefixWord, tailWord_7529945, baseEnd_7529945] using wordTrace_append hprefix tailTrace_7529945
  have hstable : (prefixWord ++ tailWord_7529945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529945).length < 2 ^ (prefixWord ++ tailWord_7529945).sum := by decide
  have hdescent : baseEnd_7529945 < baseStart_7529945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529949 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_7529949 : Nat := 118140960795 + 7529949 * 2 ^ 59
def prefixEnd_7529949 : Nat := 4983230072969 + 3 ^ 40 * 7529949 * 2
def baseEnd_7529949 : Nat := 3866483140842264773607901

theorem tailTrace_7529949 : CollatzResearch.WordTrace tailWord_7529949 prefixEnd_7529949 3866483140842264773607901 := by
  unfold tailWord_7529949
  simp only [CollatzResearch.WordTrace]
  refine ⟨274639802597288260749592901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183093201731525507166395267 274639802597288260749592901)
  ·
    refine ⟨51494962986991548890548669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274639802597288260749592901 51494962986991548890548669)
    ·
      refine ⟨19310611120121830833955751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51494962986991548890548669 19310611120121830833955751)
      ·
        refine ⟨28965916680182746250933627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19310611120121830833955751 28965916680182746250933627)
        ·
          refine ⟨43448875020274119376400441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28965916680182746250933627 43448875020274119376400441)
          ·
            refine ⟨32586656265205589532300331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43448875020274119376400441 32586656265205589532300331)
            ·
              refine ⟨48879984397808384298450497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32586656265205589532300331 48879984397808384298450497)
              ·
                refine ⟨36659988298356288223837873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48879984397808384298450497 36659988298356288223837873)
                ·
                  refine ⟨27494991223767216167878405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36659988298356288223837873 27494991223767216167878405)
                  ·
                    refine ⟨5155310854456353031477201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27494991223767216167878405 5155310854456353031477201)
                    ·
                      refine ⟨3866483140842264773607901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155310854456353031477201 3866483140842264773607901)
                      ·
                        rfl

theorem cell23_7529949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_7529949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529949 prefixEnd_7529949 := by exact prefixLift 7529949
  have htrace : WordTrace (prefixWord ++ tailWord_7529949) baseStart_7529949 baseEnd_7529949 := by
    simpa [prefixWord, tailWord_7529949, baseEnd_7529949] using wordTrace_append hprefix tailTrace_7529949
  have hstable : (prefixWord ++ tailWord_7529949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529949).length < 2 ^ (prefixWord ++ tailWord_7529949).sum := by decide
  have hdescent : baseEnd_7529949 < baseStart_7529949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529959 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 3, 4]
def baseStart_7529959 : Nat := 118140960795 + 7529959 * 2 ^ 59
def prefixEnd_7529959 : Nat := 4983230072969 + 3 ^ 40 * 7529959 * 2
def baseEnd_7529959 : Nat := 1288829425216269911494285

theorem tailTrace_7529959 : CollatzResearch.WordTrace tailWord_7529959 prefixEnd_7529959 1288829425216269911494285 := by
  unfold tailWord_7529959
  simp only [CollatzResearch.WordTrace]
  refine ⟨274640167327252032457456931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183093444884834688304971287 274640167327252032457456931)
  ·
    refine ⟨411960250990878048686185397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274640167327252032457456931 411960250990878048686185397)
    ·
      refine ⟨38621273530394817064329881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 411960250990878048686185397 38621273530394817064329881)
      ·
        refine ⟨28965955147796112798247411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38621273530394817064329881 28965955147796112798247411)
        ·
          refine ⟨43448932721694169197371117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28965955147796112798247411 43448932721694169197371117)
          ·
            refine ⟨16293349770635313449014169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43448932721694169197371117 16293349770635313449014169)
            ·
              refine ⟨12220012327976485086760627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16293349770635313449014169 12220012327976485086760627)
              ·
                refine ⟨18330018491964727630140941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220012327976485086760627 18330018491964727630140941)
                ·
                  refine ⟨6873756934486772861302853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18330018491964727630140941 6873756934486772861302853)
                  ·
                    refine ⟨1288829425216269911494285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873756934486772861302853 1288829425216269911494285)
                    ·
                      rfl

theorem cell23_7529959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_7529959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7529959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7529959 prefixEnd_7529959 := by exact prefixLift 7529959
  have htrace : WordTrace (prefixWord ++ tailWord_7529959) baseStart_7529959 baseEnd_7529959 := by
    simpa [prefixWord, tailWord_7529959, baseEnd_7529959] using wordTrace_append hprefix tailTrace_7529959
  have hstable : (prefixWord ++ tailWord_7529959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529959).length < 2 ^ (prefixWord ++ tailWord_7529959).sum := by decide
  have hdescent : baseEnd_7529959 < baseStart_7529959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530016 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7530016 : Nat := 118140960795 + 7530016 * 2 ^ 59
def prefixEnd_7530016 : Nat := 4983230072969 + 3 ^ 40 * 7530016 * 2
def baseEnd_7530016 : Nat := 3866517544046116011470093

theorem tailTrace_7530016 : CollatzResearch.WordTrace tailWord_7530016 prefixEnd_7530016 3866517544046116011470093 := by
  unfold tailWord_7530016
  simp only [CollatzResearch.WordTrace]
  refine ⟨137321123144022765596140951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183094830858697020794854601 137321123144022765596140951)
  ·
    refine ⟨205981684716034148394211427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137321123144022765596140951 205981684716034148394211427)
    ·
      refine ⟨308972527074051222591317141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205981684716034148394211427 308972527074051222591317141)
      ·
        refine ⟨14483087206596151058967991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308972527074051222591317141 14483087206596151058967991)
        ·
          refine ⟨21724630809894226588451987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14483087206596151058967991 21724630809894226588451987)
          ·
            refine ⟨32586946214841339882677981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21724630809894226588451987 32586946214841339882677981)
            ·
              refine ⟨12220104830565502456004243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32586946214841339882677981 12220104830565502456004243)
              ·
                refine ⟨18330157245848253684006365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220104830565502456004243 18330157245848253684006365)
                ·
                  refine ⟨6873808967193095131502387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18330157245848253684006365 6873808967193095131502387)
                  ·
                    refine ⟨10310713450789642697253581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873808967193095131502387 10310713450789642697253581)
                    ·
                      refine ⟨3866517544046116011470093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310713450789642697253581 3866517544046116011470093)
                      ·
                        rfl

theorem cell23_7530016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7530016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530016 prefixEnd_7530016 := by exact prefixLift 7530016
  have htrace : WordTrace (prefixWord ++ tailWord_7530016) baseStart_7530016 baseEnd_7530016 := by
    simpa [prefixWord, tailWord_7530016, baseEnd_7530016] using wordTrace_append hprefix tailTrace_7530016
  have hstable : (prefixWord ++ tailWord_7530016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530016).length < 2 ^ (prefixWord ++ tailWord_7530016).sum := by decide
  have hdescent : baseEnd_7530016 < baseStart_7530016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530039 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_7530039 : Nat := 118140960795 + 7530039 * 2 ^ 59
def prefixEnd_7530039 : Nat := 4983230072969 + 3 ^ 40 * 7530039 * 2
def baseEnd_7530039 : Nat := 3866529354101169421482487

theorem tailTrace_7530039 : CollatzResearch.WordTrace tailWord_7530039 prefixEnd_7530039 3866529354101169421482487 := by
  unfold tailWord_7530039
  simp only [CollatzResearch.WordTrace]
  refine ⟨274643085166962206120369171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183095390111308137413579447 274643085166962206120369171)
  ·
    refine ⟨411964627750443309180553757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274643085166962206120369171 411964627750443309180553757)
    ·
      refine ⟨154486735406416240942707659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411964627750443309180553757 154486735406416240942707659)
      ·
        refine ⟨231730103109624361414061489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154486735406416240942707659 231730103109624361414061489)
        ·
          refine ⟨173797577332218271060546117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231730103109624361414061489 173797577332218271060546117)
          ·
            refine ⟨32587045749790925823852397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173797577332218271060546117 32587045749790925823852397)
            ·
              refine ⟨12220142156171597183944649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32587045749790925823852397 12220142156171597183944649)
              ·
                refine ⟨9165106617128697887958487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12220142156171597183944649 9165106617128697887958487)
                ·
                  refine ⟨13747659925693046831937731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165106617128697887958487 13747659925693046831937731)
                  ·
                    refine ⟨20621489888539570247906597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13747659925693046831937731 20621489888539570247906597)
                    ·
                      refine ⟨3866529354101169421482487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20621489888539570247906597 3866529354101169421482487)
                      ·
                        rfl

theorem cell23_7530039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_7530039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530039 prefixEnd_7530039 := by exact prefixLift 7530039
  have htrace : WordTrace (prefixWord ++ tailWord_7530039) baseStart_7530039 baseEnd_7530039 := by
    simpa [prefixWord, tailWord_7530039, baseEnd_7530039] using wordTrace_append hprefix tailTrace_7530039
  have hstable : (prefixWord ++ tailWord_7530039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530039).length < 2 ^ (prefixWord ++ tailWord_7530039).sum := by decide
  have hdescent : baseEnd_7530039 < baseStart_7530039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530066 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_7530066 : Nat := 118140960795 + 7530066 * 2 ^ 59
def prefixEnd_7530066 : Nat := 4983230072969 + 3 ^ 40 * 7530066 * 2
def baseEnd_7530066 : Nat := 1288847739359613605281621

theorem tailTrace_7530066 : CollatzResearch.WordTrace tailWord_7530066 prefixEnd_7530066 1288847739359613605281621 := by
  unfold tailWord_7530066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68661017484466097432900513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183096046625242926487734701 68661017484466097432900513)
  ·
    refine ⟨51495763113349573074675385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68661017484466097432900513 51495763113349573074675385)
    ·
      refine ⟨38621822335012179806006539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51495763113349573074675385 38621822335012179806006539)
      ·
        refine ⟨57932733502518269709009809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38621822335012179806006539 57932733502518269709009809)
        ·
          refine ⟨43449550126888702281757357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57932733502518269709009809 43449550126888702281757357)
          ·
            refine ⟨16293581297583263355659009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43449550126888702281757357 16293581297583263355659009)
            ·
              refine ⟨12220185973187447516744257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16293581297583263355659009 12220185973187447516744257)
              ·
                refine ⟨9165139479890585637558193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12220185973187447516744257 9165139479890585637558193)
                ·
                  refine ⟨6873854609917939228168645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9165139479890585637558193 6873854609917939228168645)
                  ·
                    refine ⟨1288847739359613605281621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873854609917939228168645 1288847739359613605281621)
                    ·
                      rfl

theorem cell23_7530066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_7530066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530066 prefixEnd_7530066 := by exact prefixLift 7530066
  have htrace : WordTrace (prefixWord ++ tailWord_7530066) baseStart_7530066 baseEnd_7530066 := by
    simpa [prefixWord, tailWord_7530066, baseEnd_7530066] using wordTrace_append hprefix tailTrace_7530066
  have hstable : (prefixWord ++ tailWord_7530066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530066).length < 2 ^ (prefixWord ++ tailWord_7530066).sum := by decide
  have hdescent : baseEnd_7530066 < baseStart_7530066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530072 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_7530072 : Nat := 118140960795 + 7530072 * 2 ^ 59
def prefixEnd_7530072 : Nat := 4983230072969 + 3 ^ 40 * 7530072 * 2
def baseEnd_7530072 : Nat := 3866546298962767792369835

theorem tailTrace_7530072 : CollatzResearch.WordTrace tailWord_7530072 prefixEnd_7530072 3866546298962767792369835 := by
  unfold tailWord_7530072
  simp only [CollatzResearch.WordTrace]
  refine ⟨137322144387921326378160235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183096192517228435170880313 137322144387921326378160235)
  ·
    refine ⟨205983216581881989567240353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137322144387921326378160235 205983216581881989567240353)
    ·
      refine ⟨154487412436411492175430265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205983216581881989567240353 154487412436411492175430265)
      ·
        refine ⟨115865559327308619131572699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154487412436411492175430265 115865559327308619131572699)
        ·
          refine ⟨173798338990962928697359049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115865559327308619131572699 173798338990962928697359049)
          ·
            refine ⟨130348754243222196523019287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173798338990962928697359049 130348754243222196523019287)
            ·
              refine ⟨195523131364833294784528931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130348754243222196523019287 195523131364833294784528931)
              ·
                refine ⟨293284697047249942176793397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195523131364833294784528931 293284697047249942176793397)
                ·
                  refine ⟨27495440348179682079074381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293284697047249942176793397 27495440348179682079074381)
                  ·
                    refine ⟨10310790130567380779652893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27495440348179682079074381 10310790130567380779652893)
                    ·
                      refine ⟨3866546298962767792369835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310790130567380779652893 3866546298962767792369835)
                      ·
                        rfl

theorem cell23_7530072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_7530072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530072 prefixEnd_7530072 := by exact prefixLift 7530072
  have htrace : WordTrace (prefixWord ++ tailWord_7530072) baseStart_7530072 baseEnd_7530072 := by
    simpa [prefixWord, tailWord_7530072, baseEnd_7530072] using wordTrace_append hprefix tailTrace_7530072
  have hstable : (prefixWord ++ tailWord_7530072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530072).length < 2 ^ (prefixWord ++ tailWord_7530072).sum := by decide
  have hdescent : baseEnd_7530072 < baseStart_7530072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530140 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7530140 : Nat := 118140960795 + 7530140 * 2 ^ 59
def prefixEnd_7530140 : Nat := 4983230072969 + 3 ^ 40 * 7530140 * 2
def baseEnd_7530140 : Nat := 3866581215647273526319523

theorem tailTrace_7530140 : CollatzResearch.WordTrace tailWord_7530140 prefixEnd_7530140 3866581215647273526319523 := by
  unfold tailWord_7530140
  simp only [CollatzResearch.WordTrace]
  refine ⟨137323384469798150184897937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183097845959730866913197249 137323384469798150184897937)
  ·
    refine ⟨102992538352348612638673453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137323384469798150184897937 102992538352348612638673453)
    ·
      refine ⟨38622201882130729739502545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102992538352348612638673453 38622201882130729739502545)
      ·
        refine ⟨28966651411598047304626909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38622201882130729739502545 28966651411598047304626909)
        ·
          refine ⟨10862494279349267739235091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28966651411598047304626909 10862494279349267739235091)
          ·
            refine ⟨16293741419023901608852637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862494279349267739235091 16293741419023901608852637)
            ·
              refine ⟨6110153032133963103319739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16293741419023901608852637 6110153032133963103319739)
              ·
                refine ⟨9165229548200944654979609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110153032133963103319739 9165229548200944654979609)
                ·
                  refine ⟨6873922161150708491234707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9165229548200944654979609 6873922161150708491234707)
                  ·
                    refine ⟨10310883241726062736852061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873922161150708491234707 10310883241726062736852061)
                    ·
                      refine ⟨3866581215647273526319523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10310883241726062736852061 3866581215647273526319523)
                      ·
                        rfl

theorem cell23_7530140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7530140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530140 prefixEnd_7530140 := by exact prefixLift 7530140
  have htrace : WordTrace (prefixWord ++ tailWord_7530140) baseStart_7530140 baseEnd_7530140 := by
    simpa [prefixWord, tailWord_7530140, baseEnd_7530140] using wordTrace_append hprefix tailTrace_7530140
  have hstable : (prefixWord ++ tailWord_7530140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530140).length < 2 ^ (prefixWord ++ tailWord_7530140).sum := by decide
  have hdescent : baseEnd_7530140 < baseStart_7530140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530166 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7530166 : Nat := 118140960795 + 7530166 * 2 ^ 59
def prefixEnd_7530166 : Nat := 4983230072969 + 3 ^ 40 * 7530166 * 2
def baseEnd_7530166 : Nat := 3866594566144290424594403

theorem tailTrace_7530166 : CollatzResearch.WordTrace tailWord_7530166 prefixEnd_7530166 3866594566144290424594403 := by
  unfold tailWord_7530166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17165482327343881675640147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183098478158334737873494901 17165482327343881675640147)
  ·
    refine ⟨25748223491015822513460221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17165482327343881675640147 25748223491015822513460221)
    ·
      refine ⟨9655583809130933442547583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25748223491015822513460221 9655583809130933442547583)
      ·
        refine ⟨14483375713696400163821375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9655583809130933442547583 14483375713696400163821375)
        ·
          refine ⟨21725063570544600245732063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14483375713696400163821375 21725063570544600245732063)
          ·
            refine ⟨32587595355816900368598095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21725063570544600245732063 32587595355816900368598095)
            ·
              refine ⟨48881393033725350552897143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32587595355816900368598095 48881393033725350552897143)
              ·
                refine ⟨73322089550588025829345715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48881393033725350552897143 73322089550588025829345715)
                ·
                  refine ⟨109983134325882038744018573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73322089550588025829345715 109983134325882038744018573)
                  ·
                    refine ⟨41243675372205764529006965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109983134325882038744018573 41243675372205764529006965)
                    ·
                      refine ⟨3866594566144290424594403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41243675372205764529006965 3866594566144290424594403)
                      ·
                        rfl

theorem cell23_7530166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7530166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530166 prefixEnd_7530166 := by exact prefixLift 7530166
  have htrace : WordTrace (prefixWord ++ tailWord_7530166) baseStart_7530166 baseEnd_7530166 := by
    simpa [prefixWord, tailWord_7530166, baseEnd_7530166] using wordTrace_append hprefix tailTrace_7530166
  have hstable : (prefixWord ++ tailWord_7530166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530166).length < 2 ^ (prefixWord ++ tailWord_7530166).sum := by decide
  have hdescent : baseEnd_7530166 < baseStart_7530166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530186 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_7530186 : Nat := 118140960795 + 7530186 * 2 ^ 59
def prefixEnd_7530186 : Nat := 4983230072969 + 3 ^ 40 * 7530186 * 2
def baseEnd_7530186 : Nat := 429622759528597816260479

theorem tailTrace_7530186 : CollatzResearch.WordTrace tailWord_7530186 prefixEnd_7530186 429622759528597816260479 := by
  unfold tailWord_7530186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68662111674357412556492603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183098964464953100150646941 68662111674357412556492603)
  ·
    refine ⟨102993167511536118834738905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68662111674357412556492603 102993167511536118834738905)
    ·
      refine ⟨77244875633652089126054179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102993167511536118834738905 77244875633652089126054179)
      ·
        refine ⟨115867313450478133689081269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77244875633652089126054179 115867313450478133689081269)
        ·
          refine ⟨10862560635982325033351369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115867313450478133689081269 10862560635982325033351369)
          ·
            refine ⟨8146920476986743775013527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10862560635982325033351369 8146920476986743775013527)
            ·
              refine ⟨12220380715480115662520291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146920476986743775013527 12220380715480115662520291)
              ·
                refine ⟨18330571073220173493780437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220380715480115662520291 18330571073220173493780437)
                ·
                  refine ⟨429622759528597816260479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18330571073220173493780437 429622759528597816260479)
                  ·
                    rfl

theorem cell23_7530186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_7530186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530186 prefixEnd_7530186 := by exact prefixLift 7530186
  have htrace : WordTrace (prefixWord ++ tailWord_7530186) baseStart_7530186 baseEnd_7530186 := by
    simpa [prefixWord, tailWord_7530186, baseEnd_7530186] using wordTrace_append hprefix tailTrace_7530186
  have hstable : (prefixWord ++ tailWord_7530186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530186).length < 2 ^ (prefixWord ++ tailWord_7530186).sum := by decide
  have hdescent : baseEnd_7530186 < baseStart_7530186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530216 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_7530216 : Nat := 118140960795 + 7530216 * 2 ^ 59
def prefixEnd_7530216 : Nat := 4983230072969 + 3 ^ 40 * 7530216 * 2
def baseEnd_7530216 : Nat := 1288873413392338409656391

theorem tailTrace_7530216 : CollatzResearch.WordTrace tailWord_7530216 prefixEnd_7530216 1288873413392338409656391 := by
  unfold tailWord_7530216
  simp only [CollatzResearch.WordTrace]
  refine ⟨137324770443660482674781251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183099693924880643566375001 137324770443660482674781251)
  ·
    refine ⟨205987155665490724012171877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137324770443660482674781251 205987155665490724012171877)
    ·
      refine ⟨38622591687279510752282227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205987155665490724012171877 38622591687279510752282227)
      ·
        refine ⟨57933887530919266128423341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38622591687279510752282227 57933887530919266128423341)
        ·
          refine ⟨21725207824094724798158753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57933887530919266128423341 21725207824094724798158753)
          ·
            refine ⟨16293905868071043598619065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21725207824094724798158753 16293905868071043598619065)
            ·
              refine ⟨12220429401053282698964299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16293905868071043598619065 12220429401053282698964299)
              ·
                refine ⟨18330644101579924048446449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220429401053282698964299 18330644101579924048446449)
                ·
                  refine ⟨13747983076184943036334837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18330644101579924048446449 13747983076184943036334837)
                  ·
                    refine ⟨1288873413392338409656391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13747983076184943036334837 1288873413392338409656391)
                    ·
                      rfl

theorem cell23_7530216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_7530216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530216 prefixEnd_7530216 := by exact prefixLift 7530216
  have htrace : WordTrace (prefixWord ++ tailWord_7530216) baseStart_7530216 baseEnd_7530216 := by
    simpa [prefixWord, tailWord_7530216, baseEnd_7530216] using wordTrace_append hprefix tailTrace_7530216
  have hstable : (prefixWord ++ tailWord_7530216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530216).length < 2 ^ (prefixWord ++ tailWord_7530216).sum := by decide
  have hdescent : baseEnd_7530216 < baseStart_7530216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530219 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4]
def baseStart_7530219 : Nat := 118140960795 + 7530219 * 2 ^ 59
def prefixEnd_7530219 : Nat := 4983230072969 + 3 ^ 40 * 7530219 * 2
def baseEnd_7530219 : Nat := 3866621780618978717231659

theorem tailTrace_7530219 : CollatzResearch.WordTrace tailWord_7530219 prefixEnd_7530219 3866621780618978717231659 := by
  unfold tailWord_7530219
  simp only [CollatzResearch.WordTrace]
  refine ⟨274649650306310096861921711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183099766870873397907947807 274649650306310096861921711)
  ·
    refine ⟨411974475459465145292882567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274649650306310096861921711 411974475459465145292882567)
    ·
      refine ⟨617961713189197717939323851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411974475459465145292882567 617961713189197717939323851)
      ·
        refine ⟨926942569783796576908985777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617961713189197717939323851 926942569783796576908985777)
        ·
          refine ⟨695206927337847432681739333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926942569783796576908985777 695206927337847432681739333)
          ·
            refine ⟨130351298875846393627826125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695206927337847432681739333 130351298875846393627826125)
            ·
              refine ⟨48881737078442397610434797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130351298875846393627826125 48881737078442397610434797)
              ·
                refine ⟨18330651404415899103913049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48881737078442397610434797 18330651404415899103913049)
                ·
                  refine ⟨13747988553311924327934787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18330651404415899103913049 13747988553311924327934787)
                  ·
                    refine ⟨20621982829967886491902181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13747988553311924327934787 20621982829967886491902181)
                    ·
                      refine ⟨3866621780618978717231659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20621982829967886491902181 3866621780618978717231659)
                      ·
                        rfl

theorem cell23_7530219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4].length) (baseStart_7530219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530219 prefixEnd_7530219 := by exact prefixLift 7530219
  have htrace : WordTrace (prefixWord ++ tailWord_7530219) baseStart_7530219 baseEnd_7530219 := by
    simpa [prefixWord, tailWord_7530219, baseEnd_7530219] using wordTrace_append hprefix tailTrace_7530219
  have hstable : (prefixWord ++ tailWord_7530219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530219).length < 2 ^ (prefixWord ++ tailWord_7530219).sum := by decide
  have hdescent : baseEnd_7530219 < baseStart_7530219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530236 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_7530236 : Nat := 118140960795 + 7530236 * 2 ^ 59
def prefixEnd_7530236 : Nat := 4983230072969 + 3 ^ 40 * 7530236 * 2
def baseEnd_7530236 : Nat := 3866630509790105150719081

theorem tailTrace_7530236 : CollatzResearch.WordTrace tailWord_7530236 prefixEnd_7530236 3866630509790105150719081 := by
  unfold tailWord_7530236
  simp only [CollatzResearch.WordTrace]
  refine ⟨137325135173624254382645281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183100180231499005843527041 137325135173624254382645281)
  ·
    refine ⟨102993851380218190786983961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137325135173624254382645281 102993851380218190786983961)
    ·
      refine ⟨77245388535163643090237971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102993851380218190786983961 77245388535163643090237971)
      ·
        refine ⟨115868082802745464635356957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77245388535163643090237971 115868082802745464635356957)
        ·
          refine ⟨43450531051029549238258859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115868082802745464635356957 43450531051029549238258859)
          ·
            refine ⟨65175796576544323857388289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43450531051029549238258859 65175796576544323857388289)
            ·
              refine ⟨48881847432408242893041217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65175796576544323857388289 48881847432408242893041217)
              ·
                refine ⟨36661385574306182169780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48881847432408242893041217 36661385574306182169780913)
                ·
                  refine ⟨27496039180729636627335685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36661385574306182169780913 27496039180729636627335685)
                  ·
                    refine ⟨5155507346386806867625441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27496039180729636627335685 5155507346386806867625441)
                    ·
                      refine ⟨3866630509790105150719081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5155507346386806867625441 3866630509790105150719081)
                      ·
                        rfl

theorem cell23_7530236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_7530236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530236 prefixEnd_7530236 := by exact prefixLift 7530236
  have htrace : WordTrace (prefixWord ++ tailWord_7530236) baseStart_7530236 baseEnd_7530236 := by
    simpa [prefixWord, tailWord_7530236, baseEnd_7530236] using wordTrace_append hprefix tailTrace_7530236
  have hstable : (prefixWord ++ tailWord_7530236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530236).length < 2 ^ (prefixWord ++ tailWord_7530236).sum := by decide
  have hdescent : baseEnd_7530236 < baseStart_7530236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530270 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7530270 : Nat := 118140960795 + 7530270 * 2 ^ 59
def prefixEnd_7530270 : Nat := 4983230072969 + 3 ^ 40 * 7530270 * 2
def baseEnd_7530270 : Nat := 3866647968132358017693925

theorem tailTrace_7530270 : CollatzResearch.WordTrace tailWord_7530270 prefixEnd_7530270 3866647968132358017693925 := by
  unfold tailWord_7530270
  simp only [CollatzResearch.WordTrace]
  refine ⟨34331438803640666571503533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183101006952750221714685509 34331438803640666571503533)
  ·
    refine ⟨12874289551365249964313825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34331438803640666571503533 12874289551365249964313825)
    ·
      refine ⟨9655717163523937473235369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12874289551365249964313825 9655717163523937473235369)
      ·
        refine ⟨7241787872642953104926527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655717163523937473235369 7241787872642953104926527)
        ·
          refine ⟨10862681808964429657389791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241787872642953104926527 10862681808964429657389791)
          ·
            refine ⟨16294022713446644486084687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862681808964429657389791 16294022713446644486084687)
            ·
              refine ⟨24441034070169966729127031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16294022713446644486084687 24441034070169966729127031)
              ·
                refine ⟨36661551105254950093690547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24441034070169966729127031 36661551105254950093690547)
                ·
                  refine ⟨54992326657882425140535821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36661551105254950093690547 54992326657882425140535821)
                  ·
                    refine ⟨20622122496705909427700933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54992326657882425140535821 20622122496705909427700933)
                    ·
                      refine ⟨3866647968132358017693925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20622122496705909427700933 3866647968132358017693925)
                      ·
                        rfl

theorem cell23_7530270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7530270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530270 prefixEnd_7530270 := by exact prefixLift 7530270
  have htrace : WordTrace (prefixWord ++ tailWord_7530270) baseStart_7530270 baseEnd_7530270 := by
    simpa [prefixWord, tailWord_7530270, baseEnd_7530270] using wordTrace_append hprefix tailTrace_7530270
  have hstable : (prefixWord ++ tailWord_7530270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530270).length < 2 ^ (prefixWord ++ tailWord_7530270).sum := by decide
  have hdescent : baseEnd_7530270 < baseStart_7530270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530273 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7530273 : Nat := 118140960795 + 7530273 * 2 ^ 59
def prefixEnd_7530273 : Nat := 4983230072969 + 3 ^ 40 * 7530273 * 2
def baseEnd_7530273 : Nat := 3866649508574321505956411

theorem tailTrace_7530273 : CollatzResearch.WordTrace tailWord_7530273 prefixEnd_7530273 3866649508574321505956411 := by
  unfold tailWord_7530273
  simp only [CollatzResearch.WordTrace]
  refine ⟨274651619848114464084387473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183101079898742976056258315 274651619848114464084387473)
  ·
    refine ⟨205988714886085848063290605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274651619848114464084387473 205988714886085848063290605)
    ·
      refine ⟨77245768082282193023733977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205988714886085848063290605 77245768082282193023733977)
      ·
        refine ⟨57934326061711644767800483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77245768082282193023733977 57934326061711644767800483)
        ·
          refine ⟨86901489092567467151700725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57934326061711644767800483 86901489092567467151700725)
          ·
            refine ⟨8147014602428200045471943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86901489092567467151700725 8147014602428200045471943)
            ·
              refine ⟨12220521903642300068207915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8147014602428200045471943 12220521903642300068207915)
              ·
                refine ⟨18330782855463450102311873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220521903642300068207915 18330782855463450102311873)
                ·
                  refine ⟨13748087141597587576733905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18330782855463450102311873 13748087141597587576733905)
                  ·
                    refine ⟨10311065356198190682550429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13748087141597587576733905 10311065356198190682550429)
                    ·
                      refine ⟨3866649508574321505956411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10311065356198190682550429 3866649508574321505956411)
                      ·
                        rfl

theorem cell23_7530273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7530273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530273 prefixEnd_7530273 := by exact prefixLift 7530273
  have htrace : WordTrace (prefixWord ++ tailWord_7530273) baseStart_7530273 baseEnd_7530273 := by
    simpa [prefixWord, tailWord_7530273, baseEnd_7530273] using wordTrace_append hprefix tailTrace_7530273
  have hstable : (prefixWord ++ tailWord_7530273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530273).length < 2 ^ (prefixWord ++ tailWord_7530273).sum := by decide
  have hdescent : baseEnd_7530273 < baseStart_7530273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7530280 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 1, 4]
def baseStart_7530280 : Nat := 118140960795 + 7530280 * 2 ^ 59
def prefixEnd_7530280 : Nat := 4983230072969 + 3 ^ 40 * 7530280 * 2
def baseEnd_7530280 : Nat := 1288884367646300992856293

theorem tailTrace_7530280 : CollatzResearch.WordTrace tailWord_7530280 prefixEnd_7530280 1288884367646300992856293 := by
  unfold tailWord_7530280
  simp only [CollatzResearch.WordTrace]
  refine ⟨137325937579544552139946147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183101250106059402853261529 137325937579544552139946147)
  ·
    refine ⟨205988906369316828209919221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137325937579544552139946147 205988906369316828209919221)
    ·
      refine ⟨19311459972123452644679927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205988906369316828209919221 19311459972123452644679927)
      ·
        refine ⟨28967189958185178967019891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19311459972123452644679927 28967189958185178967019891)
        ·
          refine ⟨43450784937277768450529837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28967189958185178967019891 43450784937277768450529837)
          ·
            refine ⟨16294044351479163168948689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43450784937277768450529837 16294044351479163168948689)
            ·
              refine ⟨12220533263609372376711517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16294044351479163168948689 12220533263609372376711517)
              ·
                refine ⟨4582699973853514641266819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12220533263609372376711517 4582699973853514641266819)
                ·
                  refine ⟨6874049960780271961900229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582699973853514641266819 6874049960780271961900229)
                  ·
                    refine ⟨1288884367646300992856293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874049960780271961900229 1288884367646300992856293)
                    ·
                      rfl

theorem cell23_7530280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_7530280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7530280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7530280 prefixEnd_7530280 := by exact prefixLift 7530280
  have htrace : WordTrace (prefixWord ++ tailWord_7530280) baseStart_7530280 baseEnd_7530280 := by
    simpa [prefixWord, tailWord_7530280, baseEnd_7530280] using wordTrace_append hprefix tailTrace_7530280
  have hstable : (prefixWord ++ tailWord_7530280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7530280).length < 2 ^ (prefixWord ++ tailWord_7530280).sum := by decide
  have hdescent : baseEnd_7530280 < baseStart_7530280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7530280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
