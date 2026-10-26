import V185TrunkScan23Chunk1301

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7711734 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_7711734 : Nat := 118140960795 + 7711734 * 2 ^ 59
def prefixEnd_7711734 : Nat := 4983230072969 + 3 ^ 40 * 7711734 * 2
def baseEnd_7711734 : Nat := 1319942073873278679653129

theorem tailTrace_7711734 : CollatzResearch.WordTrace tailWord_7711734 prefixEnd_7711734 1319942073873278679653129 := by
  unfold tailWord_7711734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579377890232015759741391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187513364162474834770574837 17579377890232015759741391)
  ·
    refine ⟨26369066835348023639612087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579377890232015759741391 26369066835348023639612087)
    ·
      refine ⟨39553600253022035459418131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26369066835348023639612087 39553600253022035459418131)
      ·
        refine ⟨59330400379533053189127197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39553600253022035459418131 59330400379533053189127197)
        ·
          refine ⟨22248900142324894945922699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59330400379533053189127197 22248900142324894945922699)
          ·
            refine ⟨33373350213487342418884049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22248900142324894945922699 33373350213487342418884049)
            ·
              refine ⟨25030012660115506814163037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33373350213487342418884049 25030012660115506814163037)
              ·
                refine ⟨9386254747543315055311139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25030012660115506814163037 9386254747543315055311139)
                ·
                  refine ⟨14079382121314972582966709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9386254747543315055311139 14079382121314972582966709)
                  ·
                    refine ⟨1319942073873278679653129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14079382121314972582966709 1319942073873278679653129)
                    ·
                      rfl

theorem cell23_7711734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_7711734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711734 prefixEnd_7711734 := by exact prefixLift 7711734
  have htrace : WordTrace (prefixWord ++ tailWord_7711734) baseStart_7711734 baseEnd_7711734 := by
    simpa [prefixWord, tailWord_7711734, baseEnd_7711734] using wordTrace_append hprefix tailTrace_7711734
  have hstable : (prefixWord ++ tailWord_7711734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711734).length < 2 ^ (prefixWord ++ tailWord_7711734).sum := by decide
  have hdescent : baseEnd_7711734 < baseStart_7711734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711737 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_7711737 : Nat := 118140960795 + 7711737 * 2 ^ 59
def prefixEnd_7711737 : Nat := 4983230072969 + 3 ^ 40 * 7711737 * 2
def baseEnd_7711737 : Nat := 3959827762061799527221873

theorem tailTrace_7711737 : CollatzResearch.WordTrace tailWord_7711737 prefixEnd_7711737 3959827762061799527221873 := by
  unfold tailWord_7711737
  simp only [CollatzResearch.WordTrace]
  refine ⟨281270155662701383668221465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187513437108467589112147643 281270155662701383668221465)
  ·
    refine ⟨210952616747026037751166099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281270155662701383668221465 210952616747026037751166099)
    ·
      refine ⟨316428925120539056626749149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210952616747026037751166099 316428925120539056626749149)
      ·
        refine ⟨118660846920202146235030931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316428925120539056626749149 118660846920202146235030931)
        ·
          refine ⟨177991270380303219352546397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118660846920202146235030931 177991270380303219352546397)
          ·
            refine ⟨66746726392613707257204899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177991270380303219352546397 66746726392613707257204899)
            ·
              refine ⟨100120089588920560885807349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66746726392613707257204899 100120089588920560885807349)
              ·
                refine ⟨9386258398961302583044439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100120089588920560885807349 9386258398961302583044439)
                ·
                  refine ⟨14079387598441953874566659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9386258398961302583044439 14079387598441953874566659)
                  ·
                    refine ⟨21119081397662930811849989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14079387598441953874566659 21119081397662930811849989)
                    ·
                      refine ⟨3959827762061799527221873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21119081397662930811849989 3959827762061799527221873)
                      ·
                        rfl

theorem cell23_7711737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_7711737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711737 prefixEnd_7711737 := by exact prefixLift 7711737
  have htrace : WordTrace (prefixWord ++ tailWord_7711737) baseStart_7711737 baseEnd_7711737 := by
    simpa [prefixWord, tailWord_7711737, baseEnd_7711737] using wordTrace_append hprefix tailTrace_7711737
  have hstable : (prefixWord ++ tailWord_7711737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711737).length < 2 ^ (prefixWord ++ tailWord_7711737).sum := by decide
  have hdescent : baseEnd_7711737 < baseStart_7711737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711767 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7711767 : Nat := 118140960795 + 7711767 * 2 ^ 59
def prefixEnd_7711767 : Nat := 4983230072969 + 3 ^ 40 * 7711767 * 2
def baseEnd_7711767 : Nat := 3959843166481434409846735

theorem tailTrace_7711767 : CollatzResearch.WordTrace tailWord_7711767 prefixEnd_7711767 3959843166481434409846735 := by
  unfold tailWord_7711767
  simp only [CollatzResearch.WordTrace]
  refine ⟨281271249852592698791813555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187514166568395132527875703 281271249852592698791813555)
  ·
    refine ⟨421906874778889048187720333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281271249852592698791813555 421906874778889048187720333)
    ·
      refine ⟨158215078042083393070395125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421906874778889048187720333 158215078042083393070395125)
      ·
        refine ⟨14832663566445318100349543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158215078042083393070395125 14832663566445318100349543)
        ·
          refine ⟨22248995349667977150524315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832663566445318100349543 22248995349667977150524315)
          ·
            refine ⟨33373493024501965725786473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22248995349667977150524315 33373493024501965725786473)
            ·
              refine ⟨25030119768376474294339855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33373493024501965725786473 25030119768376474294339855)
              ·
                refine ⟨37545179652564711441509783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25030119768376474294339855 37545179652564711441509783)
                ·
                  refine ⟨56317769478847067162264675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37545179652564711441509783 56317769478847067162264675)
                  ·
                    refine ⟨84476654218270600743397013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56317769478847067162264675 84476654218270600743397013)
                    ·
                      refine ⟨3959843166481434409846735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84476654218270600743397013 3959843166481434409846735)
                      ·
                        rfl

theorem cell23_7711767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7711767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711767 prefixEnd_7711767 := by exact prefixLift 7711767
  have htrace : WordTrace (prefixWord ++ tailWord_7711767) baseStart_7711767 baseEnd_7711767 := by
    simpa [prefixWord, tailWord_7711767, baseEnd_7711767] using wordTrace_append hprefix tailTrace_7711767
  have hstable : (prefixWord ++ tailWord_7711767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711767).length < 2 ^ (prefixWord ++ tailWord_7711767).sum := by decide
  have hdescent : baseEnd_7711767 < baseStart_7711767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711787 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3]
def baseStart_7711787 : Nat := 118140960795 + 7711787 * 2 ^ 59
def prefixEnd_7711787 : Nat := 4983230072969 + 3 ^ 40 * 7711787 * 2
def baseEnd_7711787 : Nat := 3959853436094524331596643

theorem tailTrace_7711787 : CollatzResearch.WordTrace tailWord_7711787 prefixEnd_7711787 3959853436094524331596643 := by
  unfold tailWord_7711787
  simp only [CollatzResearch.WordTrace]
  refine ⟨281271979312520242207541615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187514652875013494805027743 281271979312520242207541615)
  ·
    refine ⟨421907968968780363311312423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281271979312520242207541615 421907968968780363311312423)
    ·
      refine ⟨632861953453170544966968635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421907968968780363311312423 632861953453170544966968635)
      ·
        refine ⟨949292930179755817450452953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632861953453170544966968635 949292930179755817450452953)
        ·
          refine ⟨711969697634816863087839715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949292930179755817450452953 711969697634816863087839715)
          ·
            refine ⟨1067954546452225294631759573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711969697634816863087839715 1067954546452225294631759573)
            ·
              refine ⟨25030184682474030342931865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1067954546452225294631759573 25030184682474030342931865)
              ·
                refine ⟨18772638511855522757198899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25030184682474030342931865 18772638511855522757198899)
                ·
                  refine ⟨28158957767783284135798349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18772638511855522757198899 28158957767783284135798349)
                  ·
                    refine ⟨10559609162918731550924381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28158957767783284135798349 10559609162918731550924381)
                    ·
                      refine ⟨3959853436094524331596643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559609162918731550924381 3959853436094524331596643)
                      ·
                        rfl

theorem cell23_7711787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3].length) (baseStart_7711787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711787 prefixEnd_7711787 := by exact prefixLift 7711787
  have htrace : WordTrace (prefixWord ++ tailWord_7711787) baseStart_7711787 baseEnd_7711787 := by
    simpa [prefixWord, tailWord_7711787, baseEnd_7711787] using wordTrace_append hprefix tailTrace_7711787
  have hstable : (prefixWord ++ tailWord_7711787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711787).length < 2 ^ (prefixWord ++ tailWord_7711787).sum := by decide
  have hdescent : baseEnd_7711787 < baseStart_7711787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711805 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7711805 : Nat := 118140960795 + 7711805 * 2 ^ 59
def prefixEnd_7711805 : Nat := 4983230072969 + 3 ^ 40 * 7711805 * 2
def baseEnd_7711805 : Nat := 3959862678746305261171561

theorem tailTrace_7711805 : CollatzResearch.WordTrace tailWord_7711805 prefixEnd_7711805 3959862678746305261171561 := by
  unfold tailWord_7711805
  simp only [CollatzResearch.WordTrace]
  refine ⟨281272635826455031281696869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187515090550970020854464579 281272635826455031281696869)
  ·
    refine ⟨52738619217460318365318163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281272635826455031281696869 52738619217460318365318163)
    ·
      refine ⟨79107928826190477547977245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52738619217460318365318163 79107928826190477547977245)
      ·
        refine ⟨29665473309821429080491467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79107928826190477547977245 29665473309821429080491467)
        ·
          refine ⟨44498209964732143620737201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29665473309821429080491467 44498209964732143620737201)
          ·
            refine ⟨33373657473549107715552901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44498209964732143620737201 33373657473549107715552901)
            ·
              refine ⟨6257560776290457696666169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33373657473549107715552901 6257560776290457696666169)
              ·
                refine ⟨4693170582217843272499627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257560776290457696666169 4693170582217843272499627)
                ·
                  refine ⟨7039755873326764908749441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693170582217843272499627 7039755873326764908749441)
                  ·
                    refine ⟨5279816904995073681562081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7039755873326764908749441 5279816904995073681562081)
                    ·
                      refine ⟨3959862678746305261171561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279816904995073681562081 3959862678746305261171561)
                      ·
                        rfl

theorem cell23_7711805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7711805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711805 prefixEnd_7711805 := by exact prefixLift 7711805
  have htrace : WordTrace (prefixWord ++ tailWord_7711805) baseStart_7711805 baseEnd_7711805 := by
    simpa [prefixWord, tailWord_7711805, baseEnd_7711805] using wordTrace_append hprefix tailTrace_7711805
  have hstable : (prefixWord ++ tailWord_7711805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711805).length < 2 ^ (prefixWord ++ tailWord_7711805).sum := by decide
  have hdescent : baseEnd_7711805 < baseStart_7711805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711821 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_7711821 : Nat := 118140960795 + 7711821 * 2 ^ 59
def prefixEnd_7711821 : Nat := 4983230072969 + 3 ^ 40 * 7711821 * 2
def baseEnd_7711821 : Nat := 3959870894436777198571487

theorem tailTrace_7711821 : CollatzResearch.WordTrace tailWord_7711821 prefixEnd_7711821 3959870894436777198571487 := by
  unfold tailWord_7711821
  simp only [CollatzResearch.WordTrace]
  refine ⟨281273219394397066014279317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187515479596264710676186211 281273219394397066014279317)
  ·
    refine ⟨13184682159112362469419343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281273219394397066014279317 13184682159112362469419343)
    ·
      refine ⟨19777023238668543704129015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13184682159112362469419343 19777023238668543704129015)
      ·
        refine ⟨29665534858002815556193523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19777023238668543704129015 29665534858002815556193523)
        ·
          refine ⟨44498302287004223334290285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29665534858002815556193523 44498302287004223334290285)
          ·
            refine ⟨16686863357626583750358857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44498302287004223334290285 16686863357626583750358857)
            ·
              refine ⟨12515147518219937812769143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16686863357626583750358857 12515147518219937812769143)
              ·
                refine ⟨18772721277329906719153715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12515147518219937812769143 18772721277329906719153715)
                ·
                  refine ⟨28159081915994860078730573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18772721277329906719153715 28159081915994860078730573)
                  ·
                    refine ⟨10559655718498072529523965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28159081915994860078730573 10559655718498072529523965)
                    ·
                      refine ⟨3959870894436777198571487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559655718498072529523965 3959870894436777198571487)
                      ·
                        rfl

theorem cell23_7711821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_7711821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711821 prefixEnd_7711821 := by exact prefixLift 7711821
  have htrace : WordTrace (prefixWord ++ tailWord_7711821) baseStart_7711821 baseEnd_7711821 := by
    simpa [prefixWord, tailWord_7711821, baseEnd_7711821] using wordTrace_append hprefix tailTrace_7711821
  have hstable : (prefixWord ++ tailWord_7711821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711821).length < 2 ^ (prefixWord ++ tailWord_7711821).sum := by decide
  have hdescent : baseEnd_7711821 < baseStart_7711821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711838 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7711838 : Nat := 118140960795 + 7711838 * 2 ^ 59
def prefixEnd_7711838 : Nat := 4983230072969 + 3 ^ 40 * 7711838 * 2
def baseEnd_7711838 : Nat := 3959879623607903632058909

theorem tailTrace_7711838 : CollatzResearch.WordTrace tailWord_7711838 prefixEnd_7711838 3959879623607903632058909 := by
  unfold tailWord_7711838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35159229929416934739706021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187515892956890318611765445 35159229929416934739706021)
  ·
    refine ⟨6592355611765675263694879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35159229929416934739706021 6592355611765675263694879)
    ·
      refine ⟨9888533417648512895542319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6592355611765675263694879 9888533417648512895542319)
      ·
        refine ⟨14832800126472769343313479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9888533417648512895542319 14832800126472769343313479)
        ·
          refine ⟨22249200189709154014970219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832800126472769343313479 22249200189709154014970219)
          ·
            refine ⟨33373800284563731022455329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22249200189709154014970219 33373800284563731022455329)
            ·
              refine ⟨25030350213422798266841497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33373800284563731022455329 25030350213422798266841497)
              ·
                refine ⟨18772762660067098700131123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25030350213422798266841497 18772762660067098700131123)
                ·
                  refine ⟨28159143990100648050196685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18772762660067098700131123 28159143990100648050196685)
                  ·
                    refine ⟨10559678996287743018823757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28159143990100648050196685 10559678996287743018823757)
                    ·
                      refine ⟨3959879623607903632058909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559678996287743018823757 3959879623607903632058909)
                      ·
                        rfl

theorem cell23_7711838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7711838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711838 prefixEnd_7711838 := by exact prefixLift 7711838
  have htrace : WordTrace (prefixWord ++ tailWord_7711838) baseStart_7711838 baseEnd_7711838 := by
    simpa [prefixWord, tailWord_7711838, baseEnd_7711838] using wordTrace_append hprefix tailTrace_7711838
  have hstable : (prefixWord ++ tailWord_7711838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711838).length < 2 ^ (prefixWord ++ tailWord_7711838).sum := by decide
  have hdescent : baseEnd_7711838 < baseStart_7711838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711944 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_7711944 : Nat := 118140960795 + 7711944 * 2 ^ 59
def prefixEnd_7711944 : Nat := 4983230072969 + 3 ^ 40 * 7711944 * 2
def baseEnd_7711944 : Nat := 1319978017519093405777807

theorem tailTrace_7711944 : CollatzResearch.WordTrace tailWord_7711944 prefixEnd_7711944 1319978017519093405777807 := by
  unfold tailWord_7711944
  simp only [CollatzResearch.WordTrace]
  refine ⟨140638852786475729010503443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187518470381967638680671257 140638852786475729010503443)
  ·
    refine ⟨210958279179713593515755165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140638852786475729010503443 210958279179713593515755165)
    ·
      refine ⟨79109354692392597568408187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210958279179713593515755165 79109354692392597568408187)
      ·
        refine ⟨118664032038588896352612281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79109354692392597568408187 118664032038588896352612281)
        ·
          refine ⟨88998024028941672264459211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118664032038588896352612281 88998024028941672264459211)
          ·
            refine ⟨133497036043412508396688817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88998024028941672264459211 133497036043412508396688817)
            ·
              refine ⟨100122777032559381297516613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133497036043412508396688817 100122777032559381297516613)
              ·
                refine ⟨18773020693604883993284365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100122777032559381297516613 18773020693604883993284365)
                ·
                  refine ⟨7039882760101831497481637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18773020693604883993284365 7039882760101831497481637)
                  ·
                    refine ⟨1319978017519093405777807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039882760101831497481637 1319978017519093405777807)
                    ·
                      rfl

theorem cell23_7711944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_7711944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711944 prefixEnd_7711944 := by exact prefixLift 7711944
  have htrace : WordTrace (prefixWord ++ tailWord_7711944) baseStart_7711944 baseEnd_7711944 := by
    simpa [prefixWord, tailWord_7711944, baseEnd_7711944] using wordTrace_append hprefix tailTrace_7711944
  have hstable : (prefixWord ++ tailWord_7711944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711944).length < 2 ^ (prefixWord ++ tailWord_7711944).sum := by decide
  have hdescent : baseEnd_7711944 < baseStart_7711944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711961 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 1, 4]
def baseStart_7711961 : Nat := 118140960795 + 7711961 * 2 ^ 59
def prefixEnd_7711961 : Nat := 4983230072969 + 3 ^ 40 * 7711961 * 2
def baseEnd_7711961 : Nat := 1319980927242802216940281

theorem tailTrace_7711961 : CollatzResearch.WordTrace tailWord_7711961 prefixEnd_7711961 1319980927242802216940281 := by
  unfold tailWord_7711961
  simp only [CollatzResearch.WordTrace]
  refine ⟨281278325613889869924375737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187518883742593246616250491 281278325613889869924375737)
  ·
    refine ⟨210958744210417402443281803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281278325613889869924375737 210958744210417402443281803)
    ·
      refine ⟨316438116315626103664922705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210958744210417402443281803 316438116315626103664922705)
      ·
        refine ⟨237328587236719577748692029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316438116315626103664922705 237328587236719577748692029)
        ·
          refine ⟨88998220213769841655759511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237328587236719577748692029 88998220213769841655759511)
          ·
            refine ⟨133497330320654762483639267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88998220213769841655759511 133497330320654762483639267)
            ·
              refine ⟨200245995480982143725458901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133497330320654762483639267 200245995480982143725458901)
              ·
                refine ⟨4693265519085518993565443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 200245995480982143725458901 4693265519085518993565443)
                ·
                  refine ⟨7039898278628278490348165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693265519085518993565443 7039898278628278490348165)
                  ·
                    refine ⟨1319980927242802216940281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039898278628278490348165 1319980927242802216940281)
                    ·
                      rfl

theorem cell23_7711961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 4].length) (baseStart_7711961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711961 prefixEnd_7711961 := by exact prefixLift 7711961
  have htrace : WordTrace (prefixWord ++ tailWord_7711961) baseStart_7711961 baseEnd_7711961 := by
    simpa [prefixWord, tailWord_7711961, baseEnd_7711961] using wordTrace_append hprefix tailTrace_7711961
  have hstable : (prefixWord ++ tailWord_7711961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711961).length < 2 ^ (prefixWord ++ tailWord_7711961).sum := by decide
  have hdescent : baseEnd_7711961 < baseStart_7711961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711978 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_7711978 : Nat := 118140960795 + 7711978 * 2 ^ 59
def prefixEnd_7711978 : Nat := 4983230072969 + 3 ^ 40 * 7711978 * 2
def baseEnd_7711978 : Nat := 1319983836966511028102755

theorem tailTrace_7711978 : CollatzResearch.WordTrace tailWord_7711978 prefixEnd_7711978 1319983836966511028102755 := by
  unfold tailWord_7711978
  simp only [CollatzResearch.WordTrace]
  refine ⟨70319736413707070456936147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187519297103218854551829725 70319736413707070456936147)
  ·
    refine ⟨105479604620560605685404221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70319736413707070456936147 105479604620560605685404221)
    ·
      refine ⟨39554851732710227132026583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105479604620560605685404221 39554851732710227132026583)
      ·
        refine ⟨59332277599065340698039875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39554851732710227132026583 59332277599065340698039875)
        ·
          refine ⟨88998416398598011047059813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59332277599065340698039875 88998416398598011047059813)
          ·
            refine ⟨16687203074737127071323715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88998416398598011047059813 16687203074737127071323715)
            ·
              refine ⟨25030804612105690606985573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16687203074737127071323715 25030804612105690606985573)
              ·
                refine ⟨4693275864769816988809795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25030804612105690606985573 4693275864769816988809795)
                ·
                  refine ⟨7039913797154725483214693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693275864769816988809795 7039913797154725483214693)
                  ·
                    refine ⟨1319983836966511028102755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039913797154725483214693 1319983836966511028102755)
                    ·
                      rfl

theorem cell23_7711978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_7711978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711978 prefixEnd_7711978 := by exact prefixLift 7711978
  have htrace : WordTrace (prefixWord ++ tailWord_7711978) baseStart_7711978 baseEnd_7711978 := by
    simpa [prefixWord, tailWord_7711978, baseEnd_7711978] using wordTrace_append hprefix tailTrace_7711978
  have hstable : (prefixWord ++ tailWord_7711978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711978).length < 2 ^ (prefixWord ++ tailWord_7711978).sum := by decide
  have hdescent : baseEnd_7711978 < baseStart_7711978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712001 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_7712001 : Nat := 118140960795 + 7712001 * 2 ^ 59
def prefixEnd_7712001 : Nat := 4983230072969 + 3 ^ 40 * 7712001 * 2
def baseEnd_7712001 : Nat := 3959963320954586494320659

theorem tailTrace_7712001 : CollatzResearch.WordTrace tailWord_7712001 prefixEnd_7712001 3959963320954586494320659 := by
  unfold tailWord_7712001
  simp only [CollatzResearch.WordTrace]
  refine ⟨281279784533744956755831857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187519856355829971170554571 281279784533744956755831857)
  ·
    refine ⟨210959838400308717566873893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281279784533744956755831857 210959838400308717566873893)
    ·
      refine ⟨39554969700057884543788855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210959838400308717566873893 39554969700057884543788855)
      ·
        refine ⟨59332454550086826815683283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39554969700057884543788855 59332454550086826815683283)
        ·
          refine ⟨88998681825130240223524925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59332454550086826815683283 88998681825130240223524925)
          ·
            refine ⟨33374505684423840083821847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88998681825130240223524925 33374505684423840083821847)
            ·
              refine ⟨50061758526635760125732771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33374505684423840083821847 50061758526635760125732771)
              ·
                refine ⟨75092637789953640188599157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50061758526635760125732771 75092637789953640188599157)
                ·
                  refine ⟨7039934792808153767681171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75092637789953640188599157 7039934792808153767681171)
                  ·
                    refine ⟨10559902189212230651521757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7039934792808153767681171 10559902189212230651521757)
                    ·
                      refine ⟨3959963320954586494320659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559902189212230651521757 3959963320954586494320659)
                      ·
                        rfl

theorem cell23_7712001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_7712001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712001 prefixEnd_7712001 := by exact prefixLift 7712001
  have htrace : WordTrace (prefixWord ++ tailWord_7712001) baseStart_7712001 baseEnd_7712001 := by
    simpa [prefixWord, tailWord_7712001, baseEnd_7712001] using wordTrace_append hprefix tailTrace_7712001
  have hstable : (prefixWord ++ tailWord_7712001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712001).length < 2 ^ (prefixWord ++ tailWord_7712001).sum := by decide
  have hdescent : baseEnd_7712001 < baseStart_7712001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712011 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 5, 2]
def baseStart_7712011 : Nat := 118140960795 + 7712011 * 2 ^ 59
def prefixEnd_7712011 : Nat := 4983230072969 + 3 ^ 40 * 7712011 * 2
def baseEnd_7712011 : Nat := 3959968455761131455195613

theorem tailTrace_7712011 : CollatzResearch.WordTrace tailWord_7712011 prefixEnd_7712011 3959968455761131455195613 := by
  unfold tailWord_7712011
  simp only [CollatzResearch.WordTrace]
  refine ⟨281280149263708728463695887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187520099509139152309130591 281280149263708728463695887)
  ·
    refine ⟨421920223895563092695543831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281280149263708728463695887 421920223895563092695543831)
    ·
      refine ⟨632880335843344639043315747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421920223895563092695543831 632880335843344639043315747)
      ·
        refine ⟨949320503765016958564973621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632880335843344639043315747 949320503765016958564973621)
        ·
          refine ⟨88998797227970339865466277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 949320503765016958564973621 88998797227970339865466277)
          ·
            refine ⟨16687274480244438724774927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88998797227970339865466277 16687274480244438724774927)
            ·
              refine ⟨25030911720366658087162391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16687274480244438724774927 25030911720366658087162391)
              ·
                refine ⟨37546367580549987130743587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25030911720366658087162391 37546367580549987130743587)
                ·
                  refine ⟨56319551370824980696115381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37546367580549987130743587 56319551370824980696115381)
                  ·
                    refine ⟨5279957941014841940260817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56319551370824980696115381 5279957941014841940260817)
                    ·
                      refine ⟨3959968455761131455195613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279957941014841940260817 3959968455761131455195613)
                      ·
                        rfl

theorem cell23_7712011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5, 2].length) (baseStart_7712011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712011 prefixEnd_7712011 := by exact prefixLift 7712011
  have htrace : WordTrace (prefixWord ++ tailWord_7712011) baseStart_7712011 baseEnd_7712011 := by
    simpa [prefixWord, tailWord_7712011, baseEnd_7712011] using wordTrace_append hprefix tailTrace_7712011
  have hstable : (prefixWord ++ tailWord_7712011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712011).length < 2 ^ (prefixWord ++ tailWord_7712011).sum := by decide
  have hdescent : baseEnd_7712011 < baseStart_7712011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712047 : List Nat := [1, 1, 2, 1, 2, 1, 3, 12]
def baseStart_7712047 : Nat := 118140960795 + 7712047 * 2 ^ 59
def prefixEnd_7712047 : Nat := 4983230072969 + 3 ^ 40 * 7712047 * 2
def baseEnd_7712047 : Nat := 146666183002396048679461

theorem tailTrace_7712047 : CollatzResearch.WordTrace tailWord_7712047 prefixEnd_7712047 146666183002396048679461 := by
  unfold tailWord_7712047
  simp only [CollatzResearch.WordTrace]
  refine ⟨281281462291578306612006395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187520974861052204408004263 281281462291578306612006395)
  ·
    refine ⟨421922193437367459918009593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281281462291578306612006395 421922193437367459918009593)
    ·
      refine ⟨316441645078025594938507195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421922193437367459918009593 316441645078025594938507195)
      ·
        refine ⟨474662467617038392407760793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316441645078025594938507195 474662467617038392407760793)
        ·
          refine ⟨355996850712778794305820595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474662467617038392407760793 355996850712778794305820595)
          ·
            refine ⟨533995276069168191458730893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355996850712778794305820595 533995276069168191458730893)
            ·
              refine ⟨200248228525938071797024085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533995276069168191458730893 200248228525938071797024085)
              ·
                refine ⟨146666183002396048679461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 200248228525938071797024085 146666183002396048679461)
                ·
                  rfl

theorem cell23_7712047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 12].length) (baseStart_7712047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712047 prefixEnd_7712047 := by exact prefixLift 7712047
  have htrace : WordTrace (prefixWord ++ tailWord_7712047) baseStart_7712047 baseEnd_7712047 := by
    simpa [prefixWord, tailWord_7712047, baseEnd_7712047] using wordTrace_append hprefix tailTrace_7712047
  have hstable : (prefixWord ++ tailWord_7712047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712047).length < 2 ^ (prefixWord ++ tailWord_7712047).sum := by decide
  have hdescent : baseEnd_7712047 < baseStart_7712047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712051 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 1, 6]
def baseStart_7712051 : Nat := 118140960795 + 7712051 * 2 ^ 59
def prefixEnd_7712051 : Nat := 4983230072969 + 3 ^ 40 * 7712051 * 2
def baseEnd_7712051 : Nat := 1319996331662437099565143

theorem tailTrace_7712051 : CollatzResearch.WordTrace tailWord_7712051 prefixEnd_7712051 1319996331662437099565143 := by
  unfold tailWord_7712051
  simp only [CollatzResearch.WordTrace]
  refine ⟨281281608183563815295152007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187521072122375876863434671 281281608183563815295152007)
  ·
    refine ⟨421922412275345722942728011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281281608183563815295152007 421922412275345722942728011)
    ·
      refine ⟨632883618413018584414092017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421922412275345722942728011 632883618413018584414092017)
      ·
        refine ⟨474662713809763938310569013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632883618413018584414092017 474662713809763938310569013)
        ·
          refine ⟨44499629419665369216615845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474662713809763938310569013 44499629419665369216615845)
          ·
            refine ⟨8343680516187256728115471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44499629419665369216615845 8343680516187256728115471)
            ·
              refine ⟨12515520774280885092173207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343680516187256728115471 12515520774280885092173207)
              ·
                refine ⟨18773281161421327638259811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12515520774280885092173207 18773281161421327638259811)
                ·
                  refine ⟨28159921742131991457389717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18773281161421327638259811 28159921742131991457389717)
                  ·
                    refine ⟨1319996331662437099565143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28159921742131991457389717 1319996331662437099565143)
                    ·
                      rfl

theorem cell23_7712051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 6].length) (baseStart_7712051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712051 prefixEnd_7712051 := by exact prefixLift 7712051
  have htrace : WordTrace (prefixWord ++ tailWord_7712051) baseStart_7712051 baseEnd_7712051 := by
    simpa [prefixWord, tailWord_7712051, baseEnd_7712051] using wordTrace_append hprefix tailTrace_7712051
  have hstable : (prefixWord ++ tailWord_7712051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712051).length < 2 ^ (prefixWord ++ tailWord_7712051).sum := by decide
  have hdescent : baseEnd_7712051 < baseStart_7712051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712058 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_7712058 : Nat := 118140960795 + 7712058 * 2 ^ 59
def prefixEnd_7712058 : Nat := 4983230072969 + 3 ^ 40 * 7712058 * 2
def baseEnd_7712058 : Nat := 3959992589351892771307897

theorem tailTrace_7712058 : CollatzResearch.WordTrace tailWord_7712058 prefixEnd_7712058 3959992589351892771307897 := by
  unfold tailWord_7712058
  simp only [CollatzResearch.WordTrace]
  refine ⟨70320465873634613872664207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187521242329692303660437885 70320465873634613872664207)
  ·
    refine ⟨105480698810451920808996311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70320465873634613872664207 105480698810451920808996311)
    ·
      refine ⟨158221048215677881213494467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105480698810451920808996311 158221048215677881213494467)
      ·
        refine ⟨237331572323516821820241701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158221048215677881213494467 237331572323516821820241701)
        ·
          refine ⟨44499669810659404091295319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237331572323516821820241701 44499669810659404091295319)
          ·
            refine ⟨66749504715989106136942979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44499669810659404091295319 66749504715989106136942979)
            ·
              refine ⟨100124257073983659205414469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66749504715989106136942979 100124257073983659205414469)
              ·
                refine ⟨18773298201371936101015213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100124257073983659205414469 18773298201371936101015213)
                ·
                  refine ⟨7039986825514476037880705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18773298201371936101015213 7039986825514476037880705)
                  ·
                    refine ⟨5279990119135857028410529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7039986825514476037880705 5279990119135857028410529)
                    ·
                      refine ⟨3959992589351892771307897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279990119135857028410529 3959992589351892771307897)
                      ·
                        rfl

theorem cell23_7712058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_7712058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712058 prefixEnd_7712058 := by exact prefixLift 7712058
  have htrace : WordTrace (prefixWord ++ tailWord_7712058) baseStart_7712058 baseEnd_7712058 := by
    simpa [prefixWord, tailWord_7712058, baseEnd_7712058] using wordTrace_append hprefix tailTrace_7712058
  have hstable : (prefixWord ++ tailWord_7712058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712058).length < 2 ^ (prefixWord ++ tailWord_7712058).sum := by decide
  have hdescent : baseEnd_7712058 < baseStart_7712058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712068 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7712068 : Nat := 118140960795 + 7712068 * 2 ^ 59
def prefixEnd_7712068 : Nat := 4983230072969 + 3 ^ 40 * 7712068 * 2
def baseEnd_7712068 : Nat := 1319999241386145910727617

theorem tailTrace_7712068 : CollatzResearch.WordTrace tailWord_7712068 prefixEnd_7712068 1319999241386145910727617 := by
  unfold tailWord_7712068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140641114112251113599260429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187521485483001484799013905 140641114112251113599260429)
  ·
    refine ⟨52740417792094167599722661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140641114112251113599260429 52740417792094167599722661)
    ·
      refine ⟨9888828336017656424947999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52740417792094167599722661 9888828336017656424947999)
      ·
        refine ⟨14833242504026484637421999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9888828336017656424947999 14833242504026484637421999)
        ·
          refine ⟨22249863756039726956132999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14833242504026484637421999 22249863756039726956132999)
          ·
            refine ⟨33374795634059590434199499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22249863756039726956132999 33374795634059590434199499)
            ·
              refine ⟨50062193451089385651299249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33374795634059590434199499 50062193451089385651299249)
              ·
                refine ⟨37546645088317039238474437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50062193451089385651299249 37546645088317039238474437)
                ·
                  refine ⟨7039995954059444857213957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37546645088317039238474437 7039995954059444857213957)
                  ·
                    refine ⟨1319999241386145910727617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039995954059444857213957 1319999241386145910727617)
                    ·
                      rfl

theorem cell23_7712068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7712068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712068 prefixEnd_7712068 := by exact prefixLift 7712068
  have htrace : WordTrace (prefixWord ++ tailWord_7712068) baseStart_7712068 baseEnd_7712068 := by
    simpa [prefixWord, tailWord_7712068, baseEnd_7712068] using wordTrace_append hprefix tailTrace_7712068
  have hstable : (prefixWord ++ tailWord_7712068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712068).length < 2 ^ (prefixWord ++ tailWord_7712068).sum := by decide
  have hdescent : baseEnd_7712068 < baseStart_7712068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712086 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7712086 : Nat := 118140960795 + 7712086 * 2 ^ 59
def prefixEnd_7712086 : Nat := 4983230072969 + 3 ^ 40 * 7712086 * 2
def baseEnd_7712086 : Nat := 3960006966810218661757769

theorem tailTrace_7712086 : CollatzResearch.WordTrace tailWord_7712086 prefixEnd_7712086 3960006966810218661757769 := by
  unfold tailWord_7712086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17580180296152313517042257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187521923158958010848450741 17580180296152313517042257)
  ·
    refine ⟨13185135222114235137781693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17580180296152313517042257 13185135222114235137781693)
    ·
      refine ⟨4944425708292838176668135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13185135222114235137781693 4944425708292838176668135)
      ·
        refine ⟨7416638562439257265002203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944425708292838176668135 7416638562439257265002203)
        ·
          refine ⟨11124957843658885897503305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7416638562439257265002203 11124957843658885897503305)
          ·
            refine ⟨8343718382744164423127479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11124957843658885897503305 8343718382744164423127479)
            ·
              refine ⟨12515577574116246634691219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343718382744164423127479 12515577574116246634691219)
              ·
                refine ⟨18773366361174369952036829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12515577574116246634691219 18773366361174369952036829)
                ·
                  refine ⟨7040012385440388732013811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18773366361174369952036829 7040012385440388732013811)
                  ·
                    refine ⟨10560018578160583098020717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040012385440388732013811 10560018578160583098020717)
                    ·
                      refine ⟨3960006966810218661757769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560018578160583098020717 3960006966810218661757769)
                      ·
                        rfl

theorem cell23_7712086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7712086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712086 prefixEnd_7712086 := by exact prefixLift 7712086
  have htrace : WordTrace (prefixWord ++ tailWord_7712086) baseStart_7712086 baseEnd_7712086 := by
    simpa [prefixWord, tailWord_7712086, baseEnd_7712086] using wordTrace_append hprefix tailTrace_7712086
  have hstable : (prefixWord ++ tailWord_7712086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712086).length < 2 ^ (prefixWord ++ tailWord_7712086).sum := by decide
  have hdescent : baseEnd_7712086 < baseStart_7712086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712142 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7712142 : Nat := 118140960795 + 7712142 * 2 ^ 59
def prefixEnd_7712142 : Nat := 4983230072969 + 3 ^ 40 * 7712142 * 2
def baseEnd_7712142 : Nat := 3960035721726870442657511

theorem tailTrace_7712142 : CollatzResearch.WordTrace tailWord_7712142 prefixEnd_7712142 3960035721726870442657511 := by
  unfold tailWord_7712142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35160615903279267229589335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187523284817489425224476453 35160615903279267229589335)
  ·
    refine ⟨52740923854918900844384003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35160615903279267229589335 52740923854918900844384003)
    ·
      refine ⟨79111385782378351266576005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52740923854918900844384003 79111385782378351266576005)
      ·
        refine ⟨14833384834195940862483001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79111385782378351266576005 14833384834195940862483001)
        ·
          refine ⟨11125038625646955646862251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833384834195940862483001 11125038625646955646862251)
          ·
            refine ⟨16687557938470433470293377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125038625646955646862251 16687557938470433470293377)
            ·
              refine ⟨12515668453852825102720033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16687557938470433470293377 12515668453852825102720033)
              ·
                refine ⟨9386751340389618827040025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12515668453852825102720033 9386751340389618827040025)
                ·
                  refine ⟨7040063505292214120280019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9386751340389618827040025 7040063505292214120280019)
                  ·
                    refine ⟨10560095257938321180420029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040063505292214120280019 10560095257938321180420029)
                    ·
                      refine ⟨3960035721726870442657511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560095257938321180420029 3960035721726870442657511)
                      ·
                        rfl

theorem cell23_7712142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7712142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712142 prefixEnd_7712142 := by exact prefixLift 7712142
  have htrace : WordTrace (prefixWord ++ tailWord_7712142) baseStart_7712142 baseEnd_7712142 := by
    simpa [prefixWord, tailWord_7712142, baseEnd_7712142] using wordTrace_append hprefix tailTrace_7712142
  have hstable : (prefixWord ++ tailWord_7712142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712142).length < 2 ^ (prefixWord ++ tailWord_7712142).sum := by decide
  have hdescent : baseEnd_7712142 < baseStart_7712142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712238 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7712238 : Nat := 118140960795 + 7712238 * 2 ^ 59
def prefixEnd_7712238 : Nat := 4983230072969 + 3 ^ 40 * 7712238 * 2
def baseEnd_7712238 : Nat := 3960085015869702067057069

theorem tailTrace_7712238 : CollatzResearch.WordTrace tailWord_7712238 prefixEnd_7712238 3960085015869702067057069 := by
  unfold tailWord_7712238
  simp only [CollatzResearch.WordTrace]
  refine ⟨35161053579235793279026171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187525619089257564154806245 35161053579235793279026171)
  ·
    refine ⟨52741580368853689918539257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35161053579235793279026171 52741580368853689918539257)
    ·
      refine ⟨39556185276640267438904443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52741580368853689918539257 39556185276640267438904443)
      ·
        refine ⟨59334277914960401158356665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39556185276640267438904443 59334277914960401158356665)
        ·
          refine ⟨44500708436220300868767499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59334277914960401158356665 44500708436220300868767499)
          ·
            refine ⟨66751062654330451303151249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44500708436220300868767499 66751062654330451303151249)
            ·
              refine ⟨50063296990747838477363437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66751062654330451303151249 50063296990747838477363437)
              ·
                refine ⟨18773736371530439429011289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50063296990747838477363437 18773736371530439429011289)
                ·
                  refine ⟨14080302278647829571758467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18773736371530439429011289 14080302278647829571758467)
                  ·
                    refine ⟨21120453417971744357637701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14080302278647829571758467 21120453417971744357637701)
                    ·
                      refine ⟨3960085015869702067057069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21120453417971744357637701 3960085015869702067057069)
                      ·
                        rfl

theorem cell23_7712238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7712238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712238 prefixEnd_7712238 := by exact prefixLift 7712238
  have htrace : WordTrace (prefixWord ++ tailWord_7712238) baseStart_7712238 baseEnd_7712238 := by
    simpa [prefixWord, tailWord_7712238, baseEnd_7712238] using wordTrace_append hprefix tailTrace_7712238
  have hstable : (prefixWord ++ tailWord_7712238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712238).length < 2 ^ (prefixWord ++ tailWord_7712238).sum := by decide
  have hdescent : baseEnd_7712238 < baseStart_7712238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712261 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 6]
def baseStart_7712261 : Nat := 118140960795 + 7712261 * 2 ^ 59
def prefixEnd_7712261 : Nat := 4983230072969 + 3 ^ 40 * 7712261 * 2
def baseEnd_7712261 : Nat := 440010758436083941896607

theorem tailTrace_7712261 : CollatzResearch.WordTrace tailWord_7712261 prefixEnd_7712261 440010758436083941896607 := by
  unfold tailWord_7712261
  simp only [CollatzResearch.WordTrace]
  refine ⟨281289267512803021160296637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187526178341868680773531091 281289267512803021160296637)
  ·
    refine ⟨105483475317301132935111239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281289267512803021160296637 105483475317301132935111239)
    ·
      refine ⟨158225212975951699402666859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105483475317301132935111239 158225212975951699402666859)
      ·
        refine ⟨237337819463927549104000289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158225212975951699402666859 237337819463927549104000289)
        ·
          refine ⟨178003364597945661828000217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237337819463927549104000289 178003364597945661828000217)
          ·
            refine ⟨133502523448459246371000163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178003364597945661828000217 133502523448459246371000163)
            ·
              refine ⟨200253785172688869556500245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133502523448459246371000163 200253785172688869556500245)
              ·
                refine ⟨9386896179969790760460949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200253785172688869556500245 9386896179969790760460949)
                ·
                  refine ⟨440010758436083941896607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9386896179969790760460949 440010758436083941896607)
                  ·
                    rfl

theorem cell23_7712261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_7712261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712261 prefixEnd_7712261 := by exact prefixLift 7712261
  have htrace : WordTrace (prefixWord ++ tailWord_7712261) baseStart_7712261 baseEnd_7712261 := by
    simpa [prefixWord, tailWord_7712261, baseEnd_7712261] using wordTrace_append hprefix tailTrace_7712261
  have hstable : (prefixWord ++ tailWord_7712261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712261).length < 2 ^ (prefixWord ++ tailWord_7712261).sum := by decide
  have hdescent : baseEnd_7712261 < baseStart_7712261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712316 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_7712316 : Nat := 118140960795 + 7712316 * 2 ^ 59
def prefixEnd_7712316 : Nat := 4983230072969 + 3 ^ 40 * 7712316 * 2
def baseEnd_7712316 : Nat := 1320041689120250920627237

theorem tailTrace_7712316 : CollatzResearch.WordTrace tailWord_7712316 prefixEnd_7712316 1320041689120250920627237 := by
  unfold tailWord_7712316
  simp only [CollatzResearch.WordTrace]
  refine ⟨140645636763801882776774401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187527515685069177035699201 140645636763801882776774401)
  ·
    refine ⟨105484227572851412082580801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140645636763801882776774401 105484227572851412082580801)
    ·
      refine ⟨79113170679638559061935601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105484227572851412082580801 79113170679638559061935601)
      ·
        refine ⟨59334878009728919296451701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79113170679638559061935601 59334878009728919296451701)
        ·
          refine ⟨5562644813412086184042347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59334878009728919296451701 5562644813412086184042347)
          ·
            refine ⟨8343967220118129276063521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562644813412086184042347 8343967220118129276063521)
            ·
              refine ⟨6257975415088596957047641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8343967220118129276063521 6257975415088596957047641)
              ·
                refine ⟨4693481561316447717785731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257975415088596957047641 4693481561316447717785731)
                ·
                  refine ⟨7040222341974671576678597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693481561316447717785731 7040222341974671576678597)
                  ·
                    refine ⟨1320041689120250920627237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040222341974671576678597 1320041689120250920627237)
                    ·
                      rfl

theorem cell23_7712316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_7712316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712316 prefixEnd_7712316 := by exact prefixLift 7712316
  have htrace : WordTrace (prefixWord ++ tailWord_7712316) baseStart_7712316 baseEnd_7712316 := by
    simpa [prefixWord, tailWord_7712316, baseEnd_7712316] using wordTrace_append hprefix tailTrace_7712316
  have hstable : (prefixWord ++ tailWord_7712316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712316).length < 2 ^ (prefixWord ++ tailWord_7712316).sum := by decide
  have hdescent : baseEnd_7712316 < baseStart_7712316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712328 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_7712328 : Nat := 118140960795 + 7712328 * 2 ^ 59
def prefixEnd_7712328 : Nat := 4983230072969 + 3 ^ 40 * 7712328 * 2
def baseEnd_7712328 : Nat := 3960131229128606714931655

theorem tailTrace_7712328 : CollatzResearch.WordTrace tailWord_7712328 prefixEnd_7712328 3960131229128606714931655 := by
  unfold tailWord_7712328
  simp only [CollatzResearch.WordTrace]
  refine ⟨140645855601780145801492819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187527807469040194401990425 140645855601780145801492819)
  ·
    refine ⟨210968783402670218702239229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140645855601780145801492819 210968783402670218702239229)
    ·
      refine ⟨79113293776001332013339711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210968783402670218702239229 79113293776001332013339711)
      ·
        refine ⟨118669940664001998020009567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79113293776001332013339711 118669940664001998020009567)
        ·
          refine ⟨178004910996002997030014351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118669940664001998020009567 178004910996002997030014351)
          ·
            refine ⟨267007366494004495545021527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178004910996002997030014351 267007366494004495545021527)
            ·
              refine ⟨400511049741006743317532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267007366494004495545021527 400511049741006743317532291)
              ·
                refine ⟨600766574611510114976298437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400511049741006743317532291 600766574611510114976298437)
                ·
                  refine ⟨112643732739658146558055957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600766574611510114976298437 112643732739658146558055957)
                  ·
                    refine ⟨5280174972171475619908873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112643732739658146558055957 5280174972171475619908873)
                    ·
                      refine ⟨3960131229128606714931655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280174972171475619908873 3960131229128606714931655)
                      ·
                        rfl

theorem cell23_7712328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_7712328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712328 prefixEnd_7712328 := by exact prefixLift 7712328
  have htrace : WordTrace (prefixWord ++ tailWord_7712328) baseStart_7712328 baseEnd_7712328 := by
    simpa [prefixWord, tailWord_7712328, baseEnd_7712328] using wordTrace_append hprefix tailTrace_7712328
  have hstable : (prefixWord ++ tailWord_7712328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712328).length < 2 ^ (prefixWord ++ tailWord_7712328).sum := by decide
  have hdescent : baseEnd_7712328 < baseStart_7712328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712331 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_7712331 : Nat := 118140960795 + 7712331 * 2 ^ 59
def prefixEnd_7712331 : Nat := 4983230072969 + 3 ^ 40 * 7712331 * 2
def baseEnd_7712331 : Nat := 3960132769570570203194141

theorem tailTrace_7712331 : CollatzResearch.WordTrace tailWord_7712331 prefixEnd_7712331 3960132769570570203194141 := by
  unfold tailWord_7712331
  simp only [CollatzResearch.WordTrace]
  refine ⟨281291820622549423115344847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187527880415032948743563231 281291820622549423115344847)
  ·
    refine ⟨421937730933824134673017271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281291820622549423115344847 421937730933824134673017271)
    ·
      refine ⟨632906596400736202009525907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421937730933824134673017271 632906596400736202009525907)
      ·
        refine ⟨949359894601104303014288861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632906596400736202009525907 949359894601104303014288861)
        ·
          refine ⟨356009960475414113630358323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949359894601104303014288861 356009960475414113630358323)
          ·
            refine ⟨534014940713121170445537485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356009960475414113630358323 534014940713121170445537485)
            ·
              refine ⟨200255602767420438917076557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534014940713121170445537485 200255602767420438917076557)
              ·
                refine ⟨75095851037782664593903709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200255602767420438917076557 75095851037782664593903709)
                ·
                  refine ⟨28160944139168499222713891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75095851037782664593903709 28160944139168499222713891)
                  ·
                    refine ⟨42241416208752748834070837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28160944139168499222713891 42241416208752748834070837)
                    ·
                      refine ⟨3960132769570570203194141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42241416208752748834070837 3960132769570570203194141)
                      ·
                        rfl

theorem cell23_7712331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_7712331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712331 prefixEnd_7712331 := by exact prefixLift 7712331
  have htrace : WordTrace (prefixWord ++ tailWord_7712331) baseStart_7712331 baseEnd_7712331 := by
    simpa [prefixWord, tailWord_7712331, baseEnd_7712331] using wordTrace_append hprefix tailTrace_7712331
  have hstable : (prefixWord ++ tailWord_7712331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712331).length < 2 ^ (prefixWord ++ tailWord_7712331).sum := by decide
  have hdescent : baseEnd_7712331 < baseStart_7712331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712338 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7712338 : Nat := 118140960795 + 7712338 * 2 ^ 59
def prefixEnd_7712338 : Nat := 4983230072969 + 3 ^ 40 * 7712338 * 2
def baseEnd_7712338 : Nat := 1320045454645050558602203

theorem tailTrace_7712338 : CollatzResearch.WordTrace tailWord_7712338 prefixEnd_7712338 1320045454645050558602203 := by
  unfold tailWord_7712338
  simp only [CollatzResearch.WordTrace]
  refine ⟨70323018983381015827712417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187528050622349375540566445 70323018983381015827712417)
  ·
    refine ⟨52742264237535761870784313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70323018983381015827712417 52742264237535761870784313)
    ·
      refine ⟨39556698178151821403088235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52742264237535761870784313 39556698178151821403088235)
      ·
        refine ⟨59335047267227732104632353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39556698178151821403088235 59335047267227732104632353)
        ·
          refine ⟨44501285450420799078474265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59335047267227732104632353 44501285450420799078474265)
          ·
            refine ⟨33375964087815599308855699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44501285450420799078474265 33375964087815599308855699)
            ·
              refine ⟨50063946131723398963283549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33375964087815599308855699 50063946131723398963283549)
              ·
                refine ⟨18773979799396274611231331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50063946131723398963283549 18773979799396274611231331)
                ·
                  refine ⟨28160969699094411916846997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18773979799396274611231331 28160969699094411916846997)
                  ·
                    refine ⟨1320045454645050558602203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28160969699094411916846997 1320045454645050558602203)
                    ·
                      rfl

theorem cell23_7712338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7712338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712338 prefixEnd_7712338 := by exact prefixLift 7712338
  have htrace : WordTrace (prefixWord ++ tailWord_7712338) baseStart_7712338 baseEnd_7712338 := by
    simpa [prefixWord, tailWord_7712338, baseEnd_7712338] using wordTrace_append hprefix tailTrace_7712338
  have hstable : (prefixWord ++ tailWord_7712338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712338).length < 2 ^ (prefixWord ++ tailWord_7712338).sum := by decide
  have hdescent : baseEnd_7712338 < baseStart_7712338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712349 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7712349 : Nat := 118140960795 + 7712349 * 2 ^ 59
def prefixEnd_7712349 : Nat := 4983230072969 + 3 ^ 40 * 7712349 * 2
def baseEnd_7712349 : Nat := 3960142012222351132769059

theorem tailTrace_7712349 : CollatzResearch.WordTrace tailWord_7712349 prefixEnd_7712349 3960142012222351132769059 := by
  unfold tailWord_7712349
  simp only [CollatzResearch.WordTrace]
  refine ⟨281292477136484212189500101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187528318090989474793000067 281292477136484212189500101)
  ·
    refine ⟨52742339463090789785531269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281292477136484212189500101 52742339463090789785531269)
    ·
      refine ⟨9889188649329523084787113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52742339463090789785531269 9889188649329523084787113)
      ·
        refine ⟨7416891486997142313590335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9889188649329523084787113 7416891486997142313590335)
        ·
          refine ⟨11125337230495713470385503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7416891486997142313590335 11125337230495713470385503)
          ·
            refine ⟨16688005845743570205578255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125337230495713470385503 16688005845743570205578255)
            ·
              refine ⟨25032008768615355308367383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16688005845743570205578255 25032008768615355308367383)
              ·
                refine ⟨37548013152923032962551075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25032008768615355308367383 37548013152923032962551075)
                ·
                  refine ⟨56322019729384549443826613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37548013152923032962551075 56322019729384549443826613)
                  ·
                    refine ⟨5280189349629801510358745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56322019729384549443826613 5280189349629801510358745)
                    ·
                      refine ⟨3960142012222351132769059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280189349629801510358745 3960142012222351132769059)
                      ·
                        rfl

theorem cell23_7712349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7712349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712349 prefixEnd_7712349 := by exact prefixLift 7712349
  have htrace : WordTrace (prefixWord ++ tailWord_7712349) baseStart_7712349 baseEnd_7712349 := by
    simpa [prefixWord, tailWord_7712349, baseEnd_7712349] using wordTrace_append hprefix tailTrace_7712349
  have hstable : (prefixWord ++ tailWord_7712349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712349).length < 2 ^ (prefixWord ++ tailWord_7712349).sum := by decide
  have hdescent : baseEnd_7712349 < baseStart_7712349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712362 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_7712362 : Nat := 118140960795 + 7712362 * 2 ^ 59
def prefixEnd_7712362 : Nat := 4983230072969 + 3 ^ 40 * 7712362 * 2
def baseEnd_7712362 : Nat := 3960148687470859581906499

theorem tailTrace_7712362 : CollatzResearch.WordTrace tailWord_7712362 prefixEnd_7712362 3960148687470859581906499 := by
  unfold tailWord_7712362
  simp only [CollatzResearch.WordTrace]
  refine ⟨70323237821359278852430835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187528634190291410273148893 70323237821359278852430835)
  ·
    refine ⟨105484856732038918278646253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70323237821359278852430835 105484856732038918278646253)
    ·
      refine ⟨39556821274514594354492345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105484856732038918278646253 39556821274514594354492345)
      ·
        refine ⟨29667615955885945765869259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39556821274514594354492345 29667615955885945765869259)
        ·
          refine ⟨44501423933828918648803889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29667615955885945765869259 44501423933828918648803889)
          ·
            refine ⟨33376067950371688986602917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44501423933828918648803889 33376067950371688986602917)
            ·
              refine ⟨6258012740694691684988047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33376067950371688986602917 6258012740694691684988047)
              ·
                refine ⟨9387019111042037527482071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258012740694691684988047 9387019111042037527482071)
                ·
                  refine ⟨14080528666563056291223107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387019111042037527482071 14080528666563056291223107)
                  ·
                    refine ⟨21120792999844584436834661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14080528666563056291223107 21120792999844584436834661)
                    ·
                      refine ⟨3960148687470859581906499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21120792999844584436834661 3960148687470859581906499)
                      ·
                        rfl

theorem cell23_7712362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_7712362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712362 prefixEnd_7712362 := by exact prefixLift 7712362
  have htrace : WordTrace (prefixWord ++ tailWord_7712362) baseStart_7712362 baseEnd_7712362 := by
    simpa [prefixWord, tailWord_7712362, baseEnd_7712362] using wordTrace_append hprefix tailTrace_7712362
  have hstable : (prefixWord ++ tailWord_7712362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712362).length < 2 ^ (prefixWord ++ tailWord_7712362).sum := by decide
  have hdescent : baseEnd_7712362 < baseStart_7712362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712401 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_7712401 : Nat := 118140960795 + 7712401 * 2 ^ 59
def prefixEnd_7712401 : Nat := 4983230072969 + 3 ^ 40 * 7712401 * 2
def baseEnd_7712401 : Nat := 3960168713216384929318819

theorem tailTrace_7712401 : CollatzResearch.WordTrace tailWord_7712401 prefixEnd_7712401 3960168713216384929318819 := by
  unfold tailWord_7712401
  simp only [CollatzResearch.WordTrace]
  refine ⟨281294373732295825070393057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187529582488197216713595371 281294373732295825070393057)
  ·
    refine ⟨210970780299221868802794793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281294373732295825070393057 210970780299221868802794793)
    ·
      refine ⟨158228085224416401602096095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210970780299221868802794793 158228085224416401602096095)
      ·
        refine ⟨237342127836624602403144143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158228085224416401602096095 237342127836624602403144143)
        ·
          refine ⟨356013191754936903604716215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237342127836624602403144143 356013191754936903604716215)
          ·
            refine ⟨534019787632405355407074323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356013191754936903604716215 534019787632405355407074323)
            ·
              refine ⟨801029681448608033110611485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534019787632405355407074323 801029681448608033110611485)
              ·
                refine ⟨300386130543228012416479307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801029681448608033110611485 300386130543228012416479307)
                ·
                  refine ⟨450579195814842018624718961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300386130543228012416479307 450579195814842018624718961)
                  ·
                    refine ⟨337934396861131513968539221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 450579195814842018624718961 337934396861131513968539221)
                    ·
                      refine ⟨3960168713216384929318819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337934396861131513968539221 3960168713216384929318819)
                      ·
                        rfl

theorem cell23_7712401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_7712401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712401 prefixEnd_7712401 := by exact prefixLift 7712401
  have htrace : WordTrace (prefixWord ++ tailWord_7712401) baseStart_7712401 baseEnd_7712401 := by
    simpa [prefixWord, tailWord_7712401, baseEnd_7712401] using wordTrace_append hprefix tailTrace_7712401
  have hstable : (prefixWord ++ tailWord_7712401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712401).length < 2 ^ (prefixWord ++ tailWord_7712401).sum := by decide
  have hdescent : baseEnd_7712401 < baseStart_7712401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712402 : List Nat := [3, 2, 3, 1, 3, 2, 2, 7]
def baseStart_7712402 : Nat := 118140960795 + 7712402 * 2 ^ 59
def prefixEnd_7712402 : Nat := 4983230072969 + 3 ^ 40 * 7712402 * 2
def baseEnd_7712402 : Nat := 146672934322112571311345

theorem tailTrace_7712402 : CollatzResearch.WordTrace tailWord_7712402 prefixEnd_7712402 146672934322112571311345 := by
  unfold tailWord_7712402
  simp only [CollatzResearch.WordTrace]
  refine ⟨70323602551323050560294865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187529606803528134827452973 70323602551323050560294865)
  ·
    refine ⟨52742701913492287920221149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70323602551323050560294865 52742701913492287920221149)
    ·
      refine ⟨19778513217559607970082931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52742701913492287920221149 19778513217559607970082931)
      ·
        refine ⟨29667769826339411955124397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778513217559607970082931 29667769826339411955124397)
        ·
          refine ⟨11125413684877279483171649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29667769826339411955124397 11125413684877279483171649)
          ·
            refine ⟨8344060263657959612378737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11125413684877279483171649 8344060263657959612378737)
            ·
              refine ⟨6258045197743469709284053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344060263657959612378737 6258045197743469709284053)
              ·
                refine ⟨146672934322112571311345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6258045197743469709284053 146672934322112571311345)
                ·
                  rfl

theorem cell23_7712402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_7712402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712402 prefixEnd_7712402 := by exact prefixLift 7712402
  have htrace : WordTrace (prefixWord ++ tailWord_7712402) baseStart_7712402 baseEnd_7712402 := by
    simpa [prefixWord, tailWord_7712402, baseEnd_7712402] using wordTrace_append hprefix tailTrace_7712402
  have hstable : (prefixWord ++ tailWord_7712402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712402).length < 2 ^ (prefixWord ++ tailWord_7712402).sum := by decide
  have hdescent : baseEnd_7712402 < baseStart_7712402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712405 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_7712405 : Nat := 118140960795 + 7712405 * 2 ^ 59
def prefixEnd_7712405 : Nat := 4983230072969 + 3 ^ 40 * 7712405 * 2
def baseEnd_7712405 : Nat := 3960170767139002913668801

theorem tailTrace_7712405 : CollatzResearch.WordTrace tailWord_7712405 prefixEnd_7712405 3960170767139002913668801 := by
  unfold tailWord_7712405
  simp only [CollatzResearch.WordTrace]
  refine ⟨281294519624281333753538669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187529679749520889169025779 281294519624281333753538669)
  ·
    refine ⟨105485444859105500157577001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281294519624281333753538669 105485444859105500157577001)
    ·
      refine ⟨79114083644329125118182751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105485444859105500157577001 79114083644329125118182751)
      ·
        refine ⟨118671125466493687677274127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79114083644329125118182751 118671125466493687677274127)
        ·
          refine ⟨178006688199740531515911191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118671125466493687677274127 178006688199740531515911191)
          ·
            refine ⟨267010032299610797273866787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178006688199740531515911191 267010032299610797273866787)
            ·
              refine ⟨400515048449416195910800181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267010032299610797273866787 400515048449416195910800181)
              ·
                refine ⟨37548285792132768366637517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400515048449416195910800181 37548285792132768366637517)
                ·
                  refine ⟨14080607172049788137489069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37548285792132768366637517 14080607172049788137489069)
                  ·
                    refine ⟨5280227689518670551558401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14080607172049788137489069 5280227689518670551558401)
                    ·
                      refine ⟨3960170767139002913668801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280227689518670551558401 3960170767139002913668801)
                      ·
                        rfl

theorem cell23_7712405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_7712405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712405 prefixEnd_7712405 := by exact prefixLift 7712405
  have htrace : WordTrace (prefixWord ++ tailWord_7712405) baseStart_7712405 baseEnd_7712405 := by
    simpa [prefixWord, tailWord_7712405, baseEnd_7712405] using wordTrace_append hprefix tailTrace_7712405
  have hstable : (prefixWord ++ tailWord_7712405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712405).length < 2 ^ (prefixWord ++ tailWord_7712405).sum := by decide
  have hdescent : baseEnd_7712405 < baseStart_7712405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712408 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7712408 : Nat := 118140960795 + 7712408 * 2 ^ 59
def prefixEnd_7712408 : Nat := 4983230072969 + 3 ^ 40 * 7712408 * 2
def baseEnd_7712408 : Nat := 3960172307580966401931287

theorem tailTrace_7712408 : CollatzResearch.WordTrace tailWord_7712408 prefixEnd_7712408 3960172307580966401931287 := by
  unfold tailWord_7712408
  simp only [CollatzResearch.WordTrace]
  refine ⟨140647314521635232632948939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187529752695513643510598585 140647314521635232632948939)
  ·
    refine ⟨210970971782452848949423409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140647314521635232632948939 210970971782452848949423409)
    ·
      refine ⟨158228228836839636712067557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210970971782452848949423409 158228228836839636712067557)
      ·
        refine ⟨29667792906907431883512667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158228228836839636712067557 29667792906907431883512667)
        ·
          refine ⟨44501689360361147825269001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29667792906907431883512667 44501689360361147825269001)
          ·
            refine ⟨33376267020270860868951751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44501689360361147825269001 33376267020270860868951751)
            ·
              refine ⟨50064400530406291303427627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33376267020270860868951751 50064400530406291303427627)
              ·
                refine ⟨75096600795609436955141441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50064400530406291303427627 75096600795609436955141441)
                ·
                  refine ⟨56322450596707077716356081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75096600795609436955141441 56322450596707077716356081)
                  ·
                    refine ⟨42241837947530308287267061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56322450596707077716356081 42241837947530308287267061)
                    ·
                      refine ⟨3960172307580966401931287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42241837947530308287267061 3960172307580966401931287)
                      ·
                        rfl

theorem cell23_7712408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7712408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712408 prefixEnd_7712408 := by exact prefixLift 7712408
  have htrace : WordTrace (prefixWord ++ tailWord_7712408) baseStart_7712408 baseEnd_7712408 := by
    simpa [prefixWord, tailWord_7712408, baseEnd_7712408] using wordTrace_append hprefix tailTrace_7712408
  have hstable : (prefixWord ++ tailWord_7712408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712408).length < 2 ^ (prefixWord ++ tailWord_7712408).sum := by decide
  have hdescent : baseEnd_7712408 < baseStart_7712408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712430 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7712430 : Nat := 118140960795 + 7712430 * 2 ^ 59
def prefixEnd_7712430 : Nat := 4983230072969 + 3 ^ 40 * 7712430 * 2
def baseEnd_7712430 : Nat := 3960183604155365315856187

theorem tailTrace_7712430 : CollatzResearch.WordTrace tailWord_7712430 prefixEnd_7712430 3960183604155365315856187 := by
  unfold tailWord_7712430
  simp only [CollatzResearch.WordTrace]
  refine ⟨35161928931148845377899843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187530287632793842015465829 35161928931148845377899843)
  ·
    refine ⟨52742893396723268066849765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35161928931148845377899843 52742893396723268066849765)
    ·
      refine ⟨9889292511885612762534331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52742893396723268066849765 9889292511885612762534331)
      ·
        refine ⟨14833938767828419143801497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889292511885612762534331 14833938767828419143801497)
        ·
          refine ⟨11125454075871314357851123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833938767828419143801497 11125454075871314357851123)
          ·
            refine ⟨16688181113806971536776685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125454075871314357851123 16688181113806971536776685)
            ·
              refine ⟨6258067917677614326291257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16688181113806971536776685 6258067917677614326291257)
              ·
                refine ⟨4693550938258210744718443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258067917677614326291257 4693550938258210744718443)
                ·
                  refine ⟨7040326407387316117077665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693550938258210744718443 7040326407387316117077665)
                  ·
                    refine ⟨5280244805540487087808249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040326407387316117077665 5280244805540487087808249)
                    ·
                      refine ⟨3960183604155365315856187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280244805540487087808249 3960183604155365315856187)
                      ·
                        rfl

theorem cell23_7712430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7712430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712430 prefixEnd_7712430 := by exact prefixLift 7712430
  have htrace : WordTrace (prefixWord ++ tailWord_7712430) baseStart_7712430 baseEnd_7712430 := by
    simpa [prefixWord, tailWord_7712430, baseEnd_7712430] using wordTrace_append hprefix tailTrace_7712430
  have hstable : (prefixWord ++ tailWord_7712430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712430).length < 2 ^ (prefixWord ++ tailWord_7712430).sum := by decide
  have hdescent : baseEnd_7712430 < baseStart_7712430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712446 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_7712446 : Nat := 118140960795 + 7712446 * 2 ^ 59
def prefixEnd_7712446 : Nat := 4983230072969 + 3 ^ 40 * 7712446 * 2
def baseEnd_7712446 : Nat := 3960191819845837253256113

theorem tailTrace_7712446 : CollatzResearch.WordTrace tailWord_7712446 prefixEnd_7712446 3960191819845837253256113 := by
  unfold tailWord_7712446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162001877141599719472649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187530676678088531837187461 35162001877141599719472649)
  ·
    refine ⟨26371501407856199789604487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35162001877141599719472649 26371501407856199789604487)
    ·
      refine ⟨39557252111784299684406731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26371501407856199789604487 39557252111784299684406731)
      ·
        refine ⟨59335878167676449526610097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39557252111784299684406731 59335878167676449526610097)
        ·
          refine ⟨44501908625757337144957573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59335878167676449526610097 44501908625757337144957573)
          ·
            refine ⟨8344107867329500714679545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44501908625757337144957573 8344107867329500714679545)
            ·
              refine ⟨6258080900497125536009659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344107867329500714679545 6258080900497125536009659)
              ·
                refine ⟨9387121350745688304014489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258080900497125536009659 9387121350745688304014489)
                ·
                  refine ⟨7040341013059266228010867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387121350745688304014489 7040341013059266228010867)
                  ·
                    refine ⟨10560511519588899342016301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040341013059266228010867 10560511519588899342016301)
                    ·
                      refine ⟨3960191819845837253256113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560511519588899342016301 3960191819845837253256113)
                      ·
                        rfl

theorem cell23_7712446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_7712446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712446 prefixEnd_7712446 := by exact prefixLift 7712446
  have htrace : WordTrace (prefixWord ++ tailWord_7712446) baseStart_7712446 baseEnd_7712446 := by
    simpa [prefixWord, tailWord_7712446, baseEnd_7712446] using wordTrace_append hprefix tailTrace_7712446
  have hstable : (prefixWord ++ tailWord_7712446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712446).length < 2 ^ (prefixWord ++ tailWord_7712446).sum := by decide
  have hdescent : baseEnd_7712446 < baseStart_7712446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712448 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_7712448 : Nat := 118140960795 + 7712448 * 2 ^ 59
def prefixEnd_7712448 : Nat := 4983230072969 + 3 ^ 40 * 7712448 * 2
def baseEnd_7712448 : Nat := 3960192846807146245431103

theorem tailTrace_7712448 : CollatzResearch.WordTrace tailWord_7712448 prefixEnd_7712448 3960192846807146245431103 := by
  unfold tailWord_7712448
  simp only [CollatzResearch.WordTrace]
  refine ⟨140648043981562776048676999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187530725308750368064902665 140648043981562776048676999)
  ·
    refine ⟨210972065972344164073015499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140648043981562776048676999 210972065972344164073015499)
    ·
      refine ⟨316458098958516246109523249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210972065972344164073015499 316458098958516246109523249)
      ·
        refine ⟨237343574218887184582142437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316458098958516246109523249 237343574218887184582142437)
        ·
          refine ⟨44501920166041347109151707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237343574218887184582142437 44501920166041347109151707)
          ·
            refine ⟨66752880249062020663727561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44501920166041347109151707 66752880249062020663727561)
            ·
              refine ⟨50064660186796515497795671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66752880249062020663727561 50064660186796515497795671)
              ·
                refine ⟨75096990280194773246693507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50064660186796515497795671 75096990280194773246693507)
                ·
                  refine ⟨112645485420292159870040261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75096990280194773246693507 112645485420292159870040261)
                  ·
                    refine ⟨21121028516304779975632549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112645485420292159870040261 21121028516304779975632549)
                    ·
                      refine ⟨3960192846807146245431103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21121028516304779975632549 3960192846807146245431103)
                      ·
                        rfl

theorem cell23_7712448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_7712448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712448 prefixEnd_7712448 := by exact prefixLift 7712448
  have htrace : WordTrace (prefixWord ++ tailWord_7712448) baseStart_7712448 baseEnd_7712448 := by
    simpa [prefixWord, tailWord_7712448, baseEnd_7712448] using wordTrace_append hprefix tailTrace_7712448
  have hstable : (prefixWord ++ tailWord_7712448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712448).length < 2 ^ (prefixWord ++ tailWord_7712448).sum := by decide
  have hdescent : baseEnd_7712448 < baseStart_7712448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712450 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7712450 : Nat := 118140960795 + 7712450 * 2 ^ 59
def prefixEnd_7712450 : Nat := 4983230072969 + 3 ^ 40 * 7712450 * 2
def baseEnd_7712450 : Nat := 3960193873768455237606095

theorem tailTrace_7712450 : CollatzResearch.WordTrace tailWord_7712450 prefixEnd_7712450 3960193873768455237606095 := by
  unfold tailWord_7712450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70324040227279576609731701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187530773939412204292617869 70324040227279576609731701)
  ·
    refine ⟨6592878771307460307162347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70324040227279576609731701 6592878771307460307162347)
    ·
      refine ⟨9889318156961190460743521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6592878771307460307162347 9889318156961190460743521)
      ·
        refine ⟨7416988617720892845557641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9889318156961190460743521 7416988617720892845557641)
        ·
          refine ⟨5562741463290669634168231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7416988617720892845557641 5562741463290669634168231)
          ·
            refine ⟨8344112194936004451252347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562741463290669634168231 8344112194936004451252347)
            ·
              refine ⟨12516168292404006676878521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344112194936004451252347 12516168292404006676878521)
              ·
                refine ⟨9387126219303005007658891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516168292404006676878521 9387126219303005007658891)
                ·
                  refine ⟨14080689328954507511488337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387126219303005007658891 14080689328954507511488337)
                  ·
                    refine ⟨10560516996715880633616253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14080689328954507511488337 10560516996715880633616253)
                    ·
                      refine ⟨3960193873768455237606095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560516996715880633616253 3960193873768455237606095)
                      ·
                        rfl

theorem cell23_7712450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7712450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712450 prefixEnd_7712450 := by exact prefixLift 7712450
  have htrace : WordTrace (prefixWord ++ tailWord_7712450) baseStart_7712450 baseEnd_7712450 := by
    simpa [prefixWord, tailWord_7712450, baseEnd_7712450] using wordTrace_append hprefix tailTrace_7712450
  have hstable : (prefixWord ++ tailWord_7712450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712450).length < 2 ^ (prefixWord ++ tailWord_7712450).sum := by decide
  have hdescent : baseEnd_7712450 < baseStart_7712450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712452 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_7712452 : Nat := 118140960795 + 7712452 * 2 ^ 59
def prefixEnd_7712452 : Nat := 4983230072969 + 3 ^ 40 * 7712452 * 2
def baseEnd_7712452 : Nat := 3960194900729764229781085

theorem tailTrace_7712452 : CollatzResearch.WordTrace tailWord_7712452 prefixEnd_7712452 3960194900729764229781085 := by
  unfold tailWord_7712452
  simp only [CollatzResearch.WordTrace]
  refine ⟨140648116927555530390249805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187530822570074040520333073 140648116927555530390249805)
  ·
    refine ⟨52743043847833323896343677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140648116927555530390249805 52743043847833323896343677)
    ·
      refine ⟨19778641442937496461128879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52743043847833323896343677 19778641442937496461128879)
      ·
        refine ⟨29667962164406244691693319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778641442937496461128879 29667962164406244691693319)
        ·
          refine ⟨44501943246609367037539979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29667962164406244691693319 44501943246609367037539979)
          ·
            refine ⟨66752914869914050556309969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44501943246609367037539979 66752914869914050556309969)
            ·
              refine ⟨50064686152435537917232477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66752914869914050556309969 50064686152435537917232477)
              ·
                refine ⟨18774257307163326718962179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50064686152435537917232477 18774257307163326718962179)
                ·
                  refine ⟨28161385960744990078443269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774257307163326718962179 28161385960744990078443269)
                  ·
                    refine ⟨5280259867639685639708113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28161385960744990078443269 5280259867639685639708113)
                    ·
                      refine ⟨3960194900729764229781085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280259867639685639708113 3960194900729764229781085)
                      ·
                        rfl

theorem cell23_7712452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_7712452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712452 prefixEnd_7712452 := by exact prefixLift 7712452
  have htrace : WordTrace (prefixWord ++ tailWord_7712452) baseStart_7712452 baseEnd_7712452 := by
    simpa [prefixWord, tailWord_7712452, baseEnd_7712452] using wordTrace_append hprefix tailTrace_7712452
  have hstable : (prefixWord ++ tailWord_7712452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712452).length < 2 ^ (prefixWord ++ tailWord_7712452).sum := by decide
  have hdescent : baseEnd_7712452 < baseStart_7712452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712485 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_7712485 : Nat := 118140960795 + 7712485 * 2 ^ 59
def prefixEnd_7712485 : Nat := 4983230072969 + 3 ^ 40 * 7712485 * 2
def baseEnd_7712485 : Nat := 3960211845591362600668433

theorem tailTrace_7712485 : CollatzResearch.WordTrace tailWord_7712485 prefixEnd_7712485 3960211845591362600668433 := by
  unfold tailWord_7712485
  simp only [CollatzResearch.WordTrace]
  refine ⟨281297437463991507416450909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187531624975994338277633939 281297437463991507416450909)
  ·
    refine ⟨105486539048996815281169091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281297437463991507416450909 105486539048996815281169091)
    ·
      refine ⟨158229808573495222921753637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105486539048996815281169091 158229808573495222921753637)
      ·
        refine ⟨29668089107530354297828807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158229808573495222921753637 29668089107530354297828807)
        ·
          refine ⟨44502133661295531446743211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29668089107530354297828807 44502133661295531446743211)
          ·
            refine ⟨66753200491943297170114817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44502133661295531446743211 66753200491943297170114817)
            ·
              refine ⟨50064900368957472877586113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66753200491943297170114817 50064900368957472877586113)
              ·
                refine ⟨37548675276718104658189585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50064900368957472877586113 37548675276718104658189585)
                ·
                  refine ⟨28161506457538578493642189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37548675276718104658189585 28161506457538578493642189)
                  ·
                    refine ⟨10560564921576966935115821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28161506457538578493642189 10560564921576966935115821)
                    ·
                      refine ⟨3960211845591362600668433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560564921576966935115821 3960211845591362600668433)
                      ·
                        rfl

theorem cell23_7712485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_7712485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712485 prefixEnd_7712485 := by exact prefixLift 7712485
  have htrace : WordTrace (prefixWord ++ tailWord_7712485) baseStart_7712485 baseEnd_7712485 := by
    simpa [prefixWord, tailWord_7712485, baseEnd_7712485] using wordTrace_append hprefix tailTrace_7712485
  have hstable : (prefixWord ++ tailWord_7712485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712485).length < 2 ^ (prefixWord ++ tailWord_7712485).sum := by decide
  have hdescent : baseEnd_7712485 < baseStart_7712485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712492 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 5]
def baseStart_7712492 : Nat := 118140960795 + 7712492 * 2 ^ 59
def prefixEnd_7712492 : Nat := 4983230072969 + 3 ^ 40 * 7712492 * 2
def baseEnd_7712492 : Nat := 440023937772882674808989

theorem tailTrace_7712492 : CollatzResearch.WordTrace tailWord_7712492 prefixEnd_7712492 440023937772882674808989 := by
  unfold tailWord_7712492
  simp only [CollatzResearch.WordTrace]
  refine ⟨140648846387483073805977865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187531795183310765074637153 140648846387483073805977865)
  ·
    refine ⟨105486634790612305354483399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140648846387483073805977865 105486634790612305354483399)
    ·
      refine ⟨158229952185918458031725099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105486634790612305354483399 158229952185918458031725099)
      ·
        refine ⟨237344928278877687047587649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158229952185918458031725099 237344928278877687047587649)
        ·
          refine ⟨178008696209158265285690737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237344928278877687047587649 178008696209158265285690737)
          ·
            refine ⟨133506522156868698964268053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178008696209158265285690737 133506522156868698964268053)
            ·
              refine ⟨6258118226103220263950065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133506522156868698964268053 6258118226103220263950065)
              ·
                refine ⟨4693588669577415197962549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258118226103220263950065 4693588669577415197962549)
                ·
                  refine ⟨440023937772882674808989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4693588669577415197962549 440023937772882674808989)
                  ·
                    rfl

theorem cell23_7712492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_7712492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712492 prefixEnd_7712492 := by exact prefixLift 7712492
  have htrace : WordTrace (prefixWord ++ tailWord_7712492) baseStart_7712492 baseEnd_7712492 := by
    simpa [prefixWord, tailWord_7712492, baseEnd_7712492] using wordTrace_append hprefix tailTrace_7712492
  have hstable : (prefixWord ++ tailWord_7712492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712492).length < 2 ^ (prefixWord ++ tailWord_7712492).sum := by decide
  have hdescent : baseEnd_7712492 < baseStart_7712492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712495 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 7, 2]
def baseStart_7712495 : Nat := 118140960795 + 7712495 * 2 ^ 59
def prefixEnd_7712495 : Nat := 4983230072969 + 3 ^ 40 * 7712495 * 2
def baseEnd_7712495 : Nat := 3960216980397907561543387

theorem tailTrace_7712495 : CollatzResearch.WordTrace tailWord_7712495 prefixEnd_7712495 3960216980397907561543387 := by
  unfold tailWord_7712495
  simp only [CollatzResearch.WordTrace]
  refine ⟨281297802193955279124314939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187531868129303519416209959 281297802193955279124314939)
  ·
    refine ⟨421946703290932918686472409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281297802193955279124314939 421946703290932918686472409)
    ·
      refine ⟨316460027468199689014854307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421946703290932918686472409 316460027468199689014854307)
      ·
        refine ⟨474690041202299533522281461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316460027468199689014854307 474690041202299533522281461)
        ·
          refine ⟨44502191362715581267713887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474690041202299533522281461 44502191362715581267713887)
          ·
            refine ⟨66753287044073371901570831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44502191362715581267713887 66753287044073371901570831)
            ·
              refine ⟨100129930566110057852356247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66753287044073371901570831 100129930566110057852356247)
              ·
                refine ⟨150194895849165086778534371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100129930566110057852356247 150194895849165086778534371)
                ·
                  refine ⟨225292343773747630167801557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150194895849165086778534371 225292343773747630167801557)
                  ·
                    refine ⟨5280289307197210082057849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225292343773747630167801557 5280289307197210082057849)
                    ·
                      refine ⟨3960216980397907561543387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280289307197210082057849 3960216980397907561543387)
                      ·
                        rfl

theorem cell23_7712495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7, 2].length) (baseStart_7712495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712495 prefixEnd_7712495 := by exact prefixLift 7712495
  have htrace : WordTrace (prefixWord ++ tailWord_7712495) baseStart_7712495 baseEnd_7712495 := by
    simpa [prefixWord, tailWord_7712495, baseEnd_7712495] using wordTrace_append hprefix tailTrace_7712495
  have hstable : (prefixWord ++ tailWord_7712495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712495).length < 2 ^ (prefixWord ++ tailWord_7712495).sum := by decide
  have hdescent : baseEnd_7712495 < baseStart_7712495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712502 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7712502 : Nat := 118140960795 + 7712502 * 2 ^ 59
def prefixEnd_7712502 : Nat := 4983230072969 + 3 ^ 40 * 7712502 * 2
def baseEnd_7712502 : Nat := 3960220574762489034155855

theorem tailTrace_7712502 : CollatzResearch.WordTrace tailWord_7712502 prefixEnd_7712502 3960220574762489034155855 := by
  unfold tailWord_7712502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581128594058119957488735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187532038336619946213213173 17581128594058119957488735)
  ·
    refine ⟨26371692891087179936233103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17581128594058119957488735 26371692891087179936233103)
    ·
      refine ⟨39557539336630769904349655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26371692891087179936233103 39557539336630769904349655)
      ·
        refine ⟨59336309004946154856524483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39557539336630769904349655 59336309004946154856524483)
        ·
          refine ⟨89004463507419232284786725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59336309004946154856524483 89004463507419232284786725)
          ·
            refine ⟨16688336907641106053397511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89004463507419232284786725 16688336907641106053397511)
            ·
              refine ⟨25032505361461659080096267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16688336907641106053397511 25032505361461659080096267)
              ·
                refine ⟨37548758042192488620144401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25032505361461659080096267 37548758042192488620144401)
                ·
                  refine ⟨28161568531644366465108301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37548758042192488620144401 28161568531644366465108301)
                  ·
                    refine ⟨10560588199366637424415613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28161568531644366465108301 10560588199366637424415613)
                    ·
                      refine ⟨3960220574762489034155855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560588199366637424415613 3960220574762489034155855)
                      ·
                        rfl

theorem cell23_7712502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7712502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712502 prefixEnd_7712502 := by exact prefixLift 7712502
  have htrace : WordTrace (prefixWord ++ tailWord_7712502) baseStart_7712502 baseEnd_7712502 := by
    simpa [prefixWord, tailWord_7712502, baseEnd_7712502] using wordTrace_append hprefix tailTrace_7712502
  have hstable : (prefixWord ++ tailWord_7712502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712502).length < 2 ^ (prefixWord ++ tailWord_7712502).sum := by decide
  have hdescent : baseEnd_7712502 < baseStart_7712502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712522 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_7712522 : Nat := 118140960795 + 7712522 * 2 ^ 59
def prefixEnd_7712522 : Nat := 4983230072969 + 3 ^ 40 * 7712522 * 2
def baseEnd_7712522 : Nat := 1320076948125192985301921

theorem tailTrace_7712522 : CollatzResearch.WordTrace tailWord_7712522 prefixEnd_7712522 1320076948125192985301921 := by
  unfold tailWord_7712522
  simp only [CollatzResearch.WordTrace]
  refine ⟨70324696741214365683886955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187532524643238308490365213 70324696741214365683886955)
  ·
    refine ⟨105487045111821548525830433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70324696741214365683886955 105487045111821548525830433)
    ·
      refine ⟨79115283833866161394372825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105487045111821548525830433 79115283833866161394372825)
      ·
        refine ⟨59336462875399621045779619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79115283833866161394372825 59336462875399621045779619)
        ·
          refine ⟨89004694313099431568669429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59336462875399621045779619 89004694313099431568669429)
          ·
            refine ⟨8344190091853071709562759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89004694313099431568669429 8344190091853071709562759)
            ·
              refine ⟨12516285137779607564344139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344190091853071709562759 12516285137779607564344139)
              ·
                refine ⟨18774427706669411346516209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516285137779607564344139 18774427706669411346516209)
                ·
                  refine ⟨14080820780002058509887157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18774427706669411346516209 14080820780002058509887157)
                  ·
                    refine ⟨1320076948125192985301921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14080820780002058509887157 1320076948125192985301921)
                    ·
                      rfl

theorem cell23_7712522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_7712522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712522 prefixEnd_7712522 := by exact prefixLift 7712522
  have htrace : WordTrace (prefixWord ++ tailWord_7712522) baseStart_7712522 baseEnd_7712522 := by
    simpa [prefixWord, tailWord_7712522, baseEnd_7712522] using wordTrace_append hprefix tailTrace_7712522
  have hstable : (prefixWord ++ tailWord_7712522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712522).length < 2 ^ (prefixWord ++ tailWord_7712522).sum := by decide
  have hdescent : baseEnd_7712522 < baseStart_7712522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712552 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7712552 : Nat := 118140960795 + 7712552 * 2 ^ 59
def prefixEnd_7712552 : Nat := 4983230072969 + 3 ^ 40 * 7712552 * 2
def baseEnd_7712552 : Nat := 1320082082931737946176875

theorem tailTrace_7712552 : CollatzResearch.WordTrace tailWord_7712552 prefixEnd_7712552 1320082082931737946176875 := by
  unfold tailWord_7712552
  simp only [CollatzResearch.WordTrace]
  refine ⟨140649940577374388929569955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187533254103165851906093273 140649940577374388929569955)
  ·
    refine ⟨210974910866061583394354933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140649940577374388929569955 210974910866061583394354933)
    ·
      refine ⟨19778897893693273443220775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210974910866061583394354933 19778897893693273443220775)
      ·
        refine ⟨29668346840539910164831163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778897893693273443220775 29668346840539910164831163)
        ·
          refine ⟨44502520260809865247246745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29668346840539910164831163 44502520260809865247246745)
          ·
            refine ⟨33376890195607398935435059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44502520260809865247246745 33376890195607398935435059)
            ·
              refine ⟨50065335293411098403152589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33376890195607398935435059 50065335293411098403152589)
              ·
                refine ⟨18774500735029161901182221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50065335293411098403152589 18774500735029161901182221)
                ·
                  refine ⟨7040437775635935712943333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18774500735029161901182221 7040437775635935712943333)
                  ·
                    refine ⟨1320082082931737946176875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040437775635935712943333 1320082082931737946176875)
                    ·
                      rfl

theorem cell23_7712552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7712552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712552 prefixEnd_7712552 := by exact prefixLift 7712552
  have htrace : WordTrace (prefixWord ++ tailWord_7712552) baseStart_7712552 baseEnd_7712552 := by
    simpa [prefixWord, tailWord_7712552, baseEnd_7712552] using wordTrace_append hprefix tailTrace_7712552
  have hstable : (prefixWord ++ tailWord_7712552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712552).length < 2 ^ (prefixWord ++ tailWord_7712552).sum := by decide
  have hdescent : baseEnd_7712552 < baseStart_7712552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712625 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_7712625 : Nat := 118140960795 + 7712625 * 2 ^ 59
def prefixEnd_7712625 : Nat := 4983230072969 + 3 ^ 40 * 7712625 * 2
def baseEnd_7712625 : Nat := 1320094577627664017639263

theorem tailTrace_7712625 : CollatzResearch.WordTrace tailWord_7712625 prefixEnd_7712625 1320094577627664017639263 := by
  unfold tailWord_7712625
  simp only [CollatzResearch.WordTrace]
  refine ⟨281302543683484311326547329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187535029122322874217698219 281302543683484311326547329)
  ·
    refine ⟨210976907762613233494910497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281302543683484311326547329 210976907762613233494910497)
    ·
      refine ⟨158232680821959925121182873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210976907762613233494910497 158232680821959925121182873)
      ·
        refine ⟨118674510616469943840887155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158232680821959925121182873 118674510616469943840887155)
        ·
          refine ⟨178011765924704915761330733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118674510616469943840887155 178011765924704915761330733)
          ·
            refine ⟨66754412221764343410499025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178011765924704915761330733 66754412221764343410499025)
            ·
              refine ⟨50065809166323257557874269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66754412221764343410499025 50065809166323257557874269)
              ·
                refine ⟨18774678437371221584202851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50065809166323257557874269 18774678437371221584202851)
                ·
                  refine ⟨28162017656056832376304277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774678437371221584202851 28162017656056832376304277)
                  ·
                    refine ⟨1320094577627664017639263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28162017656056832376304277 1320094577627664017639263)
                    ·
                      rfl

theorem cell23_7712625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_7712625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712625 prefixEnd_7712625 := by exact prefixLift 7712625
  have htrace : WordTrace (prefixWord ++ tailWord_7712625) baseStart_7712625 baseEnd_7712625 := by
    simpa [prefixWord, tailWord_7712625, baseEnd_7712625] using wordTrace_append hprefix tailTrace_7712625
  have hstable : (prefixWord ++ tailWord_7712625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712625).length < 2 ^ (prefixWord ++ tailWord_7712625).sum := by decide
  have hdescent : baseEnd_7712625 < baseStart_7712625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712649 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 1, 1, 4]
def baseStart_7712649 : Nat := 118140960795 + 7712649 * 2 ^ 59
def prefixEnd_7712649 : Nat := 4983230072969 + 3 ^ 40 * 7712649 * 2
def baseEnd_7712649 : Nat := 3960296056418699959017679

theorem tailTrace_7712649 : CollatzResearch.WordTrace tailWord_7712649 prefixEnd_7712649 3960296056418699959017679 := by
  unfold tailWord_7712649
  simp only [CollatzResearch.WordTrace]
  refine ⟨281303419035397363425421001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187535612690264908950280667 281303419035397363425421001)
  ·
    refine ⟨210977564276548022569065751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281303419035397363425421001 210977564276548022569065751)
    ·
      refine ⟨316466346414822033853598627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210977564276548022569065751 316466346414822033853598627)
      ·
        refine ⟨474699519622233050780397941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316466346414822033853598627 474699519622233050780397941)
        ·
          refine ⟨44503079964584348510662307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474699519622233050780397941 44503079964584348510662307)
          ·
            refine ⟨66754619946876522765993461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44503079964584348510662307 66754619946876522765993461)
            ·
              refine ⟨6258245620019674009311887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66754619946876522765993461 6258245620019674009311887)
              ·
                refine ⟨9387368430029511013967831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258245620019674009311887 9387368430029511013967831)
                ·
                  refine ⟨14081052645044266520951747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387368430029511013967831 14081052645044266520951747)
                  ·
                    refine ⟨21121578967566399781427621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14081052645044266520951747 21121578967566399781427621)
                    ·
                      refine ⟨3960296056418699959017679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21121578967566399781427621 3960296056418699959017679)
                      ·
                        rfl

theorem cell23_7712649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 1, 4].length) (baseStart_7712649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712649 prefixEnd_7712649 := by exact prefixLift 7712649
  have htrace : WordTrace (prefixWord ++ tailWord_7712649) baseStart_7712649 baseEnd_7712649 := by
    simpa [prefixWord, tailWord_7712649, baseEnd_7712649] using wordTrace_append hprefix tailTrace_7712649
  have hstable : (prefixWord ++ tailWord_7712649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712649).length < 2 ^ (prefixWord ++ tailWord_7712649).sum := by decide
  have hdescent : baseEnd_7712649 < baseStart_7712649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712660 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_7712660 : Nat := 118140960795 + 7712660 * 2 ^ 59
def prefixEnd_7712660 : Nat := 4983230072969 + 3 ^ 40 * 7712660 * 2
def baseEnd_7712660 : Nat := 3960301704705899415980129

theorem tailTrace_7712660 : CollatzResearch.WordTrace tailWord_7712660 prefixEnd_7712660 3960301704705899415980129 := by
  unfold tailWord_7712660
  simp only [CollatzResearch.WordTrace]
  refine ⟨140651910119178756152035717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187535880158905008202714289 140651910119178756152035717)
  ·
    refine ⟨26372233147346016778506697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140651910119178756152035717 26372233147346016778506697)
    ·
      refine ⟨19779174860509512583880023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26372233147346016778506697 19779174860509512583880023)
      ·
        refine ⟨29668762290764268875820035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19779174860509512583880023 29668762290764268875820035)
        ·
          refine ⟨44503143436146403313730053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29668762290764268875820035 44503143436146403313730053)
          ·
            refine ⟨8344339394277450621324385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44503143436146403313730053 8344339394277450621324385)
            ·
              refine ⟨6258254545708087965993289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344339394277450621324385 6258254545708087965993289)
              ·
                refine ⟨4693690909281065974494967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258254545708087965993289 4693690909281065974494967)
                ·
                  refine ⟨7040536363921598961742451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693690909281065974494967 7040536363921598961742451)
                  ·
                    refine ⟨10560804545882398442613677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040536363921598961742451 10560804545882398442613677)
                    ·
                      refine ⟨3960301704705899415980129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560804545882398442613677 3960301704705899415980129)
                      ·
                        rfl

theorem cell23_7712660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_7712660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712660 prefixEnd_7712660 := by exact prefixLift 7712660
  have htrace : WordTrace (prefixWord ++ tailWord_7712660) baseStart_7712660 baseEnd_7712660 := by
    simpa [prefixWord, tailWord_7712660, baseEnd_7712660] using wordTrace_append hprefix tailTrace_7712660
  have hstable : (prefixWord ++ tailWord_7712660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712660).length < 2 ^ (prefixWord ++ tailWord_7712660).sum := by decide
  have hdescent : baseEnd_7712660 < baseStart_7712660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712679 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7712679 : Nat := 118140960795 + 7712679 * 2 ^ 59
def prefixEnd_7712679 : Nat := 4983230072969 + 3 ^ 40 * 7712679 * 2
def baseEnd_7712679 : Nat := 3960311460838334841642541

theorem tailTrace_7712679 : CollatzResearch.WordTrace tailWord_7712679 prefixEnd_7712679 3960311460838334841642541 := by
  unfold tailWord_7712679
  simp only [CollatzResearch.WordTrace]
  refine ⟨281304513225288678549013091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187536342150192452366008727 281304513225288678549013091)
  ·
    refine ⟨421956769837933017823519637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281304513225288678549013091 421956769837933017823519637)
    ·
      refine ⟨19779223586153110210477483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 421956769837933017823519637 19779223586153110210477483)
      ·
        refine ⟨29668835379229665315716225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19779223586153110210477483 29668835379229665315716225)
        ·
          refine ⟨22251626534422248986787169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29668835379229665315716225 22251626534422248986787169)
          ·
            refine ⟨16688719900816686740090377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22251626534422248986787169 16688719900816686740090377)
            ·
              refine ⟨12516539925612515055067783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16688719900816686740090377 12516539925612515055067783)
              ·
                refine ⟨18774809888418772582601675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516539925612515055067783 18774809888418772582601675)
                ·
                  refine ⟨28162214832628158873902513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774809888418772582601675 28162214832628158873902513)
                  ·
                    refine ⟨21121661124471119155426885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28162214832628158873902513 21121661124471119155426885)
                    ·
                      refine ⟨3960311460838334841642541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21121661124471119155426885 3960311460838334841642541)
                      ·
                        rfl

theorem cell23_7712679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7712679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712679 prefixEnd_7712679 := by exact prefixLift 7712679
  have htrace : WordTrace (prefixWord ++ tailWord_7712679) baseStart_7712679 baseEnd_7712679 := by
    simpa [prefixWord, tailWord_7712679, baseEnd_7712679] using wordTrace_append hprefix tailTrace_7712679
  have hstable : (prefixWord ++ tailWord_7712679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712679).length < 2 ^ (prefixWord ++ tailWord_7712679).sum := by decide
  have hdescent : baseEnd_7712679 < baseStart_7712679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712695 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_7712695 : Nat := 118140960795 + 7712695 * 2 ^ 59
def prefixEnd_7712695 : Nat := 4983230072969 + 3 ^ 40 * 7712695 * 2
def baseEnd_7712695 : Nat := 3960319676528806779042467

theorem tailTrace_7712695 : CollatzResearch.WordTrace tailWord_7712695 prefixEnd_7712695 3960319676528806779042467 := by
  unfold tailWord_7712695
  simp only [CollatzResearch.WordTrace]
  refine ⟨281305096793230713281595539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187536731195487142187730359 281305096793230713281595539)
  ·
    refine ⟨421957645189846069922393309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281305096793230713281595539 421957645189846069922393309)
    ·
      refine ⟨158234116946192276220897491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421957645189846069922393309 158234116946192276220897491)
      ·
        refine ⟨237351175419288414331346237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158234116946192276220897491 237351175419288414331346237)
        ·
          refine ⟨89006690782233155374254839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237351175419288414331346237 89006690782233155374254839)
          ·
            refine ⟨133510036173349733061382259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89006690782233155374254839 133510036173349733061382259)
            ·
              refine ⟨200265054260024599592073389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133510036173349733061382259 200265054260024599592073389)
              ·
                refine ⟨75099395347509224847027521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200265054260024599592073389 75099395347509224847027521)
                ·
                  refine ⟨56324546510631918635270641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75099395347509224847027521 56324546510631918635270641)
                  ·
                    refine ⟨42243409882973938976452981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56324546510631918635270641 42243409882973938976452981)
                    ·
                      refine ⟨3960319676528806779042467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42243409882973938976452981 3960319676528806779042467)
                      ·
                        rfl

theorem cell23_7712695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_7712695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712695 prefixEnd_7712695 := by exact prefixLift 7712695
  have htrace : WordTrace (prefixWord ++ tailWord_7712695) baseStart_7712695 baseEnd_7712695 := by
    simpa [prefixWord, tailWord_7712695, baseEnd_7712695] using wordTrace_append hprefix tailTrace_7712695
  have hstable : (prefixWord ++ tailWord_7712695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712695).length < 2 ^ (prefixWord ++ tailWord_7712695).sum := by decide
  have hdescent : baseEnd_7712695 < baseStart_7712695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712700 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7712700 : Nat := 118140960795 + 7712700 * 2 ^ 59
def prefixEnd_7712700 : Nat := 4983230072969 + 3 ^ 40 * 7712700 * 2
def baseEnd_7712700 : Nat := 3960322243932079259479945

theorem tailTrace_7712700 : CollatzResearch.WordTrace tailWord_7712700 prefixEnd_7712700 3960322243932079259479945 := by
  unfold tailWord_7712700
  simp only [CollatzResearch.WordTrace]
  refine ⟨140652639579106299567763777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187536852772141732757018369 140652639579106299567763777)
  ·
    refine ⟨105489479684329724675822833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140652639579106299567763777 105489479684329724675822833)
    ·
      refine ⟨79117109763247293506867125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105489479684329724675822833 79117109763247293506867125)
      ·
        refine ⟨7417229040304433766268793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79117109763247293506867125 7417229040304433766268793)
        ·
          refine ⟨5562921780228325324701595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7417229040304433766268793 5562921780228325324701595)
          ·
            refine ⟨8344382670342487987052393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562921780228325324701595 8344382670342487987052393)
            ·
              refine ⟨6258287002756865990289295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344382670342487987052393 6258287002756865990289295)
              ·
                refine ⟨9387430504135298985433943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258287002756865990289295 9387430504135298985433943)
                ·
                  refine ⟨14081145756202948478150915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387430504135298985433943 14081145756202948478150915)
                  ·
                    refine ⟨21121718634304422717226373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14081145756202948478150915 21121718634304422717226373)
                    ·
                      refine ⟨3960322243932079259479945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21121718634304422717226373 3960322243932079259479945)
                      ·
                        rfl

theorem cell23_7712700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7712700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712700 prefixEnd_7712700 := by exact prefixLift 7712700
  have htrace : WordTrace (prefixWord ++ tailWord_7712700) baseStart_7712700 baseEnd_7712700 := by
    simpa [prefixWord, tailWord_7712700, baseEnd_7712700] using wordTrace_append hprefix tailTrace_7712700
  have hstable : (prefixWord ++ tailWord_7712700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712700).length < 2 ^ (prefixWord ++ tailWord_7712700).sum := by decide
  have hdescent : baseEnd_7712700 < baseStart_7712700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712715 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 4, 6]
def baseStart_7712715 : Nat := 118140960795 + 7712715 * 2 ^ 59
def prefixEnd_7712715 : Nat := 4983230072969 + 3 ^ 40 * 7712715 * 2
def baseEnd_7712715 : Nat := 1320109982047298900264125

theorem tailTrace_7712715 : CollatzResearch.WordTrace tailWord_7712715 prefixEnd_7712715 1320109982047298900264125 := by
  unfold tailWord_7712715
  simp only [CollatzResearch.WordTrace]
  refine ⟨281305826253158256697323599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187537217502105504464882399 281305826253158256697323599)
  ·
    refine ⟨421958739379737385045985399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281305826253158256697323599 421958739379737385045985399)
    ·
      refine ⟨632938109069606077568978099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421958739379737385045985399 632938109069606077568978099)
      ·
        refine ⟨949407163604409116353467149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632938109069606077568978099 949407163604409116353467149)
        ·
          refine ⟨356027686351653418632550181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949407163604409116353467149 356027686351653418632550181)
          ·
            refine ⟨66755191190935015993603159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356027686351653418632550181 66755191190935015993603159)
            ·
              refine ⟨100132786786402523990404739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66755191190935015993603159 100132786786402523990404739)
              ·
                refine ⟨150199180179603785985607109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100132786786402523990404739 150199180179603785985607109)
                ·
                  refine ⟨28162346283675709872301333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150199180179603785985607109 28162346283675709872301333)
                  ·
                    refine ⟨1320109982047298900264125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28162346283675709872301333 1320109982047298900264125)
                    ·
                      rfl

theorem cell23_7712715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_7712715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712715 prefixEnd_7712715 := by exact prefixLift 7712715
  have htrace : WordTrace (prefixWord ++ tailWord_7712715) baseStart_7712715 baseEnd_7712715 := by
    simpa [prefixWord, tailWord_7712715, baseEnd_7712715] using wordTrace_append hprefix tailTrace_7712715
  have hstable : (prefixWord ++ tailWord_7712715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712715).length < 2 ^ (prefixWord ++ tailWord_7712715).sum := by decide
  have hdescent : baseEnd_7712715 < baseStart_7712715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712716 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7712716 : Nat := 118140960795 + 7712716 * 2 ^ 59
def prefixEnd_7712716 : Nat := 4983230072969 + 3 ^ 40 * 7712716 * 2
def baseEnd_7712716 : Nat := 3960330459622551196879871

theorem tailTrace_7712716 : CollatzResearch.WordTrace tailWord_7712716 prefixEnd_7712716 3960330459622551196879871 := by
  unfold tailWord_7712716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140652931363077316934055001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187537241817436422578740001 140652931363077316934055001)
  ·
    refine ⟨105489698522307987700541251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140652931363077316934055001 105489698522307987700541251)
    ·
      refine ⟨158234547783461981550811877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105489698522307987700541251 158234547783461981550811877)
      ·
        refine ⟨29668977709399121540777227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158234547783461981550811877 29668977709399121540777227)
        ·
          refine ⟨44503466564098682311165841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29668977709399121540777227 44503466564098682311165841)
          ·
            refine ⟨33377599923074011733374381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44503466564098682311165841 33377599923074011733374381)
            ·
              refine ⟨12516599971152754400015393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33377599923074011733374381 12516599971152754400015393)
              ·
                refine ⟨9387449978364565800011545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516599971152754400015393 9387449978364565800011545)
                ·
                  refine ⟨7040587483773424350008659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387449978364565800011545 7040587483773424350008659)
                  ·
                    refine ⟨10560881225660136525012989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040587483773424350008659 10560881225660136525012989)
                    ·
                      refine ⟨3960330459622551196879871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560881225660136525012989 3960330459622551196879871)
                      ·
                        rfl

theorem cell23_7712716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7712716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712716 prefixEnd_7712716 := by exact prefixLift 7712716
  have htrace : WordTrace (prefixWord ++ tailWord_7712716) baseStart_7712716 baseEnd_7712716 := by
    simpa [prefixWord, tailWord_7712716, baseEnd_7712716] using wordTrace_append hprefix tailTrace_7712716
  have hstable : (prefixWord ++ tailWord_7712716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712716).length < 2 ^ (prefixWord ++ tailWord_7712716).sum := by decide
  have hdescent : baseEnd_7712716 < baseStart_7712716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712733 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7712733 : Nat := 118140960795 + 7712733 * 2 ^ 59
def prefixEnd_7712733 : Nat := 4983230072969 + 3 ^ 40 * 7712733 * 2
def baseEnd_7712733 : Nat := 3960339188793677630367293

theorem tailTrace_7712733 : CollatzResearch.WordTrace tailWord_7712733 prefixEnd_7712733 3960339188793677630367293 := by
  unfold tailWord_7712733
  simp only [CollatzResearch.WordTrace]
  refine ⟨281306482767093045771478853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187537655178062030514319235 281306482767093045771478853)
  ·
    refine ⟨52744965518829946082152285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281306482767093045771478853 52744965518829946082152285)
    ·
      refine ⟨19779362069561229780807107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52744965518829946082152285 19779362069561229780807107)
      ·
        refine ⟨29669043104341844671210661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19779362069561229780807107 29669043104341844671210661)
        ·
          refine ⟨5562945582064095875851999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29669043104341844671210661 5562945582064095875851999)
          ·
            refine ⟨8344418373096143813777999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562945582064095875851999 8344418373096143813777999)
            ·
              refine ⟨12516627559644215720666999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344418373096143813777999 12516627559644215720666999)
              ·
                refine ⟨18774941339466323581000499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516627559644215720666999 18774941339466323581000499)
                ·
                  refine ⟨28162412009199485371500749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774941339466323581000499 28162412009199485371500749)
                  ·
                    refine ⟨10560904503449807014312781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28162412009199485371500749 10560904503449807014312781)
                    ·
                      refine ⟨3960339188793677630367293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10560904503449807014312781 3960339188793677630367293)
                      ·
                        rfl

theorem cell23_7712733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7712733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712733 prefixEnd_7712733 := by exact prefixLift 7712733
  have htrace : WordTrace (prefixWord ++ tailWord_7712733) baseStart_7712733 baseEnd_7712733 := by
    simpa [prefixWord, tailWord_7712733, baseEnd_7712733] using wordTrace_append hprefix tailTrace_7712733
  have hstable : (prefixWord ++ tailWord_7712733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712733).length < 2 ^ (prefixWord ++ tailWord_7712733).sum := by decide
  have hdescent : baseEnd_7712733 < baseStart_7712733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712743 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7712743 : Nat := 118140960795 + 7712743 * 2 ^ 59
def prefixEnd_7712743 : Nat := 4983230072969 + 3 ^ 40 * 7712743 * 2
def baseEnd_7712743 : Nat := 3960344323600222591242247

theorem tailTrace_7712743 : CollatzResearch.WordTrace tailWord_7712743 prefixEnd_7712743 3960344323600222591242247 := by
  unfold tailWord_7712743
  simp only [CollatzResearch.WordTrace]
  refine ⟨281306847497056817479342883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187537898331371211652895255 281306847497056817479342883)
  ·
    refine ⟨421960271245585226219014325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281306847497056817479342883 421960271245585226219014325)
    ·
      refine ⟨39558775429273614958032593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421960271245585226219014325 39558775429273614958032593)
      ·
        refine ⟨29669081571955211218524445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39558775429273614958032593 29669081571955211218524445)
        ·
          refine ⟨11125905589483204206946667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29669081571955211218524445 11125905589483204206946667)
          ·
            refine ⟨16688858384224806310420001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125905589483204206946667 16688858384224806310420001)
            ·
              refine ⟨12516643788168604732815001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16688858384224806310420001 12516643788168604732815001)
              ·
                refine ⟨9387482841126453549611251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516643788168604732815001 9387482841126453549611251)
                ·
                  refine ⟨14081224261689680324416877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387482841126453549611251 14081224261689680324416877)
                  ·
                    refine ⟨5280459098133630121656329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14081224261689680324416877 5280459098133630121656329)
                    ·
                      refine ⟨3960344323600222591242247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280459098133630121656329 3960344323600222591242247)
                      ·
                        rfl

theorem cell23_7712743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7712743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712743 prefixEnd_7712743 := by exact prefixLift 7712743
  have htrace : WordTrace (prefixWord ++ tailWord_7712743) baseStart_7712743 baseEnd_7712743 := by
    simpa [prefixWord, tailWord_7712743, baseEnd_7712743] using wordTrace_append hprefix tailTrace_7712743
  have hstable : (prefixWord ++ tailWord_7712743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712743).length < 2 ^ (prefixWord ++ tailWord_7712743).sum := by decide
  have hdescent : baseEnd_7712743 < baseStart_7712743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712792 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_7712792 : Nat := 118140960795 + 7712792 * 2 ^ 59
def prefixEnd_7712792 : Nat := 4983230072969 + 3 ^ 40 * 7712792 * 2
def baseEnd_7712792 : Nat := 1320123161384097633176507

theorem tailTrace_7712792 : CollatzResearch.WordTrace tailWord_7712792 prefixEnd_7712792 1320123161384097633176507 := by
  unfold tailWord_7712792
  simp only [CollatzResearch.WordTrace]
  refine ⟨140654317336939649423938315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187539089782586199231917753 140654317336939649423938315)
  ·
    refine ⟨210981476005409474135907473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140654317336939649423938315 210981476005409474135907473)
    ·
      refine ⟨158236107004057105601930605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210981476005409474135907473 158236107004057105601930605)
      ·
        refine ⟨59338540126521414600723977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158236107004057105601930605 59338540126521414600723977)
        ·
          refine ⟨44503905094891060950542983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59338540126521414600723977 44503905094891060950542983)
          ·
            refine ⟨66755857642336591425814475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44503905094891060950542983 66755857642336591425814475)
            ·
              refine ⟨100133786463504887138721713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66755857642336591425814475 100133786463504887138721713)
              ·
                refine ⟨75100339847628665354041285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100133786463504887138721713 75100339847628665354041285)
                ·
                  refine ⟨14081313721430374753882741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75100339847628665354041285 14081313721430374753882741)
                  ·
                    refine ⟨1320123161384097633176507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14081313721430374753882741 1320123161384097633176507)
                    ·
                      rfl

theorem cell23_7712792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_7712792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712792 prefixEnd_7712792 := by exact prefixLift 7712792
  have htrace : WordTrace (prefixWord ++ tailWord_7712792) baseStart_7712792 baseEnd_7712792 := by
    simpa [prefixWord, tailWord_7712792, baseEnd_7712792] using wordTrace_append hprefix tailTrace_7712792
  have hstable : (prefixWord ++ tailWord_7712792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712792).length < 2 ^ (prefixWord ++ tailWord_7712792).sum := by decide
  have hdescent : baseEnd_7712792 < baseStart_7712792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712802 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7712802 : Nat := 118140960795 + 7712802 * 2 ^ 59
def prefixEnd_7712802 : Nat := 4983230072969 + 3 ^ 40 * 7712802 * 2
def baseEnd_7712802 : Nat := 3960374618958837860404475

theorem tailTrace_7712802 : CollatzResearch.WordTrace tailWord_7712802 prefixEnd_7712802 3960374618958837860404475 := by
  unfold tailWord_7712802
  simp only [CollatzResearch.WordTrace]
  refine ⟨70327249850960767638935165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187539332935895380370493773 70327249850960767638935165)
  ·
    refine ⟨26372718694110287864600687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70327249850960767638935165 26372718694110287864600687)
    ·
      refine ⟨39559078041165431796901031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26372718694110287864600687 39559078041165431796901031)
      ·
        refine ⟨59338617061748147695351547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39559078041165431796901031 59338617061748147695351547)
        ·
          refine ⟨89007925592622221543027321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59338617061748147695351547 89007925592622221543027321)
          ·
            refine ⟨66755944194466666157270491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89007925592622221543027321 66755944194466666157270491)
            ·
              refine ⟨100133916291699999235905737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66755944194466666157270491 100133916291699999235905737)
              ·
                refine ⟨75100437218774999426929303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100133916291699999235905737 75100437218774999426929303)
                ·
                  refine ⟨112650655828162499140393955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75100437218774999426929303 112650655828162499140393955)
                  ·
                    refine ⟨168975983742243748710590933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112650655828162499140393955 168975983742243748710590933)
                    ·
                      refine ⟨3960374618958837860404475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168975983742243748710590933 3960374618958837860404475)
                      ·
                        rfl

theorem cell23_7712802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7712802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712802 prefixEnd_7712802 := by exact prefixLift 7712802
  have htrace : WordTrace (prefixWord ++ tailWord_7712802) baseStart_7712802 baseEnd_7712802 := by
    simpa [prefixWord, tailWord_7712802, baseEnd_7712802] using wordTrace_append hprefix tailTrace_7712802
  have hstable : (prefixWord ++ tailWord_7712802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712802).length < 2 ^ (prefixWord ++ tailWord_7712802).sum := by decide
  have hdescent : baseEnd_7712802 < baseStart_7712802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712829 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7712829 : Nat := 118140960795 + 7712829 * 2 ^ 59
def prefixEnd_7712829 : Nat := 4983230072969 + 3 ^ 40 * 7712829 * 2
def baseEnd_7712829 : Nat := 3960388482936509254766851

theorem tailTrace_7712829 : CollatzResearch.WordTrace tailWord_7712829 prefixEnd_7712829 3960388482936509254766851 := by
  unfold tailWord_7712829
  simp only [CollatzResearch.WordTrace]
  refine ⟨281309984174745254166973541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187539989449830169444649027 281309984174745254166973541)
  ·
    refine ⟨52745622032764735156307539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281309984174745254166973541 52745622032764735156307539)
    ·
      refine ⟨79118433049147102734461309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52745622032764735156307539 79118433049147102734461309)
      ·
        refine ⟨29669412393430163525422991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79118433049147102734461309 29669412393430163525422991)
        ·
          refine ⟨44504118590145245288134487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29669412393430163525422991 44504118590145245288134487)
          ·
            refine ⟨66756177885217867932201731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44504118590145245288134487 66756177885217867932201731)
            ·
              refine ⟨100134266827826801898302597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66756177885217867932201731 100134266827826801898302597)
              ·
                refine ⟨18775175030217525355931737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100134266827826801898302597 18775175030217525355931737)
                ·
                  refine ⟨14081381272663144016948803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18775175030217525355931737 14081381272663144016948803)
                  ·
                    refine ⟨21122071908994716025423205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14081381272663144016948803 21122071908994716025423205)
                    ·
                      refine ⟨3960388482936509254766851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21122071908994716025423205 3960388482936509254766851)
                      ·
                        rfl

theorem cell23_7712829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7712829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712829 prefixEnd_7712829 := by exact prefixLift 7712829
  have htrace : WordTrace (prefixWord ++ tailWord_7712829) baseStart_7712829 baseEnd_7712829 := by
    simpa [prefixWord, tailWord_7712829, baseEnd_7712829] using wordTrace_append hprefix tailTrace_7712829
  have hstable : (prefixWord ++ tailWord_7712829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712829).length < 2 ^ (prefixWord ++ tailWord_7712829).sum := by decide
  have hdescent : baseEnd_7712829 < baseStart_7712829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712830 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_7712830 : Nat := 118140960795 + 7712830 * 2 ^ 59
def prefixEnd_7712830 : Nat := 4983230072969 + 3 ^ 40 * 7712830 * 2
def baseEnd_7712830 : Nat := 440043221824129305650483

theorem tailTrace_7712830 : CollatzResearch.WordTrace tailWord_7712830 prefixEnd_7712830 440043221824129305650483 := by
  unfold tailWord_7712830
  simp only [CollatzResearch.WordTrace]
  refine ⟨35163752580967703917219993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187540013765161087558506629 35163752580967703917219993)
  ·
    refine ⟨26372814435725777937914995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35163752580967703917219993 26372814435725777937914995)
    ·
      refine ⟨39559221653588666906872493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26372814435725777937914995 39559221653588666906872493)
      ·
        refine ⟨14834708120095750090077185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39559221653588666906872493 14834708120095750090077185)
        ·
          refine ⟨11126031090071812567557889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14834708120095750090077185 11126031090071812567557889)
          ·
            refine ⟨8344523317553859425668417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11126031090071812567557889 8344523317553859425668417)
            ·
              refine ⟨6258392488165394569251313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344523317553859425668417 6258392488165394569251313)
              ·
                refine ⟨4693794366124045926938485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258392488165394569251313 4693794366124045926938485)
                ·
                  refine ⟨440043221824129305650483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4693794366124045926938485 440043221824129305650483)
                  ·
                    rfl

theorem cell23_7712830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_7712830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712830 prefixEnd_7712830 := by exact prefixLift 7712830
  have htrace : WordTrace (prefixWord ++ tailWord_7712830) baseStart_7712830 baseEnd_7712830 := by
    simpa [prefixWord, tailWord_7712830, baseEnd_7712830] using wordTrace_append hprefix tailTrace_7712830
  have hstable : (prefixWord ++ tailWord_7712830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712830).length < 2 ^ (prefixWord ++ tailWord_7712830).sum := by decide
  have hdescent : baseEnd_7712830 < baseStart_7712830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712839 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 3, 4]
def baseStart_7712839 : Nat := 118140960795 + 7712839 * 2 ^ 59
def prefixEnd_7712839 : Nat := 4983230072969 + 3 ^ 40 * 7712839 * 2
def baseEnd_7712839 : Nat := 1320131205914351405213935

theorem tailTrace_7712839 : CollatzResearch.WordTrace tailWord_7712839 prefixEnd_7712839 1320131205914351405213935 := by
  unfold tailWord_7712839
  simp only [CollatzResearch.WordTrace]
  refine ⟨281310348904709025874837571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187540232603139350583225047 281310348904709025874837571)
  ·
    refine ⟨421965523357063538812256357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281310348904709025874837571 421965523357063538812256357)
    ·
      refine ⟨79118535629449413527298067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421965523357063538812256357 79118535629449413527298067)
      ·
        refine ⟨118677803444174120290947101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79118535629449413527298067 118677803444174120290947101)
        ·
          refine ⟨44504176291565295109105163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118677803444174120290947101 44504176291565295109105163)
          ·
            refine ⟨66756264437347942663657745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44504176291565295109105163 66756264437347942663657745)
            ·
              refine ⟨50067198328010956997743309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66756264437347942663657745 50067198328010956997743309)
              ·
                refine ⟨18775199373004108874153741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50067198328010956997743309 18775199373004108874153741)
                ·
                  refine ⟨7040699764876540827807653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18775199373004108874153741 7040699764876540827807653)
                  ·
                    refine ⟨1320131205914351405213935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040699764876540827807653 1320131205914351405213935)
                    ·
                      rfl

theorem cell23_7712839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_7712839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712839 prefixEnd_7712839 := by exact prefixLift 7712839
  have htrace : WordTrace (prefixWord ++ tailWord_7712839) baseStart_7712839 baseEnd_7712839 := by
    simpa [prefixWord, tailWord_7712839, baseEnd_7712839] using wordTrace_append hprefix tailTrace_7712839
  have hstable : (prefixWord ++ tailWord_7712839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712839).length < 2 ^ (prefixWord ++ tailWord_7712839).sum := by decide
  have hdescent : baseEnd_7712839 < baseStart_7712839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712842 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_7712842 : Nat := 118140960795 + 7712842 * 2 ^ 59
def prefixEnd_7712842 : Nat := 4983230072969 + 3 ^ 40 * 7712842 * 2
def baseEnd_7712842 : Nat := 3960395158185017703904291

theorem tailTrace_7712842 : CollatzResearch.WordTrace tailWord_7712842 prefixEnd_7712842 3960395158185017703904291 := by
  unfold tailWord_7712842
  simp only [CollatzResearch.WordTrace]
  refine ⟨70327614580924539346799195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187540305549132104924797853 70327614580924539346799195)
  ·
    refine ⟨105491421871386809020198793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70327614580924539346799195 105491421871386809020198793)
    ·
      refine ⟨79118566403540106765149095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105491421871386809020198793 79118566403540106765149095)
      ·
        refine ⟨118677849605310160147723643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79118566403540106765149095 118677849605310160147723643)
        ·
          refine ⟨178016774407965240221585465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118677849605310160147723643 178016774407965240221585465)
          ·
            refine ⟨133512580805973930166189099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178016774407965240221585465 133512580805973930166189099)
            ·
              refine ⟨200268871208960895249283649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133512580805973930166189099 200268871208960895249283649)
              ·
                refine ⟨150201653406720671436962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200268871208960895249283649 150201653406720671436962737)
                ·
                  refine ⟨112651240055040503577722053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150201653406720671436962737 112651240055040503577722053)
                  ·
                    refine ⟨21122107510320094420822885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112651240055040503577722053 21122107510320094420822885)
                    ·
                      refine ⟨3960395158185017703904291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21122107510320094420822885 3960395158185017703904291)
                      ·
                        rfl

theorem cell23_7712842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_7712842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712842 prefixEnd_7712842 := by exact prefixLift 7712842
  have htrace : WordTrace (prefixWord ++ tailWord_7712842) baseStart_7712842 baseEnd_7712842 := by
    simpa [prefixWord, tailWord_7712842, baseEnd_7712842] using wordTrace_append hprefix tailTrace_7712842
  have hstable : (prefixWord ++ tailWord_7712842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712842).length < 2 ^ (prefixWord ++ tailWord_7712842).sum := by decide
  have hdescent : baseEnd_7712842 < baseStart_7712842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712846 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_7712846 : Nat := 118140960795 + 7712846 * 2 ^ 59
def prefixEnd_7712846 : Nat := 4983230072969 + 3 ^ 40 * 7712846 * 2
def baseEnd_7712846 : Nat := 3960397212107635688254273

theorem tailTrace_7712846 : CollatzResearch.WordTrace tailWord_7712846 prefixEnd_7712846 3960397212107635688254273 := by
  unfold tailWord_7712846
  simp only [CollatzResearch.WordTrace]
  refine ⟨35163825526960458258792799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187540402810455777380228261 35163825526960458258792799)
  ·
    refine ⟨52745738290440687388189199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35163825526960458258792799 52745738290440687388189199)
    ·
      refine ⟨79118607435661031082283799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52745738290440687388189199 79118607435661031082283799)
      ·
        refine ⟨118677911153491546623425699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79118607435661031082283799 118677911153491546623425699)
        ·
          refine ⟨178016866730237319935138549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118677911153491546623425699 178016866730237319935138549)
          ·
            refine ⟨16689081255959748743919239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178016866730237319935138549 16689081255959748743919239)
            ·
              refine ⟨25033621883939623115878859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16689081255959748743919239 25033621883939623115878859)
              ·
                refine ⟨37550432825909434673818289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25033621883939623115878859 37550432825909434673818289)
                ·
                  refine ⟨28162824619432076005363717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37550432825909434673818289 28162824619432076005363717)
                  ·
                    refine ⟨5280529616143514251005697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28162824619432076005363717 5280529616143514251005697)
                    ·
                      refine ⟨3960397212107635688254273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280529616143514251005697 3960397212107635688254273)
                      ·
                        rfl

theorem cell23_7712846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_7712846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712846 prefixEnd_7712846 := by exact prefixLift 7712846
  have htrace : WordTrace (prefixWord ++ tailWord_7712846) baseStart_7712846 baseEnd_7712846 := by
    simpa [prefixWord, tailWord_7712846, baseEnd_7712846] using wordTrace_append hprefix tailTrace_7712846
  have hstable : (prefixWord ++ tailWord_7712846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712846).length < 2 ^ (prefixWord ++ tailWord_7712846).sum := by decide
  have hdescent : baseEnd_7712846 < baseStart_7712846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712852 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 10]
def baseStart_7712852 : Nat := 118140960795 + 7712852 * 2 ^ 59
def prefixEnd_7712852 : Nat := 4983230072969 + 3 ^ 40 * 7712852 * 2
def baseEnd_7712852 : Nat := 440044476999062518308805

theorem tailTrace_7712852 : CollatzResearch.WordTrace tailWord_7712852 prefixEnd_7712852 440044476999062518308805 := by
  unfold tailWord_7712852
  simp only [CollatzResearch.WordTrace]
  refine ⟨140655411526830964547530405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187540548702441286063373873 140655411526830964547530405)
  ·
    refine ⟨26372889661280805852661951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140655411526830964547530405 26372889661280805852661951)
    ·
      refine ⟨39559334491921208778992927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26372889661280805852661951 39559334491921208778992927)
      ·
        refine ⟨59339001737881813168489391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39559334491921208778992927 59339001737881813168489391)
        ·
          refine ⟨89008502606822719752734087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59339001737881813168489391 89008502606822719752734087)
          ·
            refine ⟨133512753910234079629101131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89008502606822719752734087 133512753910234079629101131)
            ·
              refine ⟨200269130865351119443651697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133512753910234079629101131 200269130865351119443651697)
              ·
                refine ⟨150201848149013339582738773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200269130865351119443651697 150201848149013339582738773)
                ·
                  refine ⟨440044476999062518308805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150201848149013339582738773 440044476999062518308805)
                  ·
                    rfl

theorem cell23_7712852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_7712852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712852 prefixEnd_7712852 := by exact prefixLift 7712852
  have htrace : WordTrace (prefixWord ++ tailWord_7712852) baseStart_7712852 baseEnd_7712852 := by
    simpa [prefixWord, tailWord_7712852, baseEnd_7712852] using wordTrace_append hprefix tailTrace_7712852
  have hstable : (prefixWord ++ tailWord_7712852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712852).length < 2 ^ (prefixWord ++ tailWord_7712852).sum := by decide
  have hdescent : baseEnd_7712852 < baseStart_7712852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712886 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_7712886 : Nat := 118140960795 + 7712886 * 2 ^ 59
def prefixEnd_7712886 : Nat := 4983230072969 + 3 ^ 40 * 7712886 * 2
def baseEnd_7712886 : Nat := 440046416814868392417121

theorem tailTrace_7712886 : CollatzResearch.WordTrace tailWord_7712886 prefixEnd_7712886 440046416814868392417121 := by
  unfold tailWord_7712886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17582003945971172056362407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187541375423692501934532341 17582003945971172056362407)
  ·
    refine ⟨26373005918956758084543611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17582003945971172056362407 26373005918956758084543611)
    ·
      refine ⟨39559508878435137126815417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26373005918956758084543611 39559508878435137126815417)
      ·
        refine ⟨29669631658826352845111563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39559508878435137126815417 29669631658826352845111563)
        ·
          refine ⟨44504447488239529267667345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29669631658826352845111563 44504447488239529267667345)
          ·
            refine ⟨33378335616179646950750509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44504447488239529267667345 33378335616179646950750509)
            ·
              refine ⟨12516875856067367606531441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33378335616179646950750509 12516875856067367606531441)
              ·
                refine ⟨9387656892050525704898581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516875856067367606531441 9387656892050525704898581)
                ·
                  refine ⟨440046416814868392417121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9387656892050525704898581 440046416814868392417121)
                  ·
                    rfl

theorem cell23_7712886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_7712886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712886 prefixEnd_7712886 := by exact prefixLift 7712886
  have htrace : WordTrace (prefixWord ++ tailWord_7712886) baseStart_7712886 baseEnd_7712886 := by
    simpa [prefixWord, tailWord_7712886, baseEnd_7712886] using wordTrace_append hprefix tailTrace_7712886
  have hstable : (prefixWord ++ tailWord_7712886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712886).length < 2 ^ (prefixWord ++ tailWord_7712886).sum := by decide
  have hdescent : baseEnd_7712886 < baseStart_7712886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712906 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_7712906 : Nat := 118140960795 + 7712906 * 2 ^ 59
def prefixEnd_7712906 : Nat := 4983230072969 + 3 ^ 40 * 7712906 * 2
def baseEnd_7712906 : Nat := 3960428020946905453503997

theorem tailTrace_7712906 : CollatzResearch.WordTrace tailWord_7712906 prefixEnd_7712906 3960428020946905453503997 := by
  unfold tailWord_7712906
  simp only [CollatzResearch.WordTrace]
  refine ⟨70328198148866574079381643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187541861730310864211684381 70328198148866574079381643)
  ·
    refine ⟨105492297223299861119072465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70328198148866574079381643 105492297223299861119072465)
    ·
      refine ⟨79119222917474895839304349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105492297223299861119072465 79119222917474895839304349)
      ·
        refine ⟨29669708594053085939739131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79119222917474895839304349 29669708594053085939739131)
        ·
          refine ⟨44504562891079628909608697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29669708594053085939739131 44504562891079628909608697)
          ·
            refine ⟨33378422168309721682206523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44504562891079628909608697 33378422168309721682206523)
            ·
              refine ⟨50067633252464582523309785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33378422168309721682206523 50067633252464582523309785)
              ·
                refine ⟨37550724939348436892482339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50067633252464582523309785 37550724939348436892482339)
                ·
                  refine ⟨56326087409022655338723509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37550724939348436892482339 56326087409022655338723509)
                  ·
                    refine ⟨5280570694595873938005329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56326087409022655338723509 5280570694595873938005329)
                    ·
                      refine ⟨3960428020946905453503997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280570694595873938005329 3960428020946905453503997)
                      ·
                        rfl

theorem cell23_7712906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_7712906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712906 prefixEnd_7712906 := by exact prefixLift 7712906
  have htrace : WordTrace (prefixWord ++ tailWord_7712906) baseStart_7712906 baseEnd_7712906 := by
    simpa [prefixWord, tailWord_7712906, baseEnd_7712906] using wordTrace_append hprefix tailTrace_7712906
  have hstable : (prefixWord ++ tailWord_7712906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712906).length < 2 ^ (prefixWord ++ tailWord_7712906).sum := by decide
  have hdescent : baseEnd_7712906 < baseStart_7712906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712946 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_7712946 : Nat := 118140960795 + 7712946 * 2 ^ 59
def prefixEnd_7712946 : Nat := 4983230072969 + 3 ^ 40 * 7712946 * 2
def baseEnd_7712946 : Nat := 1320149520057695099001271

theorem tailTrace_7712946 : CollatzResearch.WordTrace tailWord_7712946 prefixEnd_7712946 1320149520057695099001271 := by
  unfold tailWord_7712946
  simp only [CollatzResearch.WordTrace]
  refine ⟨70328562878830345787245673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187542834343547588765988461 70328562878830345787245673)
  ·
    refine ⟨52746422159122759340434255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70328562878830345787245673 52746422159122759340434255)
    ·
      refine ⟨79119633238684139010651383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52746422159122759340434255 79119633238684139010651383)
      ·
        refine ⟨118679449858026208515977075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79119633238684139010651383 118679449858026208515977075)
        ·
          refine ⟨178019174787039312773965613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118679449858026208515977075 178019174787039312773965613)
          ·
            refine ⟨66757190545139742290237105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178019174787039312773965613 66757190545139742290237105)
            ·
              refine ⟨50067892908854806717677829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66757190545139742290237105 50067892908854806717677829)
              ·
                refine ⟨9387729920410276259564593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50067892908854806717677829 9387729920410276259564593)
                ·
                  refine ⟨7040797440307707194673445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387729920410276259564593 7040797440307707194673445)
                  ·
                    refine ⟨1320149520057695099001271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040797440307707194673445 1320149520057695099001271)
                    ·
                      rfl

theorem cell23_7712946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_7712946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712946 prefixEnd_7712946 := by exact prefixLift 7712946
  have htrace : WordTrace (prefixWord ++ tailWord_7712946) baseStart_7712946 baseEnd_7712946 := by
    simpa [prefixWord, tailWord_7712946, baseEnd_7712946] using wordTrace_append hprefix tailTrace_7712946
  have hstable : (prefixWord ++ tailWord_7712946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712946).length < 2 ^ (prefixWord ++ tailWord_7712946).sum := by decide
  have hdescent : baseEnd_7712946 < baseStart_7712946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7712986 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_7712986 : Nat := 118140960795 + 7712986 * 2 ^ 59
def prefixEnd_7712986 : Nat := 4983230072969 + 3 ^ 40 * 7712986 * 2
def baseEnd_7712986 : Nat := 3960469099399265140503629

theorem tailTrace_7712986 : CollatzResearch.WordTrace tailWord_7712986 prefixEnd_7712986 3960469099399265140503629 := by
  unfold tailWord_7712986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70328927608794117495109703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187543806956784313320292541 70328927608794117495109703)
  ·
    refine ⟨105493391413191176242664555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70328927608794117495109703 105493391413191176242664555)
    ·
      refine ⟨158240087119786764363996833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105493391413191176242664555 158240087119786764363996833)
      ·
        refine ⟨118680065339840073272997625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158240087119786764363996833 118680065339840073272997625)
        ·
          refine ⟨89010049004880054954748219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118680065339840073272997625 89010049004880054954748219)
          ·
            refine ⟨133515073507320082432122329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89010049004880054954748219 133515073507320082432122329)
            ·
              refine ⟨100136305130490061824091747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133515073507320082432122329 100136305130490061824091747)
              ·
                refine ⟨150204457695735092736137621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100136305130490061824091747 150204457695735092736137621)
                ·
                  refine ⟨7040833954487582472006451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150204457695735092736137621 7040833954487582472006451)
                  ·
                    refine ⟨10561250931731373708009677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040833954487582472006451 10561250931731373708009677)
                    ·
                      refine ⟨3960469099399265140503629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561250931731373708009677 3960469099399265140503629)
                      ·
                        rfl

theorem cell23_7712986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_7712986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7712986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7712986 prefixEnd_7712986 := by exact prefixLift 7712986
  have htrace : WordTrace (prefixWord ++ tailWord_7712986) baseStart_7712986 baseEnd_7712986 := by
    simpa [prefixWord, tailWord_7712986, baseEnd_7712986] using wordTrace_append hprefix tailTrace_7712986
  have hstable : (prefixWord ++ tailWord_7712986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7712986).length < 2 ^ (prefixWord ++ tailWord_7712986).sum := by decide
  have hdescent : baseEnd_7712986 < baseStart_7712986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7712986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713003 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 3]
def baseStart_7713003 : Nat := 118140960795 + 7713003 * 2 ^ 59
def prefixEnd_7713003 : Nat := 4983230072969 + 3 ^ 40 * 7713003 * 2
def baseEnd_7713003 : Nat := 3960477828570391573991051

theorem tailTrace_7713003 : CollatzResearch.WordTrace tailWord_7713003 prefixEnd_7713003 3960477828570391573991051 := by
  unfold tailWord_7713003
  simp only [CollatzResearch.WordTrace]
  refine ⟨281316330476114881883807663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187544220317409921255871775 281316330476114881883807663)
  ·
    refine ⟨421974495714172322825711495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281316330476114881883807663 421974495714172322825711495)
    ·
      refine ⟨632961743571258484238567243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421974495714172322825711495 632961743571258484238567243)
      ·
        refine ⟨949442615356887726357850865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632961743571258484238567243 949442615356887726357850865)
        ·
          refine ⟨712081961517665794768388149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949442615356887726357850865 712081961517665794768388149)
          ·
            refine ⟨66757683892281168259536389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 712081961517665794768388149 66757683892281168259536389)
            ·
              refine ⟨12517065729802719048663073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66757683892281168259536389 12517065729802719048663073)
              ·
                refine ⟨9387799297352039286497305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517065729802719048663073 9387799297352039286497305)
                ·
                  refine ⟨7040849473014029464872979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387799297352039286497305 7040849473014029464872979)
                  ·
                    refine ⟨10561274209521044197309469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040849473014029464872979 10561274209521044197309469)
                    ·
                      refine ⟨3960477828570391573991051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561274209521044197309469 3960477828570391573991051)
                      ·
                        rfl

theorem cell23_7713003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 3].length) (baseStart_7713003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713003 prefixEnd_7713003 := by exact prefixLift 7713003
  have htrace : WordTrace (prefixWord ++ tailWord_7713003) baseStart_7713003 baseEnd_7713003 := by
    simpa [prefixWord, tailWord_7713003, baseEnd_7713003] using wordTrace_append hprefix tailTrace_7713003
  have hstable : (prefixWord ++ tailWord_7713003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713003).length < 2 ^ (prefixWord ++ tailWord_7713003).sum := by decide
  have hdescent : baseEnd_7713003 < baseStart_7713003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713009 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_7713009 : Nat := 118140960795 + 7713009 * 2 ^ 59
def prefixEnd_7713009 : Nat := 4983230072969 + 3 ^ 40 * 7713009 * 2
def baseEnd_7713009 : Nat := 3960480909454318550516023

theorem tailTrace_7713009 : CollatzResearch.WordTrace tailWord_7713009 prefixEnd_7713009 3960480909454318550516023 := by
  unfold tailWord_7713009
  simp only [CollatzResearch.WordTrace]
  refine ⟨281316549314093144908526081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187544366209395429939017387 281316549314093144908526081)
  ·
    refine ⟨210987411985569858681394561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281316549314093144908526081 210987411985569858681394561)
    ·
      refine ⟨158240558989177394011045921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210987411985569858681394561 158240558989177394011045921)
      ·
        refine ⟨118680419241883045508284441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158240558989177394011045921 118680419241883045508284441)
        ·
          refine ⟨89010314431412284131213331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118680419241883045508284441 89010314431412284131213331)
          ·
            refine ⟨133515471647118426196819997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89010314431412284131213331 133515471647118426196819997)
            ·
              refine ⟨50068301867669409823807499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133515471647118426196819997 50068301867669409823807499)
              ·
                refine ⟨75102452801504114735711249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50068301867669409823807499 75102452801504114735711249)
                ·
                  refine ⟨56326839601128086051783437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75102452801504114735711249 56326839601128086051783437)
                  ·
                    refine ⟨21122564850423032269418789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56326839601128086051783437 21122564850423032269418789)
                    ·
                      refine ⟨3960480909454318550516023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21122564850423032269418789 3960480909454318550516023)
                      ·
                        rfl

theorem cell23_7713009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_7713009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713009 prefixEnd_7713009 := by exact prefixLift 7713009
  have htrace : WordTrace (prefixWord ++ tailWord_7713009) baseStart_7713009 baseEnd_7713009 := by
    simpa [prefixWord, tailWord_7713009, baseEnd_7713009] using wordTrace_append hprefix tailTrace_7713009
  have hstable : (prefixWord ++ tailWord_7713009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713009).length < 2 ^ (prefixWord ++ tailWord_7713009).sum := by decide
  have hdescent : baseEnd_7713009 < baseStart_7713009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713029 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_7713029 : Nat := 118140960795 + 7713029 * 2 ^ 59
def prefixEnd_7713029 : Nat := 4983230072969 + 3 ^ 40 * 7713029 * 2
def baseEnd_7713029 : Nat := 3960491179067408472265931

theorem tailTrace_7713029 : CollatzResearch.WordTrace tailWord_7713029 prefixEnd_7713029 3960491179067408472265931 := by
  unfold tailWord_7713029
  simp only [CollatzResearch.WordTrace]
  refine ⟨281317278774020688324254141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187544852516013792216169427 281317278774020688324254141)
  ·
    refine ⟨105493979540257758121595303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281317278774020688324254141 105493979540257758121595303)
    ·
      refine ⟨158240969310386637182392955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105493979540257758121595303 158240969310386637182392955)
      ·
        refine ⟨237361453965579955773589433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158240969310386637182392955 237361453965579955773589433)
        ·
          refine ⟨178021090474184966830192075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237361453965579955773589433 178021090474184966830192075)
          ·
            refine ⟨267031635711277450245288113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178021090474184966830192075 267031635711277450245288113)
            ·
              refine ⟨200273726783458087683966085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267031635711277450245288113 200273726783458087683966085)
              ·
                refine ⟨37551323771898391440743641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200273726783458087683966085 37551323771898391440743641)
                ·
                  refine ⟨28163492828923793580557731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37551323771898391440743641 28163492828923793580557731)
                  ·
                    refine ⟨42245239243385690370836597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28163492828923793580557731 42245239243385690370836597)
                    ·
                      refine ⟨3960491179067408472265931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42245239243385690370836597 3960491179067408472265931)
                      ·
                        rfl

theorem cell23_7713029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_7713029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713029 prefixEnd_7713029 := by exact prefixLift 7713029
  have htrace : WordTrace (prefixWord ++ tailWord_7713029) baseStart_7713029 baseEnd_7713029 := by
    simpa [prefixWord, tailWord_7713029, baseEnd_7713029] using wordTrace_append hprefix tailTrace_7713029
  have hstable : (prefixWord ++ tailWord_7713029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713029).length < 2 ^ (prefixWord ++ tailWord_7713029).sum := by decide
  have hdescent : baseEnd_7713029 < baseStart_7713029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713047 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_7713047 : Nat := 118140960795 + 7713047 * 2 ^ 59
def prefixEnd_7713047 : Nat := 4983230072969 + 3 ^ 40 * 7713047 * 2
def baseEnd_7713047 : Nat := 3960500421719189401840849

theorem tailTrace_7713047 : CollatzResearch.WordTrace tailWord_7713047 prefixEnd_7713047 3960500421719189401840849 := by
  unfold tailWord_7713047
  simp only [CollatzResearch.WordTrace]
  refine ⟨281317935287955477398409395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187545290191970318265606263 281317935287955477398409395)
  ·
    refine ⟨421976902931933216097614093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281317935287955477398409395 421976902931933216097614093)
    ·
      refine ⟨158241338599474956036605285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421976902931933216097614093 158241338599474956036605285)
      ·
        refine ⟨29670250987401554256863491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158241338599474956036605285 29670250987401554256863491)
        ·
          refine ⟨44505376481102331385295237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29670250987401554256863491 44505376481102331385295237)
          ·
            refine ⟨8344758090206687134742857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44505376481102331385295237 8344758090206687134742857)
            ·
              refine ⟨6258568567655015351057143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344758090206687134742857 6258568567655015351057143)
              ·
                refine ⟨9387852851482523026585715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258568567655015351057143 9387852851482523026585715)
                ·
                  refine ⟨14081779277223784539878573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387852851482523026585715 14081779277223784539878573)
                  ·
                    refine ⟨5280667228958919202454465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14081779277223784539878573 5280667228958919202454465)
                    ·
                      refine ⟨3960500421719189401840849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280667228958919202454465 3960500421719189401840849)
                      ·
                        rfl

theorem cell23_7713047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_7713047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713047 prefixEnd_7713047 := by exact prefixLift 7713047
  have htrace : WordTrace (prefixWord ++ tailWord_7713047) baseStart_7713047 baseEnd_7713047 := by
    simpa [prefixWord, tailWord_7713047, baseEnd_7713047] using wordTrace_append hprefix tailTrace_7713047
  have hstable : (prefixWord ++ tailWord_7713047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713047).length < 2 ^ (prefixWord ++ tailWord_7713047).sum := by decide
  have hdescent : baseEnd_7713047 < baseStart_7713047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713054 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7713054 : Nat := 118140960795 + 7713054 * 2 ^ 59
def prefixEnd_7713054 : Nat := 4983230072969 + 3 ^ 40 * 7713054 * 2
def baseEnd_7713054 : Nat := 3960504016083770874453317

theorem tailTrace_7713054 : CollatzResearch.WordTrace tailWord_7713054 prefixEnd_7713054 3960504016083770874453317 := by
  unfold tailWord_7713054
  simp only [CollatzResearch.WordTrace]
  refine ⟨35164773824866264699239277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187545460399286745062609477 35164773824866264699239277)
  ·
    refine ⟨13186790184324849262214729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35164773824866264699239277 13186790184324849262214729)
    ·
      refine ⟨9890092638243636946661047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13186790184324849262214729 9890092638243636946661047)
      ·
        refine ⟨14835138957365455419991571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890092638243636946661047 14835138957365455419991571)
        ·
          refine ⟨22252708436048183129987357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14835138957365455419991571 22252708436048183129987357)
          ·
            refine ⟨8344765663518068673745259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22252708436048183129987357 8344765663518068673745259)
            ·
              refine ⟨12517148495277103010617889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344765663518068673745259 12517148495277103010617889)
              ·
                refine ⟨9387861371457827257963417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517148495277103010617889 9387861371457827257963417)
                ·
                  refine ⟨7040896028593370443472563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387861371457827257963417 7040896028593370443472563)
                  ·
                    refine ⟨10561344042890055665208845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040896028593370443472563 10561344042890055665208845)
                    ·
                      refine ⟨3960504016083770874453317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561344042890055665208845 3960504016083770874453317)
                      ·
                        rfl

theorem cell23_7713054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7713054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713054 prefixEnd_7713054 := by exact prefixLift 7713054
  have htrace : WordTrace (prefixWord ++ tailWord_7713054) baseStart_7713054 baseEnd_7713054 := by
    simpa [prefixWord, tailWord_7713054, baseEnd_7713054] using wordTrace_append hprefix tailTrace_7713054
  have hstable : (prefixWord ++ tailWord_7713054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713054).length < 2 ^ (prefixWord ++ tailWord_7713054).sum := by decide
  have hdescent : baseEnd_7713054 < baseStart_7713054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713056 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7713056 : Nat := 118140960795 + 7713056 * 2 ^ 59
def prefixEnd_7713056 : Nat := 4983230072969 + 3 ^ 40 * 7713056 * 2
def baseEnd_7713056 : Nat := 3960505043045079866628307

theorem tailTrace_7713056 : CollatzResearch.WordTrace tailWord_7713056 prefixEnd_7713056 3960505043045079866628307 := by
  unfold tailWord_7713056
  simp only [CollatzResearch.WordTrace]
  refine ⟨140659131772461435967743511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187545509029948581290324681 140659131772461435967743511)
  ·
    refine ⟨210988697658692153951615267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140659131772461435967743511 210988697658692153951615267)
    ·
      refine ⟨316483046488038230927422901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210988697658692153951615267 316483046488038230927422901)
      ·
        refine ⟨29670285608253584149445897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316483046488038230927422901 29670285608253584149445897)
        ·
          refine ⟨22252714206190188112084423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29670285608253584149445897 22252714206190188112084423)
          ·
            refine ⟨33379071309285282168126635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22252714206190188112084423 33379071309285282168126635)
            ·
              refine ⟨50068606963927923252189953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33379071309285282168126635 50068606963927923252189953)
              ·
                refine ⟨37551455222945942439142465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50068606963927923252189953 37551455222945942439142465)
                ·
                  refine ⟨28163591417209456829356849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37551455222945942439142465 28163591417209456829356849)
                  ·
                    refine ⟨21122693562907092622017637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28163591417209456829356849 21122693562907092622017637)
                    ·
                      refine ⟨3960505043045079866628307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21122693562907092622017637 3960505043045079866628307)
                      ·
                        rfl

theorem cell23_7713056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7713056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713056 prefixEnd_7713056 := by exact prefixLift 7713056
  have htrace : WordTrace (prefixWord ++ tailWord_7713056) baseStart_7713056 baseEnd_7713056 := by
    simpa [prefixWord, tailWord_7713056, baseEnd_7713056] using wordTrace_append hprefix tailTrace_7713056
  have hstable : (prefixWord ++ tailWord_7713056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713056).length < 2 ^ (prefixWord ++ tailWord_7713056).sum := by decide
  have hdescent : baseEnd_7713056 < baseStart_7713056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713060 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_7713060 : Nat := 118140960795 + 7713060 * 2 ^ 59
def prefixEnd_7713060 : Nat := 4983230072969 + 3 ^ 40 * 7713060 * 2
def baseEnd_7713060 : Nat := 3960507096967697850978289

theorem tailTrace_7713060 : CollatzResearch.WordTrace tailWord_7713060 prefixEnd_7713060 3960507096967697850978289 := by
  unfold tailWord_7713060
  simp only [CollatzResearch.WordTrace]
  refine ⟨140659204718454190309316317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187545606291272253745755089 140659204718454190309316317)
  ·
    refine ⟨52747201769420321365993619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140659204718454190309316317 52747201769420321365993619)
    ·
      refine ⟨79120802654130482048990429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52747201769420321365993619 79120802654130482048990429)
      ·
        refine ⟨29670300995298930768371411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79120802654130482048990429 29670300995298930768371411)
        ·
          refine ⟨44505451492948396152557117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29670300995298930768371411 44505451492948396152557117)
          ·
            refine ⟨16689544309855648557208919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44505451492948396152557117 16689544309855648557208919)
            ·
              refine ⟨25034316464783472835813379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16689544309855648557208919 25034316464783472835813379)
              ·
                refine ⟨37551474697175209253720069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25034316464783472835813379 37551474697175209253720069)
                ·
                  refine ⟨7040901505720351735072513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37551474697175209253720069 7040901505720351735072513)
                  ·
                    refine ⟨5280676129290263801304385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040901505720351735072513 5280676129290263801304385)
                    ·
                      refine ⟨3960507096967697850978289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280676129290263801304385 3960507096967697850978289)
                      ·
                        rfl

theorem cell23_7713060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_7713060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713060 prefixEnd_7713060 := by exact prefixLift 7713060
  have htrace : WordTrace (prefixWord ++ tailWord_7713060) baseStart_7713060 baseEnd_7713060 := by
    simpa [prefixWord, tailWord_7713060, baseEnd_7713060] using wordTrace_append hprefix tailTrace_7713060
  have hstable : (prefixWord ++ tailWord_7713060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713060).length < 2 ^ (prefixWord ++ tailWord_7713060).sum := by decide
  have hdescent : baseEnd_7713060 < baseStart_7713060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713077 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_7713077 : Nat := 118140960795 + 7713077 * 2 ^ 59
def prefixEnd_7713077 : Nat := 4983230072969 + 3 ^ 40 * 7713077 * 2
def baseEnd_7713077 : Nat := 3960515826138824284465711

theorem tailTrace_7713077 : CollatzResearch.WordTrace tailWord_7713077 prefixEnd_7713077 3960515826138824284465711 := by
  unfold tailWord_7713077
  simp only [CollatzResearch.WordTrace]
  refine ⟨281319029477846792522001485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187546019651897861681334323 281319029477846792522001485)
  ·
    refine ⟨105494636054192547195750557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281319029477846792522001485 105494636054192547195750557)
    ·
      refine ⟨39560488520322205198406459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105494636054192547195750557 39560488520322205198406459)
      ·
        refine ⟨59340732780483307797609689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39560488520322205198406459 59340732780483307797609689)
        ·
          refine ⟨44505549585362480848207267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59340732780483307797609689 44505549585362480848207267)
          ·
            refine ⟨66758324378043721272310901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44505549585362480848207267 66758324378043721272310901)
            ·
              refine ⟨6258592910441598869279147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66758324378043721272310901 6258592910441598869279147)
              ·
                refine ⟨9387889365662398303918721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258592910441598869279147 9387889365662398303918721)
                ·
                  refine ⟨7040917024246798727939041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387889365662398303918721 7040917024246798727939041)
                  ·
                    refine ⟨5280687768185099045954281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040917024246798727939041 5280687768185099045954281)
                    ·
                      refine ⟨3960515826138824284465711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280687768185099045954281 3960515826138824284465711)
                      ·
                        rfl

theorem cell23_7713077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_7713077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713077 prefixEnd_7713077 := by exact prefixLift 7713077
  have htrace : WordTrace (prefixWord ++ tailWord_7713077) baseStart_7713077 baseEnd_7713077 := by
    simpa [prefixWord, tailWord_7713077, baseEnd_7713077] using wordTrace_append hprefix tailTrace_7713077
  have hstable : (prefixWord ++ tailWord_7713077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713077).length < 2 ^ (prefixWord ++ tailWord_7713077).sum := by decide
  have hdescent : baseEnd_7713077 < baseStart_7713077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713133 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_7713133 : Nat := 118140960795 + 7713133 * 2 ^ 59
def prefixEnd_7713133 : Nat := 4983230072969 + 3 ^ 40 * 7713133 * 2
def baseEnd_7713133 : Nat := 3960544581055476065365453

theorem tailTrace_7713133 : CollatzResearch.WordTrace tailWord_7713133 prefixEnd_7713133 3960544581055476065365453 := by
  unfold tailWord_7713133
  simp only [CollatzResearch.WordTrace]
  refine ⟨281321071965643914086040053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187547381310429276057360035 281321071965643914086040053)
  ·
    refine ⟨26373850496779116945566255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281321071965643914086040053 26373850496779116945566255)
    ·
      refine ⟨39560775745168675418349383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26373850496779116945566255 39560775745168675418349383)
      ·
        refine ⟨59341163617753013127524075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39560775745168675418349383 59341163617753013127524075)
        ·
          refine ⟨89011745426629519691286113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59341163617753013127524075 89011745426629519691286113)
          ·
            refine ⟨66758809069972139768464585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89011745426629519691286113 66758809069972139768464585)
            ·
              refine ⟨50069106802479104826348439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66758809069972139768464585 50069106802479104826348439)
              ·
                refine ⟨75103660203718657239522659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50069106802479104826348439 75103660203718657239522659)
                ·
                  refine ⟨112655490305577985859283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75103660203718657239522659 112655490305577985859283989)
                  ·
                    refine ⟨5280726108073968087153937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112655490305577985859283989 5280726108073968087153937)
                    ·
                      refine ⟨3960544581055476065365453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280726108073968087153937 3960544581055476065365453)
                      ·
                        rfl

theorem cell23_7713133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_7713133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713133 prefixEnd_7713133 := by exact prefixLift 7713133
  have htrace : WordTrace (prefixWord ++ tailWord_7713133) baseStart_7713133 baseEnd_7713133 := by
    simpa [prefixWord, tailWord_7713133, baseEnd_7713133] using wordTrace_append hprefix tailTrace_7713133
  have hstable : (prefixWord ++ tailWord_7713133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713133).length < 2 ^ (prefixWord ++ tailWord_7713133).sum := by decide
  have hdescent : baseEnd_7713133 < baseStart_7713133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713160 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 1, 4]
def baseStart_7713160 : Nat := 118140960795 + 7713160 * 2 ^ 59
def prefixEnd_7713160 : Nat := 4983230072969 + 3 ^ 40 * 7713160 * 2
def baseEnd_7713160 : Nat := 1320186148344382486575943

theorem tailTrace_7713160 : CollatzResearch.WordTrace tailWord_7713160 prefixEnd_7713160 1320186148344382486575943 := by
  unfold tailWord_7713160
  simp only [CollatzResearch.WordTrace]
  refine ⟨140661028368273048848636467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187548037824364065131515289 140661028368273048848636467)
  ·
    refine ⟨210991542552409573272954701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140661028368273048848636467 210991542552409573272954701)
    ·
      refine ⟨79121828457153589977358013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210991542552409573272954701 79121828457153589977358013)
      ·
        refine ⟨29670685671432596241509255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79121828457153589977358013 29670685671432596241509255)
        ·
          refine ⟨44506028507148894362263883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29670685671432596241509255 44506028507148894362263883)
          ·
            refine ⟨66759042760723341543395825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44506028507148894362263883 66759042760723341543395825)
            ·
              refine ⟨50069282070542506157546869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66759042760723341543395825 50069282070542506157546869)
              ·
                refine ⟨4693995194113359952270019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50069282070542506157546869 4693995194113359952270019)
                ·
                  refine ⟨7040992791170039928405029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693995194113359952270019 7040992791170039928405029)
                  ·
                    refine ⟨1320186148344382486575943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7040992791170039928405029 1320186148344382486575943)
                    ·
                      rfl

theorem cell23_7713160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_7713160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713160 prefixEnd_7713160 := by exact prefixLift 7713160
  have htrace : WordTrace (prefixWord ++ tailWord_7713160) baseStart_7713160 baseEnd_7713160 := by
    simpa [prefixWord, tailWord_7713160, baseEnd_7713160] using wordTrace_append hprefix tailTrace_7713160
  have hstable : (prefixWord ++ tailWord_7713160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713160).length < 2 ^ (prefixWord ++ tailWord_7713160).sum := by decide
  have hdescent : baseEnd_7713160 < baseStart_7713160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 4, 3, 2]
def baseStart_7713193 : Nat := 118140960795 + 7713193 * 2 ^ 59
def prefixEnd_7713193 : Nat := 4983230072969 + 3 ^ 40 * 7713193 * 2
def baseEnd_7713193 : Nat := 3960575389894745830615177

theorem tailTrace_7713193 : CollatzResearch.WordTrace tailWord_7713193 prefixEnd_7713193 3960575389894745830615177 := by
  unfold tailWord_7713193
  simp only [CollatzResearch.WordTrace]
  refine ⟨281323260345426544333224233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187548840230284362888816155 281323260345426544333224233)
  ·
    refine ⟨210992445259069908249918175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281323260345426544333224233 210992445259069908249918175)
    ·
      refine ⟨316488667888604862374877263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210992445259069908249918175 316488667888604862374877263)
      ·
        refine ⟨474733001832907293562315895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316488667888604862374877263 474733001832907293562315895)
        ·
          refine ⟨712099502749360940343473843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474733001832907293562315895 712099502749360940343473843)
          ·
            refine ⟨1068149254124041410515210765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712099502749360940343473843 1068149254124041410515210765)
            ·
              refine ⟨400555970296515528943204037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068149254124041410515210765 400555970296515528943204037)
              ·
                refine ⟨75104244430596661676850757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400555970296515528943204037 75104244430596661676850757)
                ·
                  refine ⟨14082045830736874064409517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75104244430596661676850757 14082045830736874064409517)
                  ·
                    refine ⟨5280767186526327774153569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14082045830736874064409517 5280767186526327774153569)
                    ·
                      refine ⟨3960575389894745830615177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280767186526327774153569 3960575389894745830615177)
                      ·
                        rfl

theorem cell23_7713193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 3, 2].length) (baseStart_7713193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713193 prefixEnd_7713193 := by exact prefixLift 7713193
  have htrace : WordTrace (prefixWord ++ tailWord_7713193) baseStart_7713193 baseEnd_7713193 := by
    simpa [prefixWord, tailWord_7713193, baseEnd_7713193] using wordTrace_append hprefix tailTrace_7713193
  have hstable : (prefixWord ++ tailWord_7713193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713193).length < 2 ^ (prefixWord ++ tailWord_7713193).sum := by decide
  have hdescent : baseEnd_7713193 < baseStart_7713193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713194 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7713194 : Nat := 118140960795 + 7713194 * 2 ^ 59
def prefixEnd_7713194 : Nat := 4983230072969 + 3 ^ 40 * 7713194 * 2
def baseEnd_7713194 : Nat := 1320191967791800108900891

theorem tailTrace_7713194 : CollatzResearch.WordTrace tailWord_7713194 prefixEnd_7713194 1320191967791800108900891 := by
  unfold tailWord_7713194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70330824204605730376002659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187548864545615281002673757 70330824204605730376002659)
  ·
    refine ⟨105496236306908595564003989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70330824204605730376002659 105496236306908595564003989)
    ·
      refine ⟨4945136076886340417062687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105496236306908595564003989 4945136076886340417062687)
      ·
        refine ⟨7417704115329510625594031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4945136076886340417062687 7417704115329510625594031)
        ·
          refine ⟨11126556172994265938391047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417704115329510625594031 11126556172994265938391047)
          ·
            refine ⟨16689834259491398907586571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126556172994265938391047 16689834259491398907586571)
            ·
              refine ⟨25034751389237098361379857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16689834259491398907586571 25034751389237098361379857)
              ·
                refine ⟨18776063541927823771034893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25034751389237098361379857 18776063541927823771034893)
                ·
                  refine ⟨7041023828222933914138085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18776063541927823771034893 7041023828222933914138085)
                  ·
                    refine ⟨1320191967791800108900891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7041023828222933914138085 1320191967791800108900891)
                    ·
                      rfl

theorem cell23_7713194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7713194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713194 prefixEnd_7713194 := by exact prefixLift 7713194
  have htrace : WordTrace (prefixWord ++ tailWord_7713194) baseStart_7713194 baseEnd_7713194 := by
    simpa [prefixWord, tailWord_7713194, baseEnd_7713194] using wordTrace_append hprefix tailTrace_7713194
  have hstable : (prefixWord ++ tailWord_7713194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713194).length < 2 ^ (prefixWord ++ tailWord_7713194).sum := by decide
  have hdescent : baseEnd_7713194 < baseStart_7713194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713234 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7713234 : Nat := 118140960795 + 7713234 * 2 ^ 59
def prefixEnd_7713234 : Nat := 4983230072969 + 3 ^ 40 * 7713234 * 2
def baseEnd_7713234 : Nat := 3960596442601580170202489

theorem tailTrace_7713234 : CollatzResearch.WordTrace tailWord_7713234 prefixEnd_7713234 3960596442601580170202489 := by
  unfold tailWord_7713234
  simp only [CollatzResearch.WordTrace]
  refine ⟨70331188934569502083866689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187549837158852005556977837 70331188934569502083866689)
  ·
    refine ⟨52748391700927126562900017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70331188934569502083866689 52748391700927126562900017)
    ·
      refine ⟨39561293775695344922175013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52748391700927126562900017 39561293775695344922175013)
      ·
        refine ⟨7417742582942877172907815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39561293775695344922175013 7417742582942877172907815)
        ·
          refine ⟨11126613874414315759361723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417742582942877172907815 11126613874414315759361723)
          ·
            refine ⟨16689920811621473639042585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126613874414315759361723 16689920811621473639042585)
            ·
              refine ⟨12517440608716105229281939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16689920811621473639042585 12517440608716105229281939)
              ·
                refine ⟨18776160913074157843922909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12517440608716105229281939 18776160913074157843922909)
                ·
                  refine ⟨7041060342402809191471091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18776160913074157843922909 7041060342402809191471091)
                  ·
                    refine ⟨10561590513604213787206637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041060342402809191471091 10561590513604213787206637)
                    ·
                      refine ⟨3960596442601580170202489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561590513604213787206637 3960596442601580170202489)
                      ·
                        rfl

theorem cell23_7713234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7713234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713234 prefixEnd_7713234 := by exact prefixLift 7713234
  have htrace : WordTrace (prefixWord ++ tailWord_7713234) baseStart_7713234 baseEnd_7713234 := by
    simpa [prefixWord, tailWord_7713234, baseEnd_7713234] using wordTrace_append hprefix tailTrace_7713234
  have hstable : (prefixWord ++ tailWord_7713234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713234).length < 2 ^ (prefixWord ++ tailWord_7713234).sum := by decide
  have hdescent : baseEnd_7713234 < baseStart_7713234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713260 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_7713260 : Nat := 118140960795 + 7713260 * 2 ^ 59
def prefixEnd_7713260 : Nat := 4983230072969 + 3 ^ 40 * 7713260 * 2
def baseEnd_7713260 : Nat := 3960609793098597068477369

theorem tailTrace_7713260 : CollatzResearch.WordTrace tailWord_7713260 prefixEnd_7713260 3960609793098597068477369 := by
  unfold tailWord_7713260
  simp only [CollatzResearch.WordTrace]
  refine ⟨140662852018091907387956617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187550469357455876517275489 140662852018091907387956617)
  ·
    refine ⟨105497139013568930540967463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140662852018091907387956617 105497139013568930540967463)
    ·
      refine ⟨158245708520353395811451195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105497139013568930540967463 158245708520353395811451195)
      ·
        refine ⟨237368562780530093717176793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158245708520353395811451195 237368562780530093717176793)
        ·
          refine ⟨178026422085397570287882595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237368562780530093717176793 178026422085397570287882595)
          ·
            refine ⟨267039633128096355431823893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178026422085397570287882595 267039633128096355431823893)
            ·
              refine ⟨12517482802879516660866745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267039633128096355431823893 12517482802879516660866745)
              ·
                refine ⟨9388112102159637495650059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517482802879516660866745 9388112102159637495650059)
                ·
                  refine ⟨14082168153239456243475089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388112102159637495650059 14082168153239456243475089)
                  ·
                    refine ⟨10561626114929592182606317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14082168153239456243475089 10561626114929592182606317)
                    ·
                      refine ⟨3960609793098597068477369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561626114929592182606317 3960609793098597068477369)
                      ·
                        rfl

theorem cell23_7713260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_7713260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713260 prefixEnd_7713260 := by exact prefixLift 7713260
  have htrace : WordTrace (prefixWord ++ tailWord_7713260) baseStart_7713260 baseEnd_7713260 := by
    simpa [prefixWord, tailWord_7713260, baseEnd_7713260] using wordTrace_append hprefix tailTrace_7713260
  have hstable : (prefixWord ++ tailWord_7713260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713260).length < 2 ^ (prefixWord ++ tailWord_7713260).sum := by decide
  have hdescent : baseEnd_7713260 < baseStart_7713260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713273 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_7713273 : Nat := 118140960795 + 7713273 * 2 ^ 59
def prefixEnd_7713273 : Nat := 4983230072969 + 3 ^ 40 * 7713273 * 2
def baseEnd_7713273 : Nat := 3960616468347105517614809

theorem tailTrace_7713273 : CollatzResearch.WordTrace tailWord_7713273 prefixEnd_7713273 3960616468347105517614809 := by
  unfold tailWord_7713273
  simp only [CollatzResearch.WordTrace]
  refine ⟨281326178185136717996136473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187550785456757811997424315 281326178185136717996136473)
  ·
    refine ⟨210994633638852538497102355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281326178185136717996136473 210994633638852538497102355)
    ·
      refine ⟨316491950458278807745653533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210994633638852538497102355 316491950458278807745653533)
      ·
        refine ⟨118684481421854552904620075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316491950458278807745653533 118684481421854552904620075)
        ·
          refine ⟨178026722132781829356930113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118684481421854552904620075 178026722132781829356930113)
          ·
            refine ⟨133520041599586372017697585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178026722132781829356930113 133520041599586372017697585)
            ·
              refine ⟨100140031199689779013273189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133520041599586372017697585 100140031199689779013273189)
              ·
                refine ⟨18776255849941833564988723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100140031199689779013273189 18776255849941833564988723)
                ·
                  refine ⟨28164383774912750347483085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18776255849941833564988723 28164383774912750347483085)
                  ·
                    refine ⟨10561643915592281380306157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28164383774912750347483085 10561643915592281380306157)
                    ·
                      refine ⟨3960616468347105517614809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561643915592281380306157 3960616468347105517614809)
                      ·
                        rfl

theorem cell23_7713273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_7713273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713273 prefixEnd_7713273 := by exact prefixLift 7713273
  have htrace : WordTrace (prefixWord ++ tailWord_7713273) baseStart_7713273 baseEnd_7713273 := by
    simpa [prefixWord, tailWord_7713273, baseEnd_7713273] using wordTrace_append hprefix tailTrace_7713273
  have hstable : (prefixWord ++ tailWord_7713273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713273).length < 2 ^ (prefixWord ++ tailWord_7713273).sum := by decide
  have hdescent : baseEnd_7713273 < baseStart_7713273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713276 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_7713276 : Nat := 118140960795 + 7713276 * 2 ^ 59
def prefixEnd_7713276 : Nat := 4983230072969 + 3 ^ 40 * 7713276 * 2
def baseEnd_7713276 : Nat := 1320206002929689668625765

theorem tailTrace_7713276 : CollatzResearch.WordTrace tailWord_7713276 prefixEnd_7713276 1320206002929689668625765 := by
  unfold tailWord_7713276
  simp only [CollatzResearch.WordTrace]
  refine ⟨140663143802062924754247841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187550858402750566338997121 140663143802062924754247841)
  ·
    refine ⟨105497357851547193565685881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140663143802062924754247841 105497357851547193565685881)
    ·
      refine ⟨79123018388660395174264411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105497357851547193565685881 79123018388660395174264411)
      ·
        refine ⟨118684527582990592761396617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79123018388660395174264411 118684527582990592761396617)
        ·
          refine ⟨89013395687242944571047463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118684527582990592761396617 89013395687242944571047463)
          ·
            refine ⟨133520093530864416856571195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89013395687242944571047463 133520093530864416856571195)
            ·
              refine ⟨200280140296296625284856793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133520093530864416856571195 200280140296296625284856793)
              ·
                refine ⟨150210105222222468963642595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200280140296296625284856793 150210105222222468963642595)
                ·
                  refine ⟨225315157833333703445463893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150210105222222468963642595 225315157833333703445463893)
                  ·
                    refine ⟨1320206002929689668625765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 225315157833333703445463893 1320206002929689668625765)
                    ·
                      rfl

theorem cell23_7713276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_7713276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713276 prefixEnd_7713276 := by exact prefixLift 7713276
  have htrace : WordTrace (prefixWord ++ tailWord_7713276) baseStart_7713276 baseEnd_7713276 := by
    simpa [prefixWord, tailWord_7713276, baseEnd_7713276] using wordTrace_append hprefix tailTrace_7713276
  have hstable : (prefixWord ++ tailWord_7713276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713276).length < 2 ^ (prefixWord ++ tailWord_7713276).sum := by decide
  have hdescent : baseEnd_7713276 < baseStart_7713276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713290 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_7713290 : Nat := 118140960795 + 7713290 * 2 ^ 59
def prefixEnd_7713290 : Nat := 4983230072969 + 3 ^ 40 * 7713290 * 2
def baseEnd_7713290 : Nat := 3960625197518231951102231

theorem tailTrace_7713290 : CollatzResearch.WordTrace tailWord_7713290 prefixEnd_7713290 3960625197518231951102231 := by
  unfold tailWord_7713290
  simp only [CollatzResearch.WordTrace]
  refine ⟨70331699556518782474876331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187551198817383419933003549 70331699556518782474876331)
  ·
    refine ⟨105497549334778173712314497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70331699556518782474876331 105497549334778173712314497)
    ·
      refine ⟨79123162001083630284235873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105497549334778173712314497 79123162001083630284235873)
      ·
        refine ⟨59342371500812722713176905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79123162001083630284235873 59342371500812722713176905)
        ·
          refine ⟨44506778625609542034882679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59342371500812722713176905 44506778625609542034882679)
          ·
            refine ⟨66760167938414313052324019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44506778625609542034882679 66760167938414313052324019)
            ·
              refine ⟨100140251907621469578486029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66760167938414313052324019 100140251907621469578486029)
              ·
                refine ⟨37552594465358051091932261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100140251907621469578486029 37552594465358051091932261)
                ·
                  refine ⟨7041111462254634579737299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37552594465358051091932261 7041111462254634579737299)
                  ·
                    refine ⟨10561667193381951869605949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041111462254634579737299 10561667193381951869605949)
                    ·
                      refine ⟨3960625197518231951102231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561667193381951869605949 3960625197518231951102231)
                      ·
                        rfl

theorem cell23_7713290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_7713290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713290 prefixEnd_7713290 := by exact prefixLift 7713290
  have htrace : WordTrace (prefixWord ++ tailWord_7713290) baseStart_7713290 baseEnd_7713290 := by
    simpa [prefixWord, tailWord_7713290, baseEnd_7713290] using wordTrace_append hprefix tailTrace_7713290
  have hstable : (prefixWord ++ tailWord_7713290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713290).length < 2 ^ (prefixWord ++ tailWord_7713290).sum := by decide
  have hdescent : baseEnd_7713290 < baseStart_7713290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713291 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 1, 2, 2]
def baseStart_7713291 : Nat := 118140960795 + 7713291 * 2 ^ 59
def prefixEnd_7713291 : Nat := 4983230072969 + 3 ^ 40 * 7713291 * 2
def baseEnd_7713291 : Nat := 3960625710998886447189727

theorem tailTrace_7713291 : CollatzResearch.WordTrace tailWord_7713291 prefixEnd_7713291 3960625710998886447189727 := by
  unfold tailWord_7713291
  simp only [CollatzResearch.WordTrace]
  refine ⟨281326834699071507070291727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187551223132714338046861151 281326834699071507070291727)
  ·
    refine ⟨421990252048607260605437591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281326834699071507070291727 421990252048607260605437591)
    ·
      refine ⟨632985378072910890908156387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421990252048607260605437591 632985378072910890908156387)
      ·
        refine ⟨949478067109366336362234581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632985378072910890908156387 949478067109366336362234581)
        ·
          refine ⟨22253392197875773508489873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 949478067109366336362234581 22253392197875773508489873)
          ·
            refine ⟨16690044148406830131367405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22253392197875773508489873 16690044148406830131367405)
            ·
              refine ⟨6258766555652561299262777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16690044148406830131367405 6258766555652561299262777)
              ·
                refine ⟨4694074916739420974447083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258766555652561299262777 4694074916739420974447083)
                ·
                  refine ⟨7041112375109131461670625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694074916739420974447083 7041112375109131461670625)
                  ·
                    refine ⟨5280834281331848596252969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041112375109131461670625 5280834281331848596252969)
                    ·
                      refine ⟨3960625710998886447189727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280834281331848596252969 3960625710998886447189727)
                      ·
                        rfl

theorem cell23_7713291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 2, 2].length) (baseStart_7713291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713291 prefixEnd_7713291 := by exact prefixLift 7713291
  have htrace : WordTrace (prefixWord ++ tailWord_7713291) baseStart_7713291 baseEnd_7713291 := by
    simpa [prefixWord, tailWord_7713291, baseEnd_7713291] using wordTrace_append hprefix tailTrace_7713291
  have hstable : (prefixWord ++ tailWord_7713291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713291).length < 2 ^ (prefixWord ++ tailWord_7713291).sum := by decide
  have hdescent : baseEnd_7713291 < baseStart_7713291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713317 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_7713317 : Nat := 118140960795 + 7713317 * 2 ^ 59
def prefixEnd_7713317 : Nat := 4983230072969 + 3 ^ 40 * 7713317 * 2
def baseEnd_7713317 : Nat := 3960639061495903345464607

theorem tailTrace_7713317 : CollatzResearch.WordTrace tailWord_7713317 prefixEnd_7713317 3960639061495903345464607 := by
  unfold tailWord_7713317
  simp only [CollatzResearch.WordTrace]
  refine ⟨281327782996977313510738205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187551855331318209007158803 281327782996977313510738205)
  ·
    refine ⟨105497918623866492566526827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281327782996977313510738205 105497918623866492566526827)
    ·
      refine ⟨158246877935799738849790241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105497918623866492566526827 158246877935799738849790241)
      ·
        refine ⟨118685158451849804137342681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158246877935799738849790241 118685158451849804137342681)
        ·
          refine ⟨89013868838887353103007011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118685158451849804137342681 89013868838887353103007011)
          ·
            refine ⟨133520803258331029654510517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89013868838887353103007011 133520803258331029654510517)
            ·
              refine ⟨12517575305468534030110361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133520803258331029654510517 12517575305468534030110361)
              ·
                refine ⟨9388181479101400522582771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517575305468534030110361 9388181479101400522582771)
                ·
                  refine ⟨14082272218652100783874157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388181479101400522582771 14082272218652100783874157)
                  ·
                    refine ⟨5280852081994537793952809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14082272218652100783874157 5280852081994537793952809)
                    ·
                      refine ⟨3960639061495903345464607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280852081994537793952809 3960639061495903345464607)
                      ·
                        rfl

theorem cell23_7713317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_7713317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713317 prefixEnd_7713317 := by exact prefixLift 7713317
  have htrace : WordTrace (prefixWord ++ tailWord_7713317) baseStart_7713317 baseEnd_7713317 := by
    simpa [prefixWord, tailWord_7713317, baseEnd_7713317] using wordTrace_append hprefix tailTrace_7713317
  have hstable : (prefixWord ++ tailWord_7713317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713317).length < 2 ^ (prefixWord ++ tailWord_7713317).sum := by decide
  have hdescent : baseEnd_7713317 < baseStart_7713317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713330 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_7713330 : Nat := 118140960795 + 7713330 * 2 ^ 59
def prefixEnd_7713330 : Nat := 4983230072969 + 3 ^ 40 * 7713330 * 2
def baseEnd_7713330 : Nat := 3960645736744411794602047

theorem tailTrace_7713330 : CollatzResearch.WordTrace tailWord_7713330 prefixEnd_7713330 3960645736744411794602047 := by
  unfold tailWord_7713330
  simp only [CollatzResearch.WordTrace]
  refine ⟨70332064286482554182740361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187552171430620144487307629 70332064286482554182740361)
  ·
    refine ⟨52749048214861915637055271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70332064286482554182740361 52749048214861915637055271)
    ·
      refine ⟨79123572322292873455582907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52749048214861915637055271 79123572322292873455582907)
      ·
        refine ⟨118685358483439310183374361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79123572322292873455582907 118685358483439310183374361)
        ·
          refine ⟨89014018862579482637530771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118685358483439310183374361 89014018862579482637530771)
          ·
            refine ⟨133521028293869223956296157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89014018862579482637530771 133521028293869223956296157)
            ·
              refine ⟨50070385610200958983611059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133521028293869223956296157 50070385610200958983611059)
              ·
                refine ⟨75105578415301438475416589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50070385610200958983611059 75105578415301438475416589)
                ·
                  refine ⟨28164591905738039428281221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75105578415301438475416589 28164591905738039428281221)
                  ·
                    refine ⟨5280860982325882392802729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28164591905738039428281221 5280860982325882392802729)
                    ·
                      refine ⟨3960645736744411794602047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280860982325882392802729 3960645736744411794602047)
                      ·
                        rfl

theorem cell23_7713330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_7713330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713330 prefixEnd_7713330 := by exact prefixLift 7713330
  have htrace : WordTrace (prefixWord ++ tailWord_7713330) baseStart_7713330 baseEnd_7713330 := by
    simpa [prefixWord, tailWord_7713330, baseEnd_7713330] using wordTrace_append hprefix tailTrace_7713330
  have hstable : (prefixWord ++ tailWord_7713330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713330).length < 2 ^ (prefixWord ++ tailWord_7713330).sum := by decide
  have hdescent : baseEnd_7713330 < baseStart_7713330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713333 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7713333 : Nat := 118140960795 + 7713333 * 2 ^ 59
def prefixEnd_7713333 : Nat := 4983230072969 + 3 ^ 40 * 7713333 * 2
def baseEnd_7713333 : Nat := 3960647277186375282864533

theorem tailTrace_7713333 : CollatzResearch.WordTrace tailWord_7713333 prefixEnd_7713333 3960647277186375282864533 := by
  unfold tailWord_7713333
  simp only [CollatzResearch.WordTrace]
  refine ⟨281328366564919348243320653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187552244376612898828880435 281328366564919348243320653)
  ·
    refine ⟨105498137461844755591245245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281328366564919348243320653 105498137461844755591245245)
    ·
      refine ⟨39561801548191783346716967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105498137461844755591245245 39561801548191783346716967)
      ·
        refine ⟨59342702322287675020075451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39561801548191783346716967 59342702322287675020075451)
        ·
          refine ⟨89014053483431512530113177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59342702322287675020075451 89014053483431512530113177)
          ·
            refine ⟨66760540112573634397584883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89014053483431512530113177 66760540112573634397584883)
            ·
              refine ⟨100140810168860451596377325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66760540112573634397584883 100140810168860451596377325)
              ·
                refine ⟨37552803813322669348641497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100140810168860451596377325 37552803813322669348641497)
                ·
                  refine ⟨28164602859992002011481123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37552803813322669348641497 28164602859992002011481123)
                  ·
                    refine ⟨42246904289988003017221685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28164602859992002011481123 42246904289988003017221685)
                    ·
                      refine ⟨3960647277186375282864533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42246904289988003017221685 3960647277186375282864533)
                      ·
                        rfl

theorem cell23_7713333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7713333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713333 prefixEnd_7713333 := by exact prefixLift 7713333
  have htrace : WordTrace (prefixWord ++ tailWord_7713333) baseStart_7713333 baseEnd_7713333 := by
    simpa [prefixWord, tailWord_7713333, baseEnd_7713333] using wordTrace_append hprefix tailTrace_7713333
  have hstable : (prefixWord ++ tailWord_7713333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713333).length < 2 ^ (prefixWord ++ tailWord_7713333).sum := by decide
  have hdescent : baseEnd_7713333 < baseStart_7713333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713342 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7713342 : Nat := 118140960795 + 7713342 * 2 ^ 59
def prefixEnd_7713342 : Nat := 4983230072969 + 3 ^ 40 * 7713342 * 2
def baseEnd_7713342 : Nat := 3960651898512265747651993

theorem tailTrace_7713342 : CollatzResearch.WordTrace tailWord_7713342 prefixEnd_7713342 3960651898512265747651993 := by
  unfold tailWord_7713342
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166086852735842847549785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187552463214591161853598853 35166086852735842847549785)
  ·
    refine ⟨26374565139551882135662339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35166086852735842847549785 26374565139551882135662339)
    ·
      refine ⟨39561847709327823203493509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26374565139551882135662339 39561847709327823203493509)
      ·
        refine ⟨7417846445498966850655033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39561847709327823203493509 7417846445498966850655033)
        ·
          refine ⟨5563384834124225137991275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7417846445498966850655033 5563384834124225137991275)
          ·
            refine ⟨8345077251186337706986913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563384834124225137991275 8345077251186337706986913)
            ·
              refine ⟨6258807938389753280240185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8345077251186337706986913 6258807938389753280240185)
              ·
                refine ⟨4694105953792314960180139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258807938389753280240185 4694105953792314960180139)
                ·
                  refine ⟨7041158930688472440270209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694105953792314960180139 7041158930688472440270209)
                  ·
                    refine ⟨5280869198016354330202657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041158930688472440270209 5280869198016354330202657)
                    ·
                      refine ⟨3960651898512265747651993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280869198016354330202657 3960651898512265747651993)
                      ·
                        rfl

theorem cell23_7713342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7713342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713342 prefixEnd_7713342 := by exact prefixLift 7713342
  have htrace : WordTrace (prefixWord ++ tailWord_7713342) baseStart_7713342 baseEnd_7713342 := by
    simpa [prefixWord, tailWord_7713342, baseEnd_7713342] using wordTrace_append hprefix tailTrace_7713342
  have hstable : (prefixWord ++ tailWord_7713342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713342).length < 2 ^ (prefixWord ++ tailWord_7713342).sum := by decide
  have hdescent : baseEnd_7713342 < baseStart_7713342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713343 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_7713343 : Nat := 118140960795 + 7713343 * 2 ^ 59
def prefixEnd_7713343 : Nat := 4983230072969 + 3 ^ 40 * 7713343 * 2
def baseEnd_7713343 : Nat := 3960652411992920243739487

theorem tailTrace_7713343 : CollatzResearch.WordTrace tailWord_7713343 prefixEnd_7713343 3960652411992920243739487 := by
  unfold tailWord_7713343
  simp only [CollatzResearch.WordTrace]
  refine ⟨281328731294883119951184683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187552487529922079967456455 281328731294883119951184683)
  ·
    refine ⟨421993096942324679926777025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281328731294883119951184683 421993096942324679926777025)
    ·
      refine ⟨316494822706743509945082769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421993096942324679926777025 316494822706743509945082769)
      ·
        refine ⟨237371117030057632458812077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316494822706743509945082769 237371117030057632458812077)
        ·
          refine ⟨89014168886271612172054529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237371117030057632458812077 89014168886271612172054529)
          ·
            refine ⟨66760626664703709129040897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89014168886271612172054529 66760626664703709129040897)
            ·
              refine ⟨50070469998527781846780673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66760626664703709129040897 50070469998527781846780673)
              ·
                refine ⟨37552852498895836385085505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50070469998527781846780673 37552852498895836385085505)
                ·
                  refine ⟨28164639374171877288814129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37552852498895836385085505 28164639374171877288814129)
                  ·
                    refine ⟨21123479530628907966610597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28164639374171877288814129 21123479530628907966610597)
                    ·
                      refine ⟨3960652411992920243739487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21123479530628907966610597 3960652411992920243739487)
                      ·
                        rfl

theorem cell23_7713343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_7713343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713343 prefixEnd_7713343 := by exact prefixLift 7713343
  have htrace : WordTrace (prefixWord ++ tailWord_7713343) baseStart_7713343 baseEnd_7713343 := by
    simpa [prefixWord, tailWord_7713343, baseEnd_7713343] using wordTrace_append hprefix tailTrace_7713343
  have hstable : (prefixWord ++ tailWord_7713343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713343).length < 2 ^ (prefixWord ++ tailWord_7713343).sum := by decide
  have hdescent : baseEnd_7713343 < baseStart_7713343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713364 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_7713364 : Nat := 118140960795 + 7713364 * 2 ^ 59
def prefixEnd_7713364 : Nat := 4983230072969 + 3 ^ 40 * 7713364 * 2
def baseEnd_7713364 : Nat := 3960663195086664661576891

theorem tailTrace_7713364 : CollatzResearch.WordTrace tailWord_7713364 prefixEnd_7713364 3960663195086664661576891 := by
  unfold tailWord_7713364
  simp only [CollatzResearch.WordTrace]
  refine ⟨140664748613903520268849573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187552998151871360358466097 140664748613903520268849573)
  ·
    refine ⟨26374640365106910050409295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140664748613903520268849573 26374640365106910050409295)
    ·
      refine ⟨39561960547660365075613943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26374640365106910050409295 39561960547660365075613943)
      ·
        refine ⟨59342940821490547613420915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39561960547660365075613943 59342940821490547613420915)
        ·
          refine ⟨89014411232235821420131373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59342940821490547613420915 89014411232235821420131373)
          ·
            refine ⟨33380404212088433032549265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89014411232235821420131373 33380404212088433032549265)
            ·
              refine ⟨25035303159066324774411949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33380404212088433032549265 25035303159066324774411949)
              ·
                refine ⟨9388238684649871790404481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25035303159066324774411949 9388238684649871790404481)
                ·
                  refine ⟨7041179013487403842803361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9388238684649871790404481 7041179013487403842803361)
                  ·
                    refine ⟨5280884260115552882102521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041179013487403842803361 5280884260115552882102521)
                    ·
                      refine ⟨3960663195086664661576891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280884260115552882102521 3960663195086664661576891)
                      ·
                        rfl

theorem cell23_7713364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_7713364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713364 prefixEnd_7713364 := by exact prefixLift 7713364
  have htrace : WordTrace (prefixWord ++ tailWord_7713364) baseStart_7713364 baseEnd_7713364 := by
    simpa [prefixWord, tailWord_7713364, baseEnd_7713364] using wordTrace_append hprefix tailTrace_7713364
  have hstable : (prefixWord ++ tailWord_7713364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713364).length < 2 ^ (prefixWord ++ tailWord_7713364).sum := by decide
  have hdescent : baseEnd_7713364 < baseStart_7713364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713398 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7713398 : Nat := 118140960795 + 7713398 * 2 ^ 59
def prefixEnd_7713398 : Nat := 4983230072969 + 3 ^ 40 * 7713398 * 2
def baseEnd_7713398 : Nat := 3960680653428917528551735

theorem tailTrace_7713398 : CollatzResearch.WordTrace tailWord_7713398 prefixEnd_7713398 3960680653428917528551735 := by
  unfold tailWord_7713398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583171081855241521527303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187553824873122576229624565 17583171081855241521527303)
  ·
    refine ⟨26374756622782862282290955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17583171081855241521527303 26374756622782862282290955)
    ·
      refine ⟨39562134934174293423436433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26374756622782862282290955 39562134934174293423436433)
      ·
        refine ⟨29671601200630720067577325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39562134934174293423436433 29671601200630720067577325)
        ·
          refine ⟨11126850450236520025341497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29671601200630720067577325 11126850450236520025341497)
          ·
            refine ⟨8345137837677390019006123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11126850450236520025341497 8345137837677390019006123)
            ·
              refine ⟨12517706756516085028509185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8345137837677390019006123 12517706756516085028509185)
              ·
                refine ⟨9388280067387063771381889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517706756516085028509185 9388280067387063771381889)
                ·
                  refine ⟨7041210050540297828536417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9388280067387063771381889 7041210050540297828536417)
                  ·
                    refine ⟨5280907537905223371402313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041210050540297828536417 5280907537905223371402313)
                    ·
                      refine ⟨3960680653428917528551735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280907537905223371402313 3960680653428917528551735)
                      ·
                        rfl

theorem cell23_7713398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7713398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713398 prefixEnd_7713398 := by exact prefixLift 7713398
  have htrace : WordTrace (prefixWord ++ tailWord_7713398) baseStart_7713398 baseEnd_7713398 := by
    simpa [prefixWord, tailWord_7713398, baseEnd_7713398] using wordTrace_append hprefix tailTrace_7713398
  have hstable : (prefixWord ++ tailWord_7713398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713398).length < 2 ^ (prefixWord ++ tailWord_7713398).sum := by decide
  have hdescent : baseEnd_7713398 < baseStart_7713398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713420 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_7713420 : Nat := 118140960795 + 7713420 * 2 ^ 59
def prefixEnd_7713420 : Nat := 4983230072969 + 3 ^ 40 * 7713420 * 2
def baseEnd_7713420 : Nat := 3960691950003316442476633

theorem tailTrace_7713420 : CollatzResearch.WordTrace tailWord_7713420 prefixEnd_7713420 3960691950003316442476633 := by
  unfold tailWord_7713420
  simp only [CollatzResearch.WordTrace]
  refine ⟨140665769857802081050868857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187554359810402774734491809 140665769857802081050868857)
  ·
    refine ⟨105499327393351560788151643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140665769857802081050868857 105499327393351560788151643)
    ·
      refine ⟨158248991090027341182227465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105499327393351560788151643 158248991090027341182227465)
      ·
        refine ⟨118686743317520505886670599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158248991090027341182227465 118686743317520505886670599)
        ·
          refine ⟨178030114976280758830005899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118686743317520505886670599 178030114976280758830005899)
          ·
            refine ⟨267045172464421138245008849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178030114976280758830005899 267045172464421138245008849)
            ·
              refine ⟨200283879348315853683756637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267045172464421138245008849 200283879348315853683756637)
              ·
                refine ⟨75106454755618445131408739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200283879348315853683756637 75106454755618445131408739)
                ·
                  refine ⟨112659682133427667697113109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75106454755618445131408739 112659682133427667697113109)
                  ·
                    refine ⟨5280922600004421923302177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112659682133427667697113109 5280922600004421923302177)
                    ·
                      refine ⟨3960691950003316442476633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5280922600004421923302177 3960691950003316442476633)
                      ·
                        rfl

theorem cell23_7713420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_7713420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713420 prefixEnd_7713420 := by exact prefixLift 7713420
  have htrace : WordTrace (prefixWord ++ tailWord_7713420) baseStart_7713420 baseEnd_7713420 := by
    simpa [prefixWord, tailWord_7713420, baseEnd_7713420] using wordTrace_append hprefix tailTrace_7713420
  have hstable : (prefixWord ++ tailWord_7713420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713420).length < 2 ^ (prefixWord ++ tailWord_7713420).sum := by decide
  have hdescent : baseEnd_7713420 < baseStart_7713420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713433 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_7713433 : Nat := 118140960795 + 7713433 * 2 ^ 59
def prefixEnd_7713433 : Nat := 4983230072969 + 3 ^ 40 * 7713433 * 2
def baseEnd_7713433 : Nat := 3960698625251824891614073

theorem tailTrace_7713433 : CollatzResearch.WordTrace tailWord_7713433 prefixEnd_7713433 3960698625251824891614073 := by
  unfold tailWord_7713433
  simp only [CollatzResearch.WordTrace]
  refine ⟨281332013864557065321960953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187554675909704710214640635 281332013864557065321960953)
  ·
    refine ⟨210999010398417798991470715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281332013864557065321960953 210999010398417798991470715)
    ·
      refine ⟨316498515597626698487206073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210999010398417798991470715 316498515597626698487206073)
      ·
        refine ⟨237373886698220023865404555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316498515597626698487206073 237373886698220023865404555)
        ·
          refine ⟨356060830047330035798106833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237373886698220023865404555 356060830047330035798106833)
          ·
            refine ⟨267045622535497526848580125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356060830047330035798106833 267045622535497526848580125)
            ·
              refine ⟨100142108450811572568217547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267045622535497526848580125 100142108450811572568217547)
              ·
                refine ⟨150213162676217358852326321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100142108450811572568217547 150213162676217358852326321)
                ·
                  refine ⟨112659872007163019139244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150213162676217358852326321 112659872007163019139244741)
                  ·
                    refine ⟨21123726001343066088608389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112659872007163019139244741 21123726001343066088608389)
                    ·
                      refine ⟨3960698625251824891614073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21123726001343066088608389 3960698625251824891614073)
                      ·
                        rfl

theorem cell23_7713433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_7713433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713433 prefixEnd_7713433 := by exact prefixLift 7713433
  have htrace : WordTrace (prefixWord ++ tailWord_7713433) baseStart_7713433 baseEnd_7713433 := by
    simpa [prefixWord, tailWord_7713433, baseEnd_7713433] using wordTrace_append hprefix tailTrace_7713433
  have hstable : (prefixWord ++ tailWord_7713433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713433).length < 2 ^ (prefixWord ++ tailWord_7713433).sum := by decide
  have hdescent : baseEnd_7713433 < baseStart_7713433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713454 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7713454 : Nat := 118140960795 + 7713454 * 2 ^ 59
def prefixEnd_7713454 : Nat := 4983230072969 + 3 ^ 40 * 7713454 * 2
def baseEnd_7713454 : Nat := 3960709408345569309451477

theorem tailTrace_7713454 : CollatzResearch.WordTrace tailWord_7713454 prefixEnd_7713454 3960709408345569309451477 := by
  unfold tailWord_7713454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35166597474685123238559427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187555186531653990605650277 35166597474685123238559427)
  ·
    refine ⟨52749896212027684857839141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35166597474685123238559427 52749896212027684857839141)
    ·
      refine ⟨9890605539755190910844839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52749896212027684857839141 9890605539755190910844839)
      ·
        refine ⟨14835908309632786366267259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9890605539755190910844839 14835908309632786366267259)
        ·
          refine ⟨22253862464449179549400889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14835908309632786366267259 22253862464449179549400889)
          ·
            refine ⟨16690396848336884662050667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22253862464449179549400889 16690396848336884662050667)
            ·
              refine ⟨25035595272505326993076001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16690396848336884662050667 25035595272505326993076001)
              ·
                refine ⟨18776696454378995244807001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25035595272505326993076001 18776696454378995244807001)
                ·
                  refine ⟨14082522340784246433605251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18776696454378995244807001 14082522340784246433605251)
                  ·
                    refine ⟨21123783511176369650407877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14082522340784246433605251 21123783511176369650407877)
                    ·
                      refine ⟨3960709408345569309451477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21123783511176369650407877 3960709408345569309451477)
                      ·
                        rfl

theorem cell23_7713454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7713454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713454 prefixEnd_7713454 := by exact prefixLift 7713454
  have htrace : WordTrace (prefixWord ++ tailWord_7713454) baseStart_7713454 baseEnd_7713454 := by
    simpa [prefixWord, tailWord_7713454, baseEnd_7713454] using wordTrace_append hprefix tailTrace_7713454
  have hstable : (prefixWord ++ tailWord_7713454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713454).length < 2 ^ (prefixWord ++ tailWord_7713454).sum := by decide
  have hdescent : baseEnd_7713454 < baseStart_7713454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713504 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 1, 1, 3]
def baseStart_7713504 : Nat := 118140960795 + 7713504 * 2 ^ 59
def prefixEnd_7713504 : Nat := 4983230072969 + 3 ^ 40 * 7713504 * 2
def baseEnd_7713504 : Nat := 3960735082378294113826247

theorem tailTrace_7713504 : CollatzResearch.WordTrace tailWord_7713504 prefixEnd_7713504 3960735082378294113826247 := by
  unfold tailWord_7713504
  simp only [CollatzResearch.WordTrace]
  refine ⟨140667301723649922223897783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187556402298199896298530377 140667301723649922223897783)
  ·
    refine ⟨211000952585474883335846675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140667301723649922223897783 211000952585474883335846675)
    ·
      refine ⟨316501428878212325003770013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211000952585474883335846675 316501428878212325003770013)
      ·
        refine ⟨118688035829329621876413755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316501428878212325003770013 118688035829329621876413755)
        ·
          refine ⟨178032053743994432814620633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118688035829329621876413755 178032053743994432814620633)
          ·
            refine ⟨133524040307995824610965475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178032053743994432814620633 133524040307995824610965475)
            ·
              refine ⟨200286060461993736916448213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133524040307995824610965475 200286060461993736916448213)
              ·
                refine ⟨4694204542077978208979255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 200286060461993736916448213 4694204542077978208979255)
                ·
                  refine ⟨7041306813116967313468883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694204542077978208979255 7041306813116967313468883)
                  ·
                    refine ⟨10561960219675450970203325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041306813116967313468883 10561960219675450970203325)
                    ·
                      refine ⟨3960735082378294113826247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10561960219675450970203325 3960735082378294113826247)
                      ·
                        rfl

theorem cell23_7713504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_7713504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713504 prefixEnd_7713504 := by exact prefixLift 7713504
  have htrace : WordTrace (prefixWord ++ tailWord_7713504) baseStart_7713504 baseEnd_7713504 := by
    simpa [prefixWord, tailWord_7713504, baseEnd_7713504] using wordTrace_append hprefix tailTrace_7713504
  have hstable : (prefixWord ++ tailWord_7713504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713504).length < 2 ^ (prefixWord ++ tailWord_7713504).sum := by decide
  have hdescent : baseEnd_7713504 < baseStart_7713504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713530 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_7713530 : Nat := 118140960795 + 7713530 * 2 ^ 59
def prefixEnd_7713530 : Nat := 4983230072969 + 3 ^ 40 * 7713530 * 2
def baseEnd_7713530 : Nat := 3960748432875311012101127

theorem tailTrace_7713530 : CollatzResearch.WordTrace tailWord_7713530 prefixEnd_7713530 3960748432875311012101127 := by
  unfold tailWord_7713530
  simp only [CollatzResearch.WordTrace]
  refine ⟨70333887936301412722060511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187557034496803767258828029 70333887936301412722060511)
  ·
    refine ⟨105500831904452119083090767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70333887936301412722060511 105500831904452119083090767)
    ·
      refine ⟨158251247856678178624636151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105500831904452119083090767 158251247856678178624636151)
      ·
        refine ⟨237376871785017267936954227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158251247856678178624636151 237376871785017267936954227)
        ·
          refine ⟨356065307677525901905431341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237376871785017267936954227 356065307677525901905431341)
          ·
            refine ⟨133524490379072213214536753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356065307677525901905431341 133524490379072213214536753)
            ·
              refine ⟨100143367784304159910902565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133524490379072213214536753 100143367784304159910902565)
              ·
                refine ⟨18776881459557029983294231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100143367784304159910902565 18776881459557029983294231)
                ·
                  refine ⟨28165322189335544974941347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18776881459557029983294231 28165322189335544974941347)
                  ·
                    refine ⟨42247983284003317462412021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28165322189335544974941347 42247983284003317462412021)
                    ·
                      refine ⟨3960748432875311012101127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42247983284003317462412021 3960748432875311012101127)
                      ·
                        rfl

theorem cell23_7713530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_7713530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713530 prefixEnd_7713530 := by exact prefixLift 7713530
  have htrace : WordTrace (prefixWord ++ tailWord_7713530) baseStart_7713530 baseEnd_7713530 := by
    simpa [prefixWord, tailWord_7713530, baseEnd_7713530] using wordTrace_append hprefix tailTrace_7713530
  have hstable : (prefixWord ++ tailWord_7713530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713530).length < 2 ^ (prefixWord ++ tailWord_7713530).sum := by decide
  have hdescent : baseEnd_7713530 < baseStart_7713530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713544 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_7713544 : Nat := 118140960795 + 7713544 * 2 ^ 59
def prefixEnd_7713544 : Nat := 4983230072969 + 3 ^ 40 * 7713544 * 2
def baseEnd_7713544 : Nat := 3960755621604473957326063

theorem tailTrace_7713544 : CollatzResearch.WordTrace tailWord_7713544 prefixEnd_7713544 3960755621604473957326063 := by
  unfold tailWord_7713544
  simp only [CollatzResearch.WordTrace]
  refine ⟨140668031183577465639625843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187557374911436620852834457 140668031183577465639625843)
  ·
    refine ⟨211002046775366198459438765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140668031183577465639625843 211002046775366198459438765)
    ·
      refine ⟨79125767540762324422289537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211002046775366198459438765 79125767540762324422289537)
      ·
        refine ⟨59344325655571743316717153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79125767540762324422289537 59344325655571743316717153)
        ·
          refine ⟨44508244241678807487537865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59344325655571743316717153 44508244241678807487537865)
          ·
            refine ⟨33381183181259105615653399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44508244241678807487537865 33381183181259105615653399)
            ·
              refine ⟨50071774771888658423480099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33381183181259105615653399 50071774771888658423480099)
              ·
                refine ⟨75107662157832987635220149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50071774771888658423480099 75107662157832987635220149)
                ·
                  refine ⟨7041343327296842590801889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75107662157832987635220149 7041343327296842590801889)
                  ·
                    refine ⟨5281007495472631943101417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041343327296842590801889 5281007495472631943101417)
                    ·
                      refine ⟨3960755621604473957326063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5281007495472631943101417 3960755621604473957326063)
                      ·
                        rfl

theorem cell23_7713544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_7713544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713544 prefixEnd_7713544 := by exact prefixLift 7713544
  have htrace : WordTrace (prefixWord ++ tailWord_7713544) baseStart_7713544 baseEnd_7713544 := by
    simpa [prefixWord, tailWord_7713544, baseEnd_7713544] using wordTrace_append hprefix tailTrace_7713544
  have hstable : (prefixWord ++ tailWord_7713544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713544).length < 2 ^ (prefixWord ++ tailWord_7713544).sum := by decide
  have hdescent : baseEnd_7713544 < baseStart_7713544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713547 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 3]
def baseStart_7713547 : Nat := 118140960795 + 7713547 * 2 ^ 59
def prefixEnd_7713547 : Nat := 4983230072969 + 3 ^ 40 * 7713547 * 2
def baseEnd_7713547 : Nat := 3960757162046437445588549

theorem tailTrace_7713547 : CollatzResearch.WordTrace tailWord_7713547 prefixEnd_7713547 3960757162046437445588549 := by
  unfold tailWord_7713547
  simp only [CollatzResearch.WordTrace]
  refine ⟨281336171786144062791610895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187557447857429375194407263 281336171786144062791610895)
  ·
    refine ⟨422004257679216094187416343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281336171786144062791610895 422004257679216094187416343)
    ·
      refine ⟨633006386518824141281124515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422004257679216094187416343 633006386518824141281124515)
      ·
        refine ⟨949509579778236211921686773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633006386518824141281124515 949509579778236211921686773)
        ·
          refine ⟨89016523104209644867658135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 949509579778236211921686773 89016523104209644867658135)
          ·
            refine ⟨133524784656314467301487203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89016523104209644867658135 133524784656314467301487203)
            ·
              refine ⟨200287176984471700952230805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133524784656314467301487203 200287176984471700952230805)
              ·
                refine ⟨9388461421147110982135819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200287176984471700952230805 9388461421147110982135819)
                ·
                  refine ⟨14082692131720666473203729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388461421147110982135819 14082692131720666473203729)
                  ·
                    refine ⟨10562019098790499854902797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14082692131720666473203729 10562019098790499854902797)
                    ·
                      refine ⟨3960757162046437445588549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562019098790499854902797 3960757162046437445588549)
                      ·
                        rfl

theorem cell23_7713547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 3].length) (baseStart_7713547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713547 prefixEnd_7713547 := by exact prefixLift 7713547
  have htrace : WordTrace (prefixWord ++ tailWord_7713547) baseStart_7713547 baseEnd_7713547 := by
    simpa [prefixWord, tailWord_7713547, baseEnd_7713547] using wordTrace_append hprefix tailTrace_7713547
  have hstable : (prefixWord ++ tailWord_7713547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713547).length < 2 ^ (prefixWord ++ tailWord_7713547).sum := by decide
  have hdescent : baseEnd_7713547 < baseStart_7713547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713564 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7713564 : Nat := 118140960795 + 7713564 * 2 ^ 59
def prefixEnd_7713564 : Nat := 4983230072969 + 3 ^ 40 * 7713564 * 2
def baseEnd_7713564 : Nat := 3960765891217563879075971

theorem tailTrace_7713564 : CollatzResearch.WordTrace tailWord_7713564 prefixEnd_7713564 3960765891217563879075971 := by
  unfold tailWord_7713564
  simp only [CollatzResearch.WordTrace]
  refine ⟨140668395913541237347489873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187557861218054983129986497 140668395913541237347489873)
  ·
    refine ⟨105501296935155928010617405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140668395913541237347489873 105501296935155928010617405)
    ·
      refine ⟨39562986350683473003981527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105501296935155928010617405 39562986350683473003981527)
      ·
        refine ⟨59344479526025209505972291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39562986350683473003981527 59344479526025209505972291)
        ·
          refine ⟨89016719289037814258958437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59344479526025209505972291 89016719289037814258958437)
          ·
            refine ⟨16690634866694590173554707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89016719289037814258958437 16690634866694590173554707)
            ·
              refine ⟨25035952300041885260332061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16690634866694590173554707 25035952300041885260332061)
              ·
                refine ⟨9388482112515706972624523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25035952300041885260332061 9388482112515706972624523)
                ·
                  refine ⟨14082723168773560458936785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388482112515706972624523 14082723168773560458936785)
                  ·
                    refine ⟨10562042376580170344202589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14082723168773560458936785 10562042376580170344202589)
                    ·
                      refine ⟨3960765891217563879075971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562042376580170344202589 3960765891217563879075971)
                      ·
                        rfl

theorem cell23_7713564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7713564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713564 prefixEnd_7713564 := by exact prefixLift 7713564
  have htrace : WordTrace (prefixWord ++ tailWord_7713564) baseStart_7713564 baseEnd_7713564 := by
    simpa [prefixWord, tailWord_7713564, baseEnd_7713564] using wordTrace_append hprefix tailTrace_7713564
  have hstable : (prefixWord ++ tailWord_7713564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713564).length < 2 ^ (prefixWord ++ tailWord_7713564).sum := by decide
  have hdescent : baseEnd_7713564 < baseStart_7713564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713577 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 3]
def baseStart_7713577 : Nat := 118140960795 + 7713577 * 2 ^ 59
def prefixEnd_7713577 : Nat := 4983230072969 + 3 ^ 40 * 7713577 * 2
def baseEnd_7713577 : Nat := 3960772566466072328213411

theorem tailTrace_7713577 : CollatzResearch.WordTrace tailWord_7713577 prefixEnd_7713577 3960772566466072328213411 := by
  unfold tailWord_7713577
  simp only [CollatzResearch.WordTrace]
  refine ⟨281337265976035377915202985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187558177317356918610135323 281337265976035377915202985)
  ·
    refine ⟨211002949482026533436402239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281337265976035377915202985 211002949482026533436402239)
    ·
      refine ⟨316504424223039800154603359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211002949482026533436402239 316504424223039800154603359)
      ·
        refine ⟨474756636334559700231905039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316504424223039800154603359 474756636334559700231905039)
        ·
          refine ⟨712134954501839550347857559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474756636334559700231905039 712134954501839550347857559)
          ·
            refine ⟨1068202431752759325521786339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712134954501839550347857559 1068202431752759325521786339)
            ·
              refine ⟨1602303647629138988282679509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068202431752759325521786339 1602303647629138988282679509)
              ·
                refine ⟨37553991741307945037875301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1602303647629138988282679509 37553991741307945037875301)
                ·
                  refine ⟨7041373451495239694601619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37553991741307945037875301 7041373451495239694601619)
                  ·
                    refine ⟨10562060177242859541902429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041373451495239694601619 10562060177242859541902429)
                    ·
                      refine ⟨3960772566466072328213411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562060177242859541902429 3960772566466072328213411)
                      ·
                        rfl

theorem cell23_7713577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_7713577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713577 prefixEnd_7713577 := by exact prefixLift 7713577
  have htrace : WordTrace (prefixWord ++ tailWord_7713577) baseStart_7713577 baseEnd_7713577 := by
    simpa [prefixWord, tailWord_7713577, baseEnd_7713577] using wordTrace_append hprefix tailTrace_7713577
  have hstable : (prefixWord ++ tailWord_7713577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713577).length < 2 ^ (prefixWord ++ tailWord_7713577).sum := by decide
  have hdescent : baseEnd_7713577 < baseStart_7713577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713581 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7713581 : Nat := 118140960795 + 7713581 * 2 ^ 59
def prefixEnd_7713581 : Nat := 4983230072969 + 3 ^ 40 * 7713581 * 2
def baseEnd_7713581 : Nat := 3960774620388690312563393

theorem tailTrace_7713581 : CollatzResearch.WordTrace tailWord_7713581 prefixEnd_7713581 3960774620388690312563393 := by
  unfold tailWord_7713581
  simp only [CollatzResearch.WordTrace]
  refine ⟨281337411868020886598348597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187558274578680591065565731 281337411868020886598348597)
  ·
    refine ⟨26375382362626958118595181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281337411868020886598348597 26375382362626958118595181)
    ·
      refine ⟨9890768385985109294473193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26375382362626958118595181 9890768385985109294473193)
      ·
        refine ⟨7418076289488831970854895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9890768385985109294473193 7418076289488831970854895)
        ·
          refine ⟨11127114434233247956282343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418076289488831970854895 11127114434233247956282343)
          ·
            refine ⟨16690671651349871934423515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127114434233247956282343 16690671651349871934423515)
            ·
              refine ⟨25036007477024807901635273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16690671651349871934423515 25036007477024807901635273)
              ·
                refine ⟨18777005607768605926226455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25036007477024807901635273 18777005607768605926226455)
                ·
                  refine ⟨28165508411652908889339683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18777005607768605926226455 28165508411652908889339683)
                  ·
                    refine ⟨42248262617479363334009525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28165508411652908889339683 42248262617479363334009525)
                    ·
                      refine ⟨3960774620388690312563393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42248262617479363334009525 3960774620388690312563393)
                      ·
                        rfl

theorem cell23_7713581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7713581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713581 prefixEnd_7713581 := by exact prefixLift 7713581
  have htrace : WordTrace (prefixWord ++ tailWord_7713581) baseStart_7713581 baseEnd_7713581 := by
    simpa [prefixWord, tailWord_7713581, baseEnd_7713581] using wordTrace_append hprefix tailTrace_7713581
  have hstable : (prefixWord ++ tailWord_7713581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713581).length < 2 ^ (prefixWord ++ tailWord_7713581).sum := by decide
  have hdescent : baseEnd_7713581 < baseStart_7713581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713588 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_7713588 : Nat := 118140960795 + 7713588 * 2 ^ 59
def prefixEnd_7713588 : Nat := 4983230072969 + 3 ^ 40 * 7713588 * 2
def baseEnd_7713588 : Nat := 1320259404917757261725287

theorem tailTrace_7713588 : CollatzResearch.WordTrace tailWord_7713588 prefixEnd_7713588 1320259404917757261725287 := by
  unfold tailWord_7713588
  simp only [CollatzResearch.WordTrace]
  refine ⟨140668833589497763396926709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187558444785997017862568945 140668833589497763396926709)
  ·
    refine ⟨13187703149015415318461879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140668833589497763396926709 13187703149015415318461879)
    ·
      refine ⟨19781554723523122977692819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13187703149015415318461879 19781554723523122977692819)
      ·
        refine ⟨29672332085284684466539229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19781554723523122977692819 29672332085284684466539229)
        ·
          refine ⟨11127124531981756674952211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29672332085284684466539229 11127124531981756674952211)
          ·
            refine ⟨16690686797972635012428317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127124531981756674952211 16690686797972635012428317)
            ·
              refine ⟨6259007549239738129660619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16690686797972635012428317 6259007549239738129660619)
              ·
                refine ⟨9388511323859607194490929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259007549239738129660619 9388511323859607194490929)
                ·
                  refine ⟨7041383492894705395868197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9388511323859607194490929 7041383492894705395868197)
                  ·
                    refine ⟨1320259404917757261725287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7041383492894705395868197 1320259404917757261725287)
                    ·
                      rfl

theorem cell23_7713588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_7713588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713588 prefixEnd_7713588 := by exact prefixLift 7713588
  have htrace : WordTrace (prefixWord ++ tailWord_7713588) baseStart_7713588 baseEnd_7713588 := by
    simpa [prefixWord, tailWord_7713588, baseEnd_7713588] using wordTrace_append hprefix tailTrace_7713588
  have hstable : (prefixWord ++ tailWord_7713588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713588).length < 2 ^ (prefixWord ++ tailWord_7713588).sum := by decide
  have hdescent : baseEnd_7713588 < baseStart_7713588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713600 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_7713600 : Nat := 118140960795 + 7713600 * 2 ^ 59
def prefixEnd_7713600 : Nat := 4983230072969 + 3 ^ 40 * 7713600 * 2
def baseEnd_7713600 : Nat := 3960784376521125738225805

theorem tailTrace_7713600 : CollatzResearch.WordTrace tailWord_7713600 prefixEnd_7713600 3960784376521125738225805 := by
  unfold tailWord_7713600
  simp only [CollatzResearch.WordTrace]
  refine ⟨140669052427476026421645127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187558736569968035228860169 140669052427476026421645127)
  ·
    refine ⟨211003578641214039632467691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140669052427476026421645127 211003578641214039632467691)
    ·
      refine ⟨316505367961821059448701537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211003578641214039632467691 316505367961821059448701537)
      ·
        refine ⟨237379025971365794586526153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316505367961821059448701537 237379025971365794586526153)
        ·
          refine ⟨178034269478524345939894615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237379025971365794586526153 178034269478524345939894615)
          ·
            refine ⟨267051404217786518909841923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178034269478524345939894615 267051404217786518909841923)
            ·
              refine ⟨400577106326679778364762885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267051404217786518909841923 400577106326679778364762885)
              ·
                refine ⟨75108207436252458443393041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400577106326679778364762885 75108207436252458443393041)
                ·
                  refine ⟨56331155577189343832544781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75108207436252458443393041 56331155577189343832544781)
                  ·
                    refine ⟨21124183341446003937204293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56331155577189343832544781 21124183341446003937204293)
                    ·
                      refine ⟨3960784376521125738225805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21124183341446003937204293 3960784376521125738225805)
                      ·
                        rfl

theorem cell23_7713600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_7713600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713600 prefixEnd_7713600 := by exact prefixLift 7713600
  have htrace : WordTrace (prefixWord ++ tailWord_7713600) baseStart_7713600 baseEnd_7713600 := by
    simpa [prefixWord, tailWord_7713600, baseEnd_7713600] using wordTrace_append hprefix tailTrace_7713600
  have hstable : (prefixWord ++ tailWord_7713600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713600).length < 2 ^ (prefixWord ++ tailWord_7713600).sum := by decide
  have hdescent : baseEnd_7713600 < baseStart_7713600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713601 : List Nat := [1, 2, 5, 3, 1, 2, 2, 7]
def baseStart_7713601 : Nat := 118140960795 + 7713601 * 2 ^ 59
def prefixEnd_7713601 : Nat := 4983230072969 + 3 ^ 40 * 7713601 * 2
def baseEnd_7713601 : Nat := 146695736666732601270863

theorem tailTrace_7713601 : CollatzResearch.WordTrace tailWord_7713601 prefixEnd_7713601 146695736666732601270863 := by
  unfold tailWord_7713601
  simp only [CollatzResearch.WordTrace]
  refine ⟨281338141327948430014076657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187558760885298953342717771 281338141327948430014076657)
  ·
    refine ⟨211003605995961322510557493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281338141327948430014076657 211003605995961322510557493)
    ·
      refine ⟨19781588062121373985364765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211003605995961322510557493 19781588062121373985364765)
      ·
        refine ⟨7418095523295515244511787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19781588062121373985364765 7418095523295515244511787)
        ·
          refine ⟨11127143284943272866767681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418095523295515244511787 11127143284943272866767681)
          ·
            refine ⟨8345357463707454650075761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11127143284943272866767681 8345357463707454650075761)
            ·
              refine ⟨6259018097780590987556821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8345357463707454650075761 6259018097780590987556821)
              ·
                refine ⟨146695736666732601270863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6259018097780590987556821 146695736666732601270863)
                ·
                  rfl

theorem cell23_7713601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 7].length) (baseStart_7713601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713601 prefixEnd_7713601 := by exact prefixLift 7713601
  have htrace : WordTrace (prefixWord ++ tailWord_7713601) baseStart_7713601 baseEnd_7713601 := by
    simpa [prefixWord, tailWord_7713601, baseEnd_7713601] using wordTrace_append hprefix tailTrace_7713601
  have hstable : (prefixWord ++ tailWord_7713601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713601).length < 2 ^ (prefixWord ++ tailWord_7713601).sum := by decide
  have hdescent : baseEnd_7713601 < baseStart_7713601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713610 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_7713610 : Nat := 118140960795 + 7713610 * 2 ^ 59
def prefixEnd_7713610 : Nat := 4983230072969 + 3 ^ 40 * 7713610 * 2
def baseEnd_7713610 : Nat := 1320263170442556899700253

theorem tailTrace_7713610 : CollatzResearch.WordTrace tailWord_7713610 prefixEnd_7713610 1320263170442556899700253 := by
  unfold tailWord_7713610
  simp only [CollatzResearch.WordTrace]
  refine ⟨70334617396228956137788571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187558979723277216367436189 70334617396228956137788571)
  ·
    refine ⟨105501926094343434206682857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70334617396228956137788571 105501926094343434206682857)
    ·
      refine ⟨79126444570757575655012143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105501926094343434206682857 79126444570757575655012143)
      ·
        refine ⟨118689666856136363482518215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79126444570757575655012143 118689666856136363482518215)
        ·
          refine ⟨178034500284204545223777323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118689666856136363482518215 178034500284204545223777323)
          ·
            refine ⟨267051750426306817835665985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178034500284204545223777323 267051750426306817835665985)
            ·
              refine ⟨200288812819730113376749489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267051750426306817835665985 200288812819730113376749489)
              ·
                refine ⟨150216609614797585032562117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200288812819730113376749489 150216609614797585032562117)
                ·
                  refine ⟨28165614302774547193605397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150216609614797585032562117 28165614302774547193605397)
                  ·
                    refine ⟨1320263170442556899700253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28165614302774547193605397 1320263170442556899700253)
                    ·
                      rfl

theorem cell23_7713610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_7713610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713610 prefixEnd_7713610 := by exact prefixLift 7713610
  have htrace : WordTrace (prefixWord ++ tailWord_7713610) baseStart_7713610 baseEnd_7713610 := by
    simpa [prefixWord, tailWord_7713610, baseEnd_7713610] using wordTrace_append hprefix tailTrace_7713610
  have hstable : (prefixWord ++ tailWord_7713610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713610).length < 2 ^ (prefixWord ++ tailWord_7713610).sum := by decide
  have hdescent : baseEnd_7713610 < baseStart_7713610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713654 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7713654 : Nat := 118140960795 + 7713654 * 2 ^ 59
def prefixEnd_7713654 : Nat := 4983230072969 + 3 ^ 40 * 7713654 * 2
def baseEnd_7713654 : Nat := 3960812104476468526950557

theorem tailTrace_7713654 : CollatzResearch.WordTrace tailWord_7713654 prefixEnd_7713654 3960812104476468526950557 := by
  unfold tailWord_7713654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17583754649797276254109751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187560049597837613377170677 17583754649797276254109751)
  ·
    refine ⟨26375631974695914381164627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17583754649797276254109751 26375631974695914381164627)
    ·
      refine ⟨39563447962043871571746941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26375631974695914381164627 39563447962043871571746941)
      ·
        refine ⟨14836292985766451839405103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39563447962043871571746941 14836292985766451839405103)
        ·
          refine ⟨22254439478649677759107655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14836292985766451839405103 22254439478649677759107655)
          ·
            refine ⟨33381659217974516638661483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22254439478649677759107655 33381659217974516638661483)
            ·
              refine ⟨50072488826961774957992225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33381659217974516638661483 50072488826961774957992225)
              ·
                refine ⟨37554366620221331218494169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50072488826961774957992225 37554366620221331218494169)
                ·
                  refine ⟨28165774965165998413870627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37554366620221331218494169 28165774965165998413870627)
                  ·
                    refine ⟨42248662447748997620805941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28165774965165998413870627 42248662447748997620805941)
                    ·
                      refine ⟨3960812104476468526950557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42248662447748997620805941 3960812104476468526950557)
                      ·
                        rfl

theorem cell23_7713654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7713654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713654 prefixEnd_7713654 := by exact prefixLift 7713654
  have htrace : WordTrace (prefixWord ++ tailWord_7713654) baseStart_7713654 baseEnd_7713654 := by
    simpa [prefixWord, tailWord_7713654, baseEnd_7713654] using wordTrace_append hprefix tailTrace_7713654
  have hstable : (prefixWord ++ tailWord_7713654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713654).length < 2 ^ (prefixWord ++ tailWord_7713654).sum := by decide
  have hdescent : baseEnd_7713654 < baseStart_7713654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_7713660 : Nat := 118140960795 + 7713660 * 2 ^ 59
def prefixEnd_7713660 : Nat := 4983230072969 + 3 ^ 40 * 7713660 * 2
def baseEnd_7713660 : Nat := 3960815185360395503475529

theorem tailTrace_7713660 : CollatzResearch.WordTrace tailWord_7713660 prefixEnd_7713660 3960815185360395503475529 := by
  unfold tailWord_7713660
  simp only [CollatzResearch.WordTrace]
  refine ⟨140670146617367341545237217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187560195489823122060316289 140670146617367341545237217)
  ·
    refine ⟨105502609963025506158927913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140670146617367341545237217 105502609963025506158927913)
    ·
      refine ⟨79126957472269129619195935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105502609963025506158927913 79126957472269129619195935)
      ·
        refine ⟨118690436208403694428793903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79126957472269129619195935 118690436208403694428793903)
        ·
          refine ⟨178035654312605541643190855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118690436208403694428793903 178035654312605541643190855)
          ·
            refine ⟨267053481468908312464786283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178035654312605541643190855 267053481468908312464786283)
            ·
              refine ⟨400580222203362468697179425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267053481468908312464786283 400580222203362468697179425)
              ·
                refine ⟨300435166652521851522884569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400580222203362468697179425 300435166652521851522884569)
                ·
                  refine ⟨225326374989391388642163427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300435166652521851522884569 225326374989391388642163427)
                  ·
                    refine ⟨337989562484087082963245141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225326374989391388642163427 337989562484087082963245141)
                    ·
                      refine ⟨3960815185360395503475529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337989562484087082963245141 3960815185360395503475529)
                      ·
                        rfl

theorem cell23_7713660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_7713660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713660 prefixEnd_7713660 := by exact prefixLift 7713660
  have htrace : WordTrace (prefixWord ++ tailWord_7713660) baseStart_7713660 baseEnd_7713660 := by
    simpa [prefixWord, tailWord_7713660, baseEnd_7713660] using wordTrace_append hprefix tailTrace_7713660
  have hstable : (prefixWord ++ tailWord_7713660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713660).length < 2 ^ (prefixWord ++ tailWord_7713660).sum := by decide
  have hdescent : baseEnd_7713660 < baseStart_7713660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713684 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_7713684 : Nat := 118140960795 + 7713684 * 2 ^ 59
def prefixEnd_7713684 : Nat := 4983230072969 + 3 ^ 40 * 7713684 * 2
def baseEnd_7713684 : Nat := 3960827508896103409575419

theorem tailTrace_7713684 : CollatzResearch.WordTrace tailWord_7713684 prefixEnd_7713684 3960827508896103409575419 := by
  unfold tailWord_7713684
  simp only [CollatzResearch.WordTrace]
  refine ⟨140670584293323867594674053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187560779057765156792898737 140670584293323867594674053)
  ·
    refine ⟨26375734554998225174001385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140670584293323867594674053 26375734554998225174001385)
    ·
      refine ⟨19781800916248668880501039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26375734554998225174001385 19781800916248668880501039)
      ·
        refine ⟨29672701374373003320751559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19781800916248668880501039 29672701374373003320751559)
        ·
          refine ⟨44509052061559504981127339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29672701374373003320751559 44509052061559504981127339)
          ·
            refine ⟨66763578092339257471691009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44509052061559504981127339 66763578092339257471691009)
            ·
              refine ⟨50072683569254443103768257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66763578092339257471691009 50072683569254443103768257)
              ·
                refine ⟨37554512676940832327826193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50072683569254443103768257 37554512676940832327826193)
                ·
                  refine ⟨28165884507705624245869645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37554512676940832327826193 28165884507705624245869645)
                  ·
                    refine ⟨10562206690389609092201117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28165884507705624245869645 10562206690389609092201117)
                    ·
                      refine ⟨3960827508896103409575419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562206690389609092201117 3960827508896103409575419)
                      ·
                        rfl

theorem cell23_7713684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_7713684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713684 prefixEnd_7713684 := by exact prefixLift 7713684
  have htrace : WordTrace (prefixWord ++ tailWord_7713684) baseStart_7713684 baseEnd_7713684 := by
    simpa [prefixWord, tailWord_7713684, baseEnd_7713684] using wordTrace_append hprefix tailTrace_7713684
  have hstable : (prefixWord ++ tailWord_7713684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713684).length < 2 ^ (prefixWord ++ tailWord_7713684).sum := by decide
  have hdescent : baseEnd_7713684 < baseStart_7713684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713687 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 2, 5]
def baseStart_7713687 : Nat := 118140960795 + 7713687 * 2 ^ 59
def prefixEnd_7713687 : Nat := 4983230072969 + 3 ^ 40 * 7713687 * 2
def baseEnd_7713687 : Nat := 1320276349779355632612635

theorem tailTrace_7713687 : CollatzResearch.WordTrace tailWord_7713687 prefixEnd_7713687 1320276349779355632612635 := by
  unfold tailWord_7713687
  simp only [CollatzResearch.WordTrace]
  refine ⟨281341278005636866701707315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187560852003757911134471543 281341278005636866701707315)
  ·
    refine ⟨422011917008455300052560973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281341278005636866701707315 422011917008455300052560973)
    ·
      refine ⟨158254468878170737519710365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422011917008455300052560973 158254468878170737519710365)
      ·
        refine ⟨59345425829314026569891387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158254468878170737519710365 59345425829314026569891387)
        ·
          refine ⟨89018138743971039854837081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59345425829314026569891387 89018138743971039854837081)
          ·
            refine ⟨66763604057978279891127811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89018138743971039854837081 66763604057978279891127811)
            ·
              refine ⟨100145406086967419836691717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66763604057978279891127811 100145406086967419836691717)
              ·
                refine ⟨18777263641306391219379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100145406086967419836691717 18777263641306391219379697)
                ·
                  refine ⟨14082947730979793414534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18777263641306391219379697 14082947730979793414534773)
                  ·
                    refine ⟨1320276349779355632612635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14082947730979793414534773 1320276349779355632612635)
                    ·
                      rfl

theorem cell23_7713687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_7713687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713687 prefixEnd_7713687 := by exact prefixLift 7713687
  have htrace : WordTrace (prefixWord ++ tailWord_7713687) baseStart_7713687 baseEnd_7713687 := by
    simpa [prefixWord, tailWord_7713687, baseEnd_7713687] using wordTrace_append hprefix tailTrace_7713687
  have hstable : (prefixWord ++ tailWord_7713687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713687).length < 2 ^ (prefixWord ++ tailWord_7713687).sum := by decide
  have hdescent : baseEnd_7713687 < baseStart_7713687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713828 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_7713828 : Nat := 118140960795 + 7713828 * 2 ^ 59
def prefixEnd_7713828 : Nat := 4983230072969 + 3 ^ 40 * 7713828 * 2
def baseEnd_7713828 : Nat := 1320300483370116948724919

theorem tailTrace_7713828 : CollatzResearch.WordTrace tailWord_7713828 prefixEnd_7713828 1320300483370116948724919 := by
  unfold tailWord_7713828
  simp only [CollatzResearch.WordTrace]
  refine ⟨140673210349063023891295069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187564280465417365188393425 140673210349063023891295069)
  ·
    refine ⟨52752453880898633959235651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140673210349063023891295069 52752453880898633959235651)
    ·
      refine ⟨79128680821347950938853477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52752453880898633959235651 79128680821347950938853477)
      ·
        refine ⟨14836627654002740801035027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79128680821347950938853477 14836627654002740801035027)
        ·
          refine ⟨22254941481004111201552541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14836627654002740801035027 22254941481004111201552541)
          ·
            refine ⟨8345603055376541700582203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22254941481004111201552541 8345603055376541700582203)
            ·
              refine ⟨12518404583064812550873305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8345603055376541700582203 12518404583064812550873305)
              ·
                refine ⟨9388803437298609413154979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12518404583064812550873305 9388803437298609413154979)
                ·
                  refine ⟨14083205155947914119732469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388803437298609413154979 14083205155947914119732469)
                  ·
                    refine ⟨1320300483370116948724919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14083205155947914119732469 1320300483370116948724919)
                    ·
                      rfl

theorem cell23_7713828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_7713828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713828 prefixEnd_7713828 := by exact prefixLift 7713828
  have htrace : WordTrace (prefixWord ++ tailWord_7713828) baseStart_7713828 baseEnd_7713828 := by
    simpa [prefixWord, tailWord_7713828, baseEnd_7713828] using wordTrace_append hprefix tailTrace_7713828
  have hstable : (prefixWord ++ tailWord_7713828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713828).length < 2 ^ (prefixWord ++ tailWord_7713828).sum := by decide
  have hdescent : baseEnd_7713828 < baseStart_7713828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713848 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_7713848 : Nat := 118140960795 + 7713848 * 2 ^ 59
def prefixEnd_7713848 : Nat := 4983230072969 + 3 ^ 40 * 7713848 * 2
def baseEnd_7713848 : Nat := 3960911719723440767924665

theorem tailTrace_7713848 : CollatzResearch.WordTrace tailWord_7713848 prefixEnd_7713848 3960911719723440767924665 := by
  unfold tailWord_7713848
  simp only [CollatzResearch.WordTrace]
  refine ⟨140673575079026795599159099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187564766772035727465545465 140673575079026795599159099)
  ·
    refine ⟨211010362618540193398738649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140673575079026795599159099 211010362618540193398738649)
    ·
      refine ⟨158257771963905145049053987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211010362618540193398738649 158257771963905145049053987)
      ·
        refine ⟨237386657945857717573580981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158257771963905145049053987 237386657945857717573580981)
        ·
          refine ⟨22254999182424161022523217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237386657945857717573580981 22254999182424161022523217)
          ·
            refine ⟨16691249386818120766892413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22254999182424161022523217 16691249386818120766892413)
            ·
              refine ⟨6259218520056795287584655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16691249386818120766892413 6259218520056795287584655)
              ·
                refine ⟨9388827780085192931376983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259218520056795287584655 9388827780085192931376983)
                ·
                  refine ⟨14083241670127789397065475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388827780085192931376983 14083241670127789397065475)
                  ·
                    refine ⟨21124862505191684095598213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14083241670127789397065475 21124862505191684095598213)
                    ·
                      refine ⟨3960911719723440767924665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21124862505191684095598213 3960911719723440767924665)
                      ·
                        rfl

theorem cell23_7713848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_7713848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713848 prefixEnd_7713848 := by exact prefixLift 7713848
  have htrace : WordTrace (prefixWord ++ tailWord_7713848) baseStart_7713848 baseEnd_7713848 := by
    simpa [prefixWord, tailWord_7713848, baseEnd_7713848] using wordTrace_append hprefix tailTrace_7713848
  have hstable : (prefixWord ++ tailWord_7713848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713848).length < 2 ^ (prefixWord ++ tailWord_7713848).sum := by decide
  have hdescent : baseEnd_7713848 < baseStart_7713848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713854 : List Nat := [4, 2, 1, 3, 1, 12]
def baseStart_7713854 : Nat := 118140960795 + 7713854 * 2 ^ 59
def prefixEnd_7713854 : Nat := 4983230072969 + 3 ^ 40 * 7713854 * 2
def baseEnd_7713854 : Nat := 16300060907849249977159

theorem tailTrace_7713854 : CollatzResearch.WordTrace tailWord_7713854 prefixEnd_7713854 16300060907849249977159 := by
  unfold tailWord_7713854
  simp only [CollatzResearch.WordTrace]
  refine ⟨35168421124503981777879577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187564912664021236148691077 35168421124503981777879577)
  ·
    refine ⟨26376315843377986333409683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35168421124503981777879577 26376315843377986333409683)
    ·
      refine ⟨39564473765066979500114525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26376315843377986333409683 39564473765066979500114525)
      ·
        refine ⟨14836677661900117312542947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39564473765066979500114525 14836677661900117312542947)
        ·
          refine ⟨22255016492850175968814421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14836677661900117312542947 22255016492850175968814421)
          ·
            refine ⟨16300060907849249977159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22255016492850175968814421 16300060907849249977159)
            ·
              rfl

theorem cell23_7713854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 12].length) (baseStart_7713854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713854 prefixEnd_7713854 := by exact prefixLift 7713854
  have htrace : WordTrace (prefixWord ++ tailWord_7713854) baseStart_7713854 baseEnd_7713854 := by
    simpa [prefixWord, tailWord_7713854, baseEnd_7713854] using wordTrace_append hprefix tailTrace_7713854
  have hstable : (prefixWord ++ tailWord_7713854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713854).length < 2 ^ (prefixWord ++ tailWord_7713854).sum := by decide
  have hdescent : baseEnd_7713854 < baseStart_7713854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713864 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_7713864 : Nat := 118140960795 + 7713864 * 2 ^ 59
def prefixEnd_7713864 : Nat := 4983230072969 + 3 ^ 40 * 7713864 * 2
def baseEnd_7713864 : Nat := 3960919935413912705324591

theorem tailTrace_7713864 : CollatzResearch.WordTrace tailWord_7713864 prefixEnd_7713864 3960919935413912705324591 := by
  unfold tailWord_7713864
  simp only [CollatzResearch.WordTrace]
  refine ⟨140673866862997812965450323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187565155817330417287267097 140673866862997812965450323)
  ·
    refine ⟨211010800294496719448175485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140673866862997812965450323 211010800294496719448175485)
    ·
      refine ⟨79129050110436269793065807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211010800294496719448175485 79129050110436269793065807)
      ·
        refine ⟨118693575165654404689598711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79129050110436269793065807 118693575165654404689598711)
        ·
          refine ⟨178040362748481607034398067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118693575165654404689598711 178040362748481607034398067)
          ·
            refine ⟨267060544122722410551597101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178040362748481607034398067 267060544122722410551597101)
            ·
              refine ⟨100147704046020903956848913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267060544122722410551597101 100147704046020903956848913)
              ·
                refine ⟨75110778034515677967636685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100147704046020903956848913 75110778034515677967636685)
                ·
                  refine ⟨28166541762943379237863757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75110778034515677967636685 28166541762943379237863757)
                  ·
                    refine ⟨10562453161103767214198909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28166541762943379237863757 10562453161103767214198909)
                    ·
                      refine ⟨3960919935413912705324591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562453161103767214198909 3960919935413912705324591)
                      ·
                        rfl

theorem cell23_7713864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_7713864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713864 prefixEnd_7713864 := by exact prefixLift 7713864
  have htrace : WordTrace (prefixWord ++ tailWord_7713864) baseStart_7713864 baseEnd_7713864 := by
    simpa [prefixWord, tailWord_7713864, baseEnd_7713864] using wordTrace_append hprefix tailTrace_7713864
  have hstable : (prefixWord ++ tailWord_7713864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713864).length < 2 ^ (prefixWord ++ tailWord_7713864).sum := by decide
  have hdescent : baseEnd_7713864 < baseStart_7713864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713884 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_7713884 : Nat := 118140960795 + 7713884 * 2 ^ 59
def prefixEnd_7713884 : Nat := 4983230072969 + 3 ^ 40 * 7713884 * 2
def baseEnd_7713884 : Nat := 1320310068342334209024833

theorem tailTrace_7713884 : CollatzResearch.WordTrace tailWord_7713884 prefixEnd_7713884 1320310068342334209024833 := by
  unfold tailWord_7713884
  simp only [CollatzResearch.WordTrace]
  refine ⟨140674231592961584673314353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187565642123948779564419137 140674231592961584673314353)
  ·
    refine ⟨105505673694721188504985765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140674231592961584673314353 105505673694721188504985765)
    ·
      refine ⟨19782313817760222844684831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105505673694721188504985765 19782313817760222844684831)
      ·
        refine ⟨29673470726640334267027247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19782313817760222844684831 29673470726640334267027247)
        ·
          refine ⟨44510206089960501400540871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29673470726640334267027247 44510206089960501400540871)
          ·
            refine ⟨66765309134940752100811307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44510206089960501400540871 66765309134940752100811307)
            ·
              refine ⟨100147963702411128151216961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66765309134940752100811307 100147963702411128151216961)
              ·
                refine ⟨75110972776808346113412721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100147963702411128151216961 75110972776808346113412721)
                ·
                  refine ⟨56333229582606259585059541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75110972776808346113412721 56333229582606259585059541)
                  ·
                    refine ⟨1320310068342334209024833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56333229582606259585059541 1320310068342334209024833)
                    ·
                      rfl

theorem cell23_7713884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_7713884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7713884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7713884 prefixEnd_7713884 := by exact prefixLift 7713884
  have htrace : WordTrace (prefixWord ++ tailWord_7713884) baseStart_7713884 baseEnd_7713884 := by
    simpa [prefixWord, tailWord_7713884, baseEnd_7713884] using wordTrace_append hprefix tailTrace_7713884
  have hstable : (prefixWord ++ tailWord_7713884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713884).length < 2 ^ (prefixWord ++ tailWord_7713884).sum := by decide
  have hdescent : baseEnd_7713884 < baseStart_7713884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714008 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_7714008 : Nat := 118140960795 + 7714008 * 2 ^ 59
def prefixEnd_7714008 : Nat := 4983230072969 + 3 ^ 40 * 7714008 * 2
def baseEnd_7714008 : Nat := 1320331292209386713974643

theorem tailTrace_7714008 : CollatzResearch.WordTrace tailWord_7714008 prefixEnd_7714008 1320331292209386713974643 := by
  unfold tailWord_7714008
  simp only [CollatzResearch.WordTrace]
  refine ⟨140676492918736969262071339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187568657224982625682761785 140676492918736969262071339)
  ·
    refine ⟨211014739378105453893107009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140676492918736969262071339 211014739378105453893107009)
    ·
      refine ⟨158261054533579090419830257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211014739378105453893107009 158261054533579090419830257)
      ·
        refine ⟨118695790900184317814872693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158261054533579090419830257 118695790900184317814872693)
        ·
          refine ⟨11127730396892279795144315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118695790900184317814872693 11127730396892279795144315)
          ·
            refine ⟨16691595595338419692716473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127730396892279795144315 16691595595338419692716473)
            ·
              refine ⟨12518696696503814769537355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16691595595338419692716473 12518696696503814769537355)
              ·
                refine ⟨18778045044755722154306033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12518696696503814769537355 18778045044755722154306033)
                ·
                  refine ⟨14083533783566791615729525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18778045044755722154306033 14083533783566791615729525)
                  ·
                    refine ⟨1320331292209386713974643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14083533783566791615729525 1320331292209386713974643)
                    ·
                      rfl

theorem cell23_7714008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_7714008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714008 prefixEnd_7714008 := by exact prefixLift 7714008
  have htrace : WordTrace (prefixWord ++ tailWord_7714008) baseStart_7714008 baseEnd_7714008 := by
    simpa [prefixWord, tailWord_7714008, baseEnd_7714008] using wordTrace_append hprefix tailTrace_7714008
  have hstable : (prefixWord ++ tailWord_7714008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714008).length < 2 ^ (prefixWord ++ tailWord_7714008).sum := by decide
  have hdescent : baseEnd_7714008 < baseStart_7714008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714038 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_7714038 : Nat := 118140960795 + 7714038 * 2 ^ 59
def prefixEnd_7714038 : Nat := 4983230072969 + 3 ^ 40 * 7714038 * 2
def baseEnd_7714038 : Nat := 1320336427015931674849597

theorem tailTrace_7714038 : CollatzResearch.WordTrace tailWord_7714038 prefixEnd_7714038 1320336427015931674849597 := by
  unfold tailWord_7714038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584630001710328352983423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187569386684910169098489845 17584630001710328352983423)
  ·
    refine ⟨26376945002565492529475135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17584630001710328352983423 26376945002565492529475135)
    ·
      refine ⟨39565417503848238794212703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26376945002565492529475135 39565417503848238794212703)
      ·
        refine ⟨59348126255772358191319055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39565417503848238794212703 59348126255772358191319055)
        ·
          refine ⟨89022189383658537286978583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59348126255772358191319055 89022189383658537286978583)
          ·
            refine ⟨133533284075487805930467875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89022189383658537286978583 133533284075487805930467875)
            ·
              refine ⟨200299926113231708895701813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133533284075487805930467875 200299926113231708895701813)
              ·
                refine ⟨18778118073115472708972045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200299926113231708895701813 18778118073115472708972045)
                ·
                  refine ⟨7041794277418302265864517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18778118073115472708972045 7041794277418302265864517)
                  ·
                    refine ⟨1320336427015931674849597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7041794277418302265864517 1320336427015931674849597)
                    ·
                      rfl

theorem cell23_7714038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_7714038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714038 prefixEnd_7714038 := by exact prefixLift 7714038
  have htrace : WordTrace (prefixWord ++ tailWord_7714038) baseStart_7714038 baseEnd_7714038 := by
    simpa [prefixWord, tailWord_7714038, baseEnd_7714038] using wordTrace_append hprefix tailTrace_7714038
  have hstable : (prefixWord ++ tailWord_7714038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714038).length < 2 ^ (prefixWord ++ tailWord_7714038).sum := by decide
  have hdescent : baseEnd_7714038 < baseStart_7714038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714051 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 6]
def baseStart_7714051 : Nat := 118140960795 + 7714051 * 2 ^ 59
def prefixEnd_7714051 : Nat := 4983230072969 + 3 ^ 40 * 7714051 * 2
def baseEnd_7714051 : Nat := 440112884032922608187359

theorem tailTrace_7714051 : CollatzResearch.WordTrace tailWord_7714051 prefixEnd_7714051 440112884032922608187359 := by
  unfold tailWord_7714051
  simp only [CollatzResearch.WordTrace]
  refine ⟨281354554176318156867958007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187569702784212104578638671 281354554176318156867958007)
  ·
    refine ⟨422031831264477235301937011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281354554176318156867958007 422031831264477235301937011)
    ·
      refine ⟨633047746896715852952905517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422031831264477235301937011 633047746896715852952905517)
      ·
        refine ⟨237392905086268444857339569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633047746896715852952905517 237392905086268444857339569)
        ·
          refine ⟨178044678814701333643004677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237392905086268444857339569 178044678814701333643004677)
          ·
            refine ⟨33383377277756500058063377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178044678814701333643004677 33383377277756500058063377)
            ·
              refine ⟨25037532958317375043547533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33383377277756500058063377 25037532958317375043547533)
              ·
                refine ⟨9389074859369015641330325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25037532958317375043547533 9389074859369015641330325)
                ·
                  refine ⟨440112884032922608187359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9389074859369015641330325 440112884032922608187359)
                  ·
                    rfl

theorem cell23_7714051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 6].length) (baseStart_7714051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714051 prefixEnd_7714051 := by exact prefixLift 7714051
  have htrace : WordTrace (prefixWord ++ tailWord_7714051) baseStart_7714051 baseEnd_7714051 := by
    simpa [prefixWord, tailWord_7714051, baseEnd_7714051] using wordTrace_append hprefix tailTrace_7714051
  have hstable : (prefixWord ++ tailWord_7714051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714051).length < 2 ^ (prefixWord ++ tailWord_7714051).sum := by decide
  have hdescent : baseEnd_7714051 < baseStart_7714051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714131 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_7714131 : Nat := 118140960795 + 7714131 * 2 ^ 59
def prefixEnd_7714131 : Nat := 4983230072969 + 3 ^ 40 * 7714131 * 2
def baseEnd_7714131 : Nat := 3961057034748663160685863

theorem tailTrace_7714131 : CollatzResearch.WordTrace tailWord_7714131 prefixEnd_7714131 3961057034748663160685863 := by
  unfold tailWord_7714131
  simp only [CollatzResearch.WordTrace]
  refine ⟨281357472016028330530870247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187571648010685553687246831 281357472016028330530870247)
  ·
    refine ⟨422036208024042495796305371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281357472016028330530870247 422036208024042495796305371)
    ·
      refine ⟨633054312036063743694458057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422036208024042495796305371 633054312036063743694458057)
      ·
        refine ⟨474790734027047807770843543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633054312036063743694458057 474790734027047807770843543)
        ·
          refine ⟨712186101040571711656265315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474790734027047807770843543 712186101040571711656265315)
          ·
            refine ⟨1068279151560857567484397973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712186101040571711656265315 1068279151560857567484397973)
            ·
              refine ⟨50075585229415198475831155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1068279151560857567484397973 50075585229415198475831155)
              ·
                refine ⟨75113377844122797713746733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50075585229415198475831155 75113377844122797713746733)
                ·
                  refine ⟨28167516691546049142655025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75113377844122797713746733 28167516691546049142655025)
                  ·
                    refine ⟨21125637518659536856991269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28167516691546049142655025 21125637518659536856991269)
                    ·
                      refine ⟨3961057034748663160685863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21125637518659536856991269 3961057034748663160685863)
                      ·
                        rfl

theorem cell23_7714131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_7714131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714131 prefixEnd_7714131 := by exact prefixLift 7714131
  have htrace : WordTrace (prefixWord ++ tailWord_7714131) baseStart_7714131 baseEnd_7714131 := by
    simpa [prefixWord, tailWord_7714131, baseEnd_7714131] using wordTrace_append hprefix tailTrace_7714131
  have hstable : (prefixWord ++ tailWord_7714131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714131).length < 2 ^ (prefixWord ++ tailWord_7714131).sum := by decide
  have hdescent : baseEnd_7714131 < baseStart_7714131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714181 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_7714181 : Nat := 118140960795 + 7714181 * 2 ^ 59
def prefixEnd_7714181 : Nat := 4983230072969 + 3 ^ 40 * 7714181 * 2
def baseEnd_7714181 : Nat := 3961082708781387965060633

theorem tailTrace_7714181 : CollatzResearch.WordTrace tailWord_7714181 prefixEnd_7714181 3961082708781387965060633 := by
  unfold tailWord_7714181
  simp only [CollatzResearch.WordTrace]
  refine ⟨281359295665847189070190397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187572863777231459380126931 281359295665847189070190397)
  ·
    refine ⟨105509735874692695901321399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281359295665847189070190397 105509735874692695901321399)
    ·
      refine ⟨158264603812039043851982099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105509735874692695901321399 158264603812039043851982099)
      ·
        refine ⟨237396905718058565777973149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158264603812039043851982099 237396905718058565777973149)
        ·
          refine ⟨89023839644271962166739931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237396905718058565777973149 89023839644271962166739931)
          ·
            refine ⟨133535759466407943250109897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89023839644271962166739931 133535759466407943250109897)
            ·
              refine ⟨100151819599805957437582423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133535759466407943250109897 100151819599805957437582423)
              ·
                refine ⟨150227729399708936156373635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100151819599805957437582423 150227729399708936156373635)
                ·
                  refine ⟨225341594099563404234560453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150227729399708936156373635 225341594099563404234560453)
                  ·
                    refine ⟨42251548893668138293980085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225341594099563404234560453 42251548893668138293980085)
                    ·
                      refine ⟨3961082708781387965060633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42251548893668138293980085 3961082708781387965060633)
                      ·
                        rfl

theorem cell23_7714181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_7714181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714181 prefixEnd_7714181 := by exact prefixLift 7714181
  have htrace : WordTrace (prefixWord ++ tailWord_7714181) baseStart_7714181 baseEnd_7714181 := by
    simpa [prefixWord, tailWord_7714181, baseEnd_7714181] using wordTrace_append hprefix tailTrace_7714181
  have hstable : (prefixWord ++ tailWord_7714181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714181).length < 2 ^ (prefixWord ++ tailWord_7714181).sum := by decide
  have hdescent : baseEnd_7714181 < baseStart_7714181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714185 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_7714185 : Nat := 118140960795 + 7714185 * 2 ^ 59
def prefixEnd_7714185 : Nat := 4983230072969 + 3 ^ 40 * 7714185 * 2
def baseEnd_7714185 : Nat := 3961084762704005949410615

theorem tailTrace_7714185 : CollatzResearch.WordTrace tailWord_7714185 prefixEnd_7714185 3961084762704005949410615 := by
  unfold tailWord_7714185
  simp only [CollatzResearch.WordTrace]
  refine ⟨281359441557832697753336009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187572961038555131835557339 281359441557832697753336009)
  ·
    refine ⟨211019581168374523315002007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281359441557832697753336009 211019581168374523315002007)
    ·
      refine ⟨316529371752561784972503011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211019581168374523315002007 316529371752561784972503011)
      ·
        refine ⟨474794057628842677458754517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316529371752561784972503011 474794057628842677458754517)
        ·
          refine ⟨11127985725676000252939559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 474794057628842677458754517 11127985725676000252939559)
          ·
            refine ⟨16691978588514000379409339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127985725676000252939559 16691978588514000379409339)
            ·
              refine ⟨25037967882771000569114009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16691978588514000379409339 25037967882771000569114009)
              ·
                refine ⟨18778475912078250426835507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25037967882771000569114009 18778475912078250426835507)
                ·
                  refine ⟨28167713868117375640253261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18778475912078250426835507 28167713868117375640253261)
                  ·
                    refine ⟨10562892700544015865094973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28167713868117375640253261 10562892700544015865094973)
                    ·
                      refine ⟨3961084762704005949410615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562892700544015865094973 3961084762704005949410615)
                      ·
                        rfl

theorem cell23_7714185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_7714185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714185 prefixEnd_7714185 := by exact prefixLift 7714185
  have htrace : WordTrace (prefixWord ++ tailWord_7714185) baseStart_7714185 baseEnd_7714185 := by
    simpa [prefixWord, tailWord_7714185, baseEnd_7714185] using wordTrace_append hprefix tailTrace_7714185
  have hstable : (prefixWord ++ tailWord_7714185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714185).length < 2 ^ (prefixWord ++ tailWord_7714185).sum := by decide
  have hdescent : baseEnd_7714185 < baseStart_7714185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714202 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7714202 : Nat := 118140960795 + 7714202 * 2 ^ 59
def prefixEnd_7714202 : Nat := 4983230072969 + 3 ^ 40 * 7714202 * 2
def baseEnd_7714202 : Nat := 3961093491875132382898037

theorem tailTrace_7714202 : CollatzResearch.WordTrace tailWord_7714202 prefixEnd_7714202 3961093491875132382898037 := by
  unfold tailWord_7714202
  simp only [CollatzResearch.WordTrace]
  refine ⟨70340015399692777414176215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187573374399180739771136573 70340015399692777414176215)
  ·
    refine ⟨105510023099539166121264323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70340015399692777414176215 105510023099539166121264323)
    ·
      refine ⟨158265034649308749181896485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105510023099539166121264323 158265034649308749181896485)
      ·
        refine ⟨29674693996745390471605591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158265034649308749181896485 29674693996745390471605591)
        ·
          refine ⟨44512040995118085707408387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29674693996745390471605591 44512040995118085707408387)
          ·
            refine ⟨66768061492677128561112581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44512040995118085707408387 66768061492677128561112581)
            ·
              refine ⟨12519011529876961605208609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66768061492677128561112581 12519011529876961605208609)
              ·
                refine ⟨9389258647407721203906457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12519011529876961605208609 9389258647407721203906457)
                ·
                  refine ⟨7041943985555790902929843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9389258647407721203906457 7041943985555790902929843)
                  ·
                    refine ⟨10562915978333686354394765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041943985555790902929843 10562915978333686354394765)
                    ·
                      refine ⟨3961093491875132382898037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10562915978333686354394765 3961093491875132382898037)
                      ·
                        rfl

theorem cell23_7714202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7714202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714202 prefixEnd_7714202 := by exact prefixLift 7714202
  have htrace : WordTrace (prefixWord ++ tailWord_7714202) baseStart_7714202 baseEnd_7714202 := by
    simpa [prefixWord, tailWord_7714202, baseEnd_7714202] using wordTrace_append hprefix tailTrace_7714202
  have hstable : (prefixWord ++ tailWord_7714202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714202).length < 2 ^ (prefixWord ++ tailWord_7714202).sum := by decide
  have hdescent : baseEnd_7714202 < baseStart_7714202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714238 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7714238 : Nat := 118140960795 + 7714238 * 2 ^ 59
def prefixEnd_7714238 : Nat := 4983230072969 + 3 ^ 40 * 7714238 * 2
def baseEnd_7714238 : Nat := 3961111977178694242047871

theorem tailTrace_7714238 : CollatzResearch.WordTrace tailWord_7714238 prefixEnd_7714238 3961111977178694242047871 := by
  unfold tailWord_7714238
  simp only [CollatzResearch.WordTrace]
  refine ⟨35170171828330085975626921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187574249751093791870010245 35170171828330085975626921)
  ·
    refine ⟨26377628871247564481720191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35170171828330085975626921 26377628871247564481720191)
    ·
      refine ⟨39566443306871346722580287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26377628871247564481720191 39566443306871346722580287)
      ·
        refine ⟨59349664960307020083870431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39566443306871346722580287 59349664960307020083870431)
        ·
          refine ⟨89024497440460530125805647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59349664960307020083870431 89024497440460530125805647)
          ·
            refine ⟨133536746160690795188708471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89024497440460530125805647 133536746160690795188708471)
            ·
              refine ⟨200305119241036192783062707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133536746160690795188708471 200305119241036192783062707)
              ·
                refine ⟨300457678861554289174594061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200305119241036192783062707 300457678861554289174594061)
                ·
                  refine ⟨112671629573082858440472773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300457678861554289174594061 112671629573082858440472773)
                  ·
                    refine ⟨21125930544953035957588645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112671629573082858440472773 21125930544953035957588645)
                    ·
                      refine ⟨3961111977178694242047871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21125930544953035957588645 3961111977178694242047871)
                      ·
                        rfl

theorem cell23_7714238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7714238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714238 prefixEnd_7714238 := by exact prefixLift 7714238
  have htrace : WordTrace (prefixWord ++ tailWord_7714238) baseStart_7714238 baseEnd_7714238 := by
    simpa [prefixWord, tailWord_7714238, baseEnd_7714238] using wordTrace_append hprefix tailTrace_7714238
  have hstable : (prefixWord ++ tailWord_7714238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714238).length < 2 ^ (prefixWord ++ tailWord_7714238).sum := by decide
  have hdescent : baseEnd_7714238 < baseStart_7714238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714265 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 5]
def baseStart_7714265 : Nat := 118140960795 + 7714265 * 2 ^ 59
def prefixEnd_7714265 : Nat := 4983230072969 + 3 ^ 40 * 7714265 * 2
def baseEnd_7714265 : Nat := 440125093461818404045583

theorem tailTrace_7714265 : CollatzResearch.WordTrace tailWord_7714265 prefixEnd_7714265 440125093461818404045583 := by
  unfold tailWord_7714265
  simp only [CollatzResearch.WordTrace]
  refine ⟨281362359397542871416248249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187574906265028580944165499 281362359397542871416248249)
  ·
    refine ⟨211021769548157153562186187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281362359397542871416248249 211021769548157153562186187)
    ·
      refine ⟨316532654322235730343279281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211021769548157153562186187 316532654322235730343279281)
      ·
        refine ⟨237399490741676797757459461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316532654322235730343279281 237399490741676797757459461)
        ·
          refine ⟨44512404514064399579523649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237399490741676797757459461 44512404514064399579523649)
          ·
            refine ⟨33384303385548299684642737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44512404514064399579523649 33384303385548299684642737)
            ·
              refine ⟨25038227539161224763482053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33384303385548299684642737 25038227539161224763482053)
              ·
                refine ⟨4694667663592729643152885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25038227539161224763482053 4694667663592729643152885)
                ·
                  refine ⟨440125093461818404045583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4694667663592729643152885 440125093461818404045583)
                  ·
                    rfl

theorem cell23_7714265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 5].length) (baseStart_7714265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714265 prefixEnd_7714265 := by exact prefixLift 7714265
  have htrace : WordTrace (prefixWord ++ tailWord_7714265) baseStart_7714265 baseEnd_7714265 := by
    simpa [prefixWord, tailWord_7714265, baseEnd_7714265] using wordTrace_append hprefix tailTrace_7714265
  have hstable : (prefixWord ++ tailWord_7714265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714265).length < 2 ^ (prefixWord ++ tailWord_7714265).sum := by decide
  have hdescent : baseEnd_7714265 < baseStart_7714265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714275 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7714275 : Nat := 118140960795 + 7714275 * 2 ^ 59
def prefixEnd_7714275 : Nat := 4983230072969 + 3 ^ 40 * 7714275 * 2
def baseEnd_7714275 : Nat := 3961130975962910597285201

theorem tailTrace_7714275 : CollatzResearch.WordTrace tailWord_7714275 prefixEnd_7714275 3961130975962910597285201 := by
  unfold tailWord_7714275
  simp only [CollatzResearch.WordTrace]
  refine ⟨281362724127506643124112279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187575149418337762082741519 281362724127506643124112279)
  ·
    refine ⟨422044086191259964686168419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281362724127506643124112279 422044086191259964686168419)
    ·
      refine ⟨633066129286889947029252629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422044086191259964686168419 633066129286889947029252629)
      ·
        refine ⟨29674974810322966266996217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 633066129286889947029252629 29674974810322966266996217)
        ·
          refine ⟨22256231107742224700247163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29674974810322966266996217 22256231107742224700247163)
          ·
            refine ⟨33384346661613337050370745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22256231107742224700247163 33384346661613337050370745)
            ·
              refine ⟨25038259996210002787778059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33384346661613337050370745 25038259996210002787778059)
              ·
                refine ⟨37557389994315004181667089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25038259996210002787778059 37557389994315004181667089)
                ·
                  refine ⟨28168042495736253136250317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37557389994315004181667089 28168042495736253136250317)
                  ·
                    refine ⟨10563015935901094926093869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28168042495736253136250317 10563015935901094926093869)
                    ·
                      refine ⟨3961130975962910597285201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10563015935901094926093869 3961130975962910597285201)
                      ·
                        rfl

theorem cell23_7714275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7714275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714275 prefixEnd_7714275 := by exact prefixLift 7714275
  have htrace : WordTrace (prefixWord ++ tailWord_7714275) baseStart_7714275 baseEnd_7714275 := by
    simpa [prefixWord, tailWord_7714275, baseEnd_7714275] using wordTrace_append hprefix tailTrace_7714275
  have hstable : (prefixWord ++ tailWord_7714275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714275).length < 2 ^ (prefixWord ++ tailWord_7714275).sum := by decide
  have hdescent : baseEnd_7714275 < baseStart_7714275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714298 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_7714298 : Nat := 118140960795 + 7714298 * 2 ^ 59
def prefixEnd_7714298 : Nat := 4983230072969 + 3 ^ 40 * 7714298 * 2
def baseEnd_7714298 : Nat := 3961142786017964007297595

theorem tailTrace_7714298 : CollatzResearch.WordTrace tailWord_7714298 prefixEnd_7714298 3961142786017964007297595 := by
  unfold tailWord_7714298
  simp only [CollatzResearch.WordTrace]
  refine ⟨70340890751605829513049887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187575708670948878701466365 70340890751605829513049887)
  ·
    refine ⟨105511336127408744269574831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70340890751605829513049887 105511336127408744269574831)
    ·
      refine ⟨158267004191113116404362247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105511336127408744269574831 158267004191113116404362247)
      ·
        refine ⟨237400506286669674606543371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158267004191113116404362247 237400506286669674606543371)
        ·
          refine ⟨356100759430004511909815057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237400506286669674606543371 356100759430004511909815057)
          ·
            refine ⟨267075569572503383932361293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356100759430004511909815057 267075569572503383932361293)
            ·
              refine ⟨100153338589688768974635485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267075569572503383932361293 100153338589688768974635485)
              ·
                refine ⟨37557501971133288365488307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100153338589688768974635485 37557501971133288365488307)
                ·
                  refine ⟨56336252956699932548232461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37557501971133288365488307 56336252956699932548232461)
                  ·
                    refine ⟨21126094858762474705587173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56336252956699932548232461 21126094858762474705587173)
                    ·
                      refine ⟨3961142786017964007297595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21126094858762474705587173 3961142786017964007297595)
                      ·
                        rfl

theorem cell23_7714298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_7714298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714298 prefixEnd_7714298 := by exact prefixLift 7714298
  have htrace : WordTrace (prefixWord ++ tailWord_7714298) baseStart_7714298 baseEnd_7714298 := by
    simpa [prefixWord, tailWord_7714298, baseEnd_7714298] using wordTrace_append hprefix tailTrace_7714298
  have hstable : (prefixWord ++ tailWord_7714298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714298).length < 2 ^ (prefixWord ++ tailWord_7714298).sum := by decide
  have hdescent : baseEnd_7714298 < baseStart_7714298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714382 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_7714382 : Nat := 118140960795 + 7714382 * 2 ^ 59
def prefixEnd_7714382 : Nat := 4983230072969 + 3 ^ 40 * 7714382 * 2
def baseEnd_7714382 : Nat := 3961185918392941678647209

theorem tailTrace_7714382 : CollatzResearch.WordTrace tailWord_7714382 prefixEnd_7714382 3961185918392941678647209 := by
  unfold tailWord_7714382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35170828342264875049782175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187577751158746000265504933 35170828342264875049782175)
  ·
    refine ⟨52756242513397312574673263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35170828342264875049782175 52756242513397312574673263)
    ·
      refine ⟨79134363770095968862009895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52756242513397312574673263 79134363770095968862009895)
      ·
        refine ⟨118701545655143953293014843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79134363770095968862009895 118701545655143953293014843)
        ·
          refine ⟨178052318482715929939522265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118701545655143953293014843 178052318482715929939522265)
          ·
            refine ⟨133539238862036947454641699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178052318482715929939522265 133539238862036947454641699)
            ·
              refine ⟨200308858293055421181962549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133539238862036947454641699 200308858293055421181962549)
              ·
                refine ⟨18778955464973945735808989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200308858293055421181962549 18778955464973945735808989)
                ·
                  refine ⟨7042108299365229650928371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18778955464973945735808989 7042108299365229650928371)
                  ·
                    refine ⟨10563162449047844476392557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042108299365229650928371 10563162449047844476392557)
                    ·
                      refine ⟨3961185918392941678647209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10563162449047844476392557 3961185918392941678647209)
                      ·
                        rfl

theorem cell23_7714382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_7714382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714382 prefixEnd_7714382 := by exact prefixLift 7714382
  have htrace : WordTrace (prefixWord ++ tailWord_7714382) baseStart_7714382 baseEnd_7714382 := by
    simpa [prefixWord, tailWord_7714382, baseEnd_7714382] using wordTrace_append hprefix tailTrace_7714382
  have hstable : (prefixWord ++ tailWord_7714382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714382).length < 2 ^ (prefixWord ++ tailWord_7714382).sum := by decide
  have hdescent : baseEnd_7714382 < baseStart_7714382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714415 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 4, 4]
def baseStart_7714415 : Nat := 118140960795 + 7714415 * 2 ^ 59
def prefixEnd_7714415 : Nat := 4983230072969 + 3 ^ 40 * 7714415 * 2
def baseEnd_7714415 : Nat := 1320400954418180016511519

theorem tailTrace_7714415 : CollatzResearch.WordTrace tailWord_7714415 prefixEnd_7714415 1320400954418180016511519 := by
  unfold tailWord_7714415
  simp only [CollatzResearch.WordTrace]
  refine ⟨281367830346999447034208699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187578553564666298022805799 281367830346999447034208699)
  ·
    refine ⟨422051745520499170551313049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281367830346999447034208699 422051745520499170551313049)
    ·
      refine ⟨316538809140374377913484787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422051745520499170551313049 316538809140374377913484787)
      ·
        refine ⟨474808213710561566870227181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316538809140374377913484787 474808213710561566870227181)
        ·
          refine ⟨178053080141460587576335193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474808213710561566870227181 178053080141460587576335193)
          ·
            refine ⟨133539810106095440682251395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178053080141460587576335193 133539810106095440682251395)
            ·
              refine ⟨200309715159143161023377093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133539810106095440682251395 200309715159143161023377093)
              ·
                refine ⟨37558071592339342691883205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200309715159143161023377093 37558071592339342691883205)
                ·
                  refine ⟨7042138423563626754728101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37558071592339342691883205 7042138423563626754728101)
                  ·
                    refine ⟨1320400954418180016511519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042138423563626754728101 1320400954418180016511519)
                    ·
                      rfl

theorem cell23_7714415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_7714415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714415 prefixEnd_7714415 := by exact prefixLift 7714415
  have htrace : WordTrace (prefixWord ++ tailWord_7714415) baseStart_7714415 baseEnd_7714415 := by
    simpa [prefixWord, tailWord_7714415, baseEnd_7714415] using wordTrace_append hprefix tailTrace_7714415
  have hstable : (prefixWord ++ tailWord_7714415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714415).length < 2 ^ (prefixWord ++ tailWord_7714415).sum := by decide
  have hdescent : baseEnd_7714415 < baseStart_7714415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714416 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 1, 1, 3]
def baseStart_7714416 : Nat := 118140960795 + 7714416 * 2 ^ 59
def prefixEnd_7714416 : Nat := 4983230072969 + 3 ^ 40 * 7714416 * 2
def baseEnd_7714416 : Nat := 3961203376735194545622053

theorem tailTrace_7714416 : CollatzResearch.WordTrace tailWord_7714416 prefixEnd_7714416 3961203376735194545622053 := by
  unfold tailWord_7714416
  simp only [CollatzResearch.WordTrace]
  refine ⟨140683933409997912102497551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187578577879997216136663401 140683933409997912102497551)
  ·
    refine ⟨211025900114996868153746327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140683933409997912102497551 211025900114996868153746327)
    ·
      refine ⟨316538850172495302230619491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211025900114996868153746327 316538850172495302230619491)
      ·
        refine ⟨474808275258742953345929237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316538850172495302230619491 474808275258742953345929237)
        ·
          refine ⟨22256637902753575938090433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 474808275258742953345929237 22256637902753575938090433)
          ·
            refine ⟨16692478427065181953567825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22256637902753575938090433 16692478427065181953567825)
            ·
              refine ⟨12519358820298886465175869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16692478427065181953567825 12519358820298886465175869)
              ·
                refine ⟨4694759557612082424440951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12519358820298886465175869 4694759557612082424440951)
                ·
                  refine ⟨7042139336418123636661427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694759557612082424440951 7042139336418123636661427)
                  ·
                    refine ⟨10563209004627185454992141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042139336418123636661427 10563209004627185454992141)
                    ·
                      refine ⟨3961203376735194545622053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10563209004627185454992141 3961203376735194545622053)
                      ·
                        rfl

theorem cell23_7714416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 1, 3].length) (baseStart_7714416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714416 prefixEnd_7714416 := by exact prefixLift 7714416
  have htrace : WordTrace (prefixWord ++ tailWord_7714416) baseStart_7714416 baseEnd_7714416 := by
    simpa [prefixWord, tailWord_7714416, baseEnd_7714416] using wordTrace_append hprefix tailTrace_7714416
  have hstable : (prefixWord ++ tailWord_7714416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714416).length < 2 ^ (prefixWord ++ tailWord_7714416).sum := by decide
  have hdescent : baseEnd_7714416 < baseStart_7714416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714425 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7714425 : Nat := 118140960795 + 7714425 * 2 ^ 59
def prefixEnd_7714425 : Nat := 4983230072969 + 3 ^ 40 * 7714425 * 2
def baseEnd_7714425 : Nat := 3961207998061085010409511

theorem tailTrace_7714425 : CollatzResearch.WordTrace tailWord_7714425 prefixEnd_7714425 3961207998061085010409511 := by
  unfold tailWord_7714425
  simp only [CollatzResearch.WordTrace]
  refine ⟨281368195076963218742072729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187578796717975479161381819 281368195076963218742072729)
  ·
    refine ⟨211026146307722414056554547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281368195076963218742072729 211026146307722414056554547)
    ·
      refine ⟨316539219461583621084831821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211026146307722414056554547 316539219461583621084831821)
      ·
        refine ⟨118702207298093857906811933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316539219461583621084831821 118702207298093857906811933)
        ·
          refine ⟨44513327736785196715054475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118702207298093857906811933 44513327736785196715054475)
          ·
            refine ⟨66769991605177795072581713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44513327736785196715054475 66769991605177795072581713)
            ·
              refine ⟨50077493703883346304436285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66769991605177795072581713 50077493703883346304436285)
              ·
                refine ⟨18779060138956254864163607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50077493703883346304436285 18779060138956254864163607)
                ·
                  refine ⟨28168590208434382296245411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18779060138956254864163607 28168590208434382296245411)
                  ·
                    refine ⟨42252885312651573444368117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28168590208434382296245411 42252885312651573444368117)
                    ·
                      refine ⟨3961207998061085010409511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42252885312651573444368117 3961207998061085010409511)
                      ·
                        rfl

theorem cell23_7714425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7714425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714425 prefixEnd_7714425 := by exact prefixLift 7714425
  have htrace : WordTrace (prefixWord ++ tailWord_7714425) baseStart_7714425 baseEnd_7714425 := by
    simpa [prefixWord, tailWord_7714425, baseEnd_7714425] using wordTrace_append hprefix tailTrace_7714425
  have hstable : (prefixWord ++ tailWord_7714425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714425).length < 2 ^ (prefixWord ++ tailWord_7714425).sum := by decide
  have hdescent : baseEnd_7714425 < baseStart_7714425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714439 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_7714439 : Nat := 118140960795 + 7714439 * 2 ^ 59
def prefixEnd_7714439 : Nat := 4983230072969 + 3 ^ 40 * 7714439 * 2
def baseEnd_7714439 : Nat := 3961215186790247955634447

theorem tailTrace_7714439 : CollatzResearch.WordTrace tailWord_7714439 prefixEnd_7714439 3961215186790247955634447 := by
  unfold tailWord_7714439
  simp only [CollatzResearch.WordTrace]
  refine ⟨281368705698912499133082371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187579137132608332755388247 281368705698912499133082371)
  ·
    refine ⟨422053058548368748699623557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281368705698912499133082371 422053058548368748699623557)
    ·
      refine ⟨79134948477819140381179417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422053058548368748699623557 79134948477819140381179417)
      ·
        refine ⟨59351211358364355285884563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79134948477819140381179417 59351211358364355285884563)
        ·
          refine ⟨89026817037546532928826845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59351211358364355285884563 89026817037546532928826845)
          ·
            refine ⟨33385056389079949848310067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89026817037546532928826845 33385056389079949848310067)
            ·
              refine ⟨50077584583619924772465101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33385056389079949848310067 50077584583619924772465101)
              ·
                refine ⟨18779094218857471789674413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50077584583619924772465101 18779094218857471789674413)
                ·
                  refine ⟨7042160332071551921127905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18779094218857471789674413 7042160332071551921127905)
                  ·
                    refine ⟨5281620249053663940845929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7042160332071551921127905 5281620249053663940845929)
                    ·
                      refine ⟨3961215186790247955634447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5281620249053663940845929 3961215186790247955634447)
                      ·
                        rfl

theorem cell23_7714439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_7714439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714439 prefixEnd_7714439 := by exact prefixLift 7714439
  have htrace : WordTrace (prefixWord ++ tailWord_7714439) baseStart_7714439 baseEnd_7714439 := by
    simpa [prefixWord, tailWord_7714439, baseEnd_7714439] using wordTrace_append hprefix tailTrace_7714439
  have hstable : (prefixWord ++ tailWord_7714439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714439).length < 2 ^ (prefixWord ++ tailWord_7714439).sum := by decide
  have hdescent : baseEnd_7714439 < baseStart_7714439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714442 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_7714442 : Nat := 118140960795 + 7714442 * 2 ^ 59
def prefixEnd_7714442 : Nat := 4983230072969 + 3 ^ 40 * 7714442 * 2
def baseEnd_7714442 : Nat := 3961216727232211443896933

theorem tailTrace_7714442 : CollatzResearch.WordTrace tailWord_7714442 prefixEnd_7714442 3961216727232211443896933 := by
  unfold tailWord_7714442
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342203779475407661360395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187579210078601087096961053 70342203779475407661360395)
  ·
    refine ⟨105513305669213111492040593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70342203779475407661360395 105513305669213111492040593)
    ·
      refine ⟨79134979251909833619030445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105513305669213111492040593 79134979251909833619030445)
      ·
        refine ⟨29675617219466187607136417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79134979251909833619030445 29675617219466187607136417)
        ·
          refine ⟨22256712914599640705352313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29675617219466187607136417 22256712914599640705352313)
          ·
            refine ⟨16692534685949730529014235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22256712914599640705352313 16692534685949730529014235)
            ·
              refine ⟨25038802028924595793521353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692534685949730529014235 25038802028924595793521353)
              ·
                refine ⟨18779101521693446845141015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25038802028924595793521353 18779101521693446845141015)
                ·
                  refine ⟨28168652282540170267711523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18779101521693446845141015 28168652282540170267711523)
                  ·
                    refine ⟨42252978423810255401567285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28168652282540170267711523 42252978423810255401567285)
                    ·
                      refine ⟨3961216727232211443896933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42252978423810255401567285 3961216727232211443896933)
                      ·
                        rfl

theorem cell23_7714442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_7714442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714442 prefixEnd_7714442 := by exact prefixLift 7714442
  have htrace : WordTrace (prefixWord ++ tailWord_7714442) baseStart_7714442 baseEnd_7714442 := by
    simpa [prefixWord, tailWord_7714442, baseEnd_7714442] using wordTrace_append hprefix tailTrace_7714442
  have hstable : (prefixWord ++ tailWord_7714442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714442).length < 2 ^ (prefixWord ++ tailWord_7714442).sum := by decide
  have hdescent : baseEnd_7714442 < baseStart_7714442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714462 : List Nat := [4, 3, 1, 1, 1, 3, 1, 9]
def baseStart_7714462 : Nat := 118140960795 + 7714462 * 2 ^ 59
def prefixEnd_7714462 : Nat := 4983230072969 + 3 ^ 40 * 7714462 * 2
def baseEnd_7714462 : Nat := 146712110994270420949883

theorem tailTrace_7714462 : CollatzResearch.WordTrace tailWord_7714462 prefixEnd_7714462 146712110994270420949883 := by
  unfold tailWord_7714462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171193072228646757646205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187579696385219449374113093 35171193072228646757646205)
  ·
    refine ⟨13189197402085742534117327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35171193072228646757646205 13189197402085742534117327)
    ·
      refine ⟨19783796103128613801175991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189197402085742534117327 19783796103128613801175991)
      ·
        refine ⟨29675694154692920701763987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19783796103128613801175991 29675694154692920701763987)
        ·
          refine ⟨44513541232039381052645981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29675694154692920701763987 44513541232039381052645981)
          ·
            refine ⟨16692577962014767894742243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44513541232039381052645981 16692577962014767894742243)
            ·
              refine ⟨25038866943022151842113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692577962014767894742243 25038866943022151842113365)
              ·
                refine ⟨146712110994270420949883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25038866943022151842113365 146712110994270420949883)
                ·
                  rfl

theorem cell23_7714462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_7714462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714462 prefixEnd_7714462 := by exact prefixLift 7714462
  have htrace : WordTrace (prefixWord ++ tailWord_7714462) baseStart_7714462 baseEnd_7714462 := by
    simpa [prefixWord, tailWord_7714462, baseEnd_7714462] using wordTrace_append hprefix tailTrace_7714462
  have hstable : (prefixWord ++ tailWord_7714462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714462).length < 2 ^ (prefixWord ++ tailWord_7714462).sum := by decide
  have hdescent : baseEnd_7714462 < baseStart_7714462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714495 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_7714495 : Nat := 118140960795 + 7714495 * 2 ^ 59
def prefixEnd_7714495 : Nat := 4983230072969 + 3 ^ 40 * 7714495 * 2
def baseEnd_7714495 : Nat := 3961243941706899736534189

theorem tailTrace_7714495 : CollatzResearch.WordTrace tailWord_7714495 prefixEnd_7714495 3961243941706899736534189 := by
  unfold tailWord_7714495
  simp only [CollatzResearch.WordTrace]
  refine ⟨281370748186709620697120939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187580498791139747131413959 281370748186709620697120939)
  ·
    refine ⟨422056122280064431045681409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281370748186709620697120939 422056122280064431045681409)
    ·
      refine ⟨316542091710048323284261057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422056122280064431045681409 316542091710048323284261057)
      ·
        refine ⟨237406568782536242463195793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316542091710048323284261057 237406568782536242463195793)
        ·
          refine ⟨178054926586902181847396845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237406568782536242463195793 178054926586902181847396845)
          ·
            refine ⟨66770597470088318192773817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178054926586902181847396845 66770597470088318192773817)
            ·
              refine ⟨50077948102566238644580363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66770597470088318192773817 50077948102566238644580363)
              ·
                refine ⟨75116922153849357966870545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50077948102566238644580363 75116922153849357966870545)
                ·
                  refine ⟨56337691615387018475152909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75116922153849357966870545 56337691615387018475152909)
                  ·
                    refine ⟨21126634355770131928182341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56337691615387018475152909 21126634355770131928182341)
                    ·
                      refine ⟨3961243941706899736534189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21126634355770131928182341 3961243941706899736534189)
                      ·
                        rfl

theorem cell23_7714495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_7714495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714495 prefixEnd_7714495 := by exact prefixLift 7714495
  have htrace : WordTrace (prefixWord ++ tailWord_7714495) baseStart_7714495 baseEnd_7714495 := by
    simpa [prefixWord, tailWord_7714495, baseEnd_7714495] using wordTrace_append hprefix tailTrace_7714495
  have hstable : (prefixWord ++ tailWord_7714495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714495).length < 2 ^ (prefixWord ++ tailWord_7714495).sum := by decide
  have hdescent : baseEnd_7714495 < baseStart_7714495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714506 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_7714506 : Nat := 118140960795 + 7714506 * 2 ^ 59
def prefixEnd_7714506 : Nat := 4983230072969 + 3 ^ 40 * 7714506 * 2
def baseEnd_7714506 : Nat := 3961249589994099193496639

theorem tailTrace_7714506 : CollatzResearch.WordTrace tailWord_7714506 prefixEnd_7714506 3961249589994099193496639 := by
  unfold tailWord_7714506
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342787347417442393942843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187580766259779846383847581 70342787347417442393942843)
  ·
    refine ⟨105514181021126163590914265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70342787347417442393942843 105514181021126163590914265)
    ·
      refine ⟨79135635765844622693185699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105514181021126163590914265 79135635765844622693185699)
      ·
        refine ⟨118703453648766934039778549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79135635765844622693185699 118703453648766934039778549)
        ·
          refine ⟨11128448779571900066229239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118703453648766934039778549 11128448779571900066229239)
          ·
            refine ⟨16692673169357850099343859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128448779571900066229239 16692673169357850099343859)
            ·
              refine ⟨25039009754036775149015789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692673169357850099343859 25039009754036775149015789)
              ·
                refine ⟨9389628657763790680880921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25039009754036775149015789 9389628657763790680880921)
                ·
                  refine ⟨7042221493322843010660691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9389628657763790680880921 7042221493322843010660691)
                  ·
                    refine ⟨10563332239984264515991037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042221493322843010660691 10563332239984264515991037)
                    ·
                      refine ⟨3961249589994099193496639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10563332239984264515991037 3961249589994099193496639)
                      ·
                        rfl

theorem cell23_7714506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_7714506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714506 prefixEnd_7714506 := by exact prefixLift 7714506
  have htrace : WordTrace (prefixWord ++ tailWord_7714506) baseStart_7714506 baseEnd_7714506 := by
    simpa [prefixWord, tailWord_7714506, baseEnd_7714506] using wordTrace_append hprefix tailTrace_7714506
  have hstable : (prefixWord ++ tailWord_7714506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714506).length < 2 ^ (prefixWord ++ tailWord_7714506).sum := by decide
  have hdescent : baseEnd_7714506 < baseStart_7714506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714516 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7714516 : Nat := 118140960795 + 7714516 * 2 ^ 59
def prefixEnd_7714516 : Nat := 4983230072969 + 3 ^ 40 * 7714516 * 2
def baseEnd_7714516 : Nat := 3961254724800644154371593

theorem tailTrace_7714516 : CollatzResearch.WordTrace tailWord_7714516 prefixEnd_7714516 3961254724800644154371593 := by
  unfold tailWord_7714516
  simp only [CollatzResearch.WordTrace]
  refine ⟨140685757059816770641817701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187581009413089027522423601 140685757059816770641817701)
  ·
    refine ⟨26378579448715644495340819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140685757059816770641817701 26378579448715644495340819)
    ·
      refine ⟨39567869173073466743011229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26378579448715644495340819 39567869173073466743011229)
      ·
        refine ⟨14837950939902550028629211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39567869173073466743011229 14837950939902550028629211)
        ·
          refine ⟨22256926409853825042943817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837950939902550028629211 22256926409853825042943817)
          ·
            refine ⟨16692694807390368782207863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22256926409853825042943817 16692694807390368782207863)
            ·
              refine ⟨25039042211085553173311795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16692694807390368782207863 25039042211085553173311795)
              ·
                refine ⟨37558563316628329759967693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25039042211085553173311795 37558563316628329759967693)
                ·
                  refine ⟨14084461243735623659987885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37558563316628329759967693 14084461243735623659987885)
                  ·
                    refine ⟨5281672966400858872495457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14084461243735623659987885 5281672966400858872495457)
                    ·
                      refine ⟨3961254724800644154371593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5281672966400858872495457 3961254724800644154371593)
                      ·
                        rfl

theorem cell23_7714516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7714516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714516 prefixEnd_7714516 := by exact prefixLift 7714516
  have htrace : WordTrace (prefixWord ++ tailWord_7714516) baseStart_7714516 baseEnd_7714516 := by
    simpa [prefixWord, tailWord_7714516, baseEnd_7714516] using wordTrace_append hprefix tailTrace_7714516
  have hstable : (prefixWord ++ tailWord_7714516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714516).length < 2 ^ (prefixWord ++ tailWord_7714516).sum := by decide
  have hdescent : baseEnd_7714516 < baseStart_7714516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714542 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7714542 : Nat := 118140960795 + 7714542 * 2 ^ 59
def prefixEnd_7714542 : Nat := 4983230072969 + 3 ^ 40 * 7714542 * 2
def baseEnd_7714542 : Nat := 3961268075297661052646473

theorem tailTrace_7714542 : CollatzResearch.WordTrace tailWord_7714542 prefixEnd_7714542 3961268075297661052646473 := by
  unfold tailWord_7714542
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171557802192418465510235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187581641611692898482721253 35171557802192418465510235)
  ·
    refine ⟨52757336703288627698265353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35171557802192418465510235 52757336703288627698265353)
    ·
      refine ⟨39568002527466470773699015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52757336703288627698265353 39568002527466470773699015)
      ·
        refine ⟨59352003791199706160548523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39568002527466470773699015 59352003791199706160548523)
        ·
          refine ⟨89028005686799559240822785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59352003791199706160548523 89028005686799559240822785)
          ·
            refine ⟨66771004265099669430617089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89028005686799559240822785 66771004265099669430617089)
            ·
              refine ⟨50078253198824752072962817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66771004265099669430617089 50078253198824752072962817)
              ·
                refine ⟨37558689899118564054722113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50078253198824752072962817 37558689899118564054722113)
                ·
                  refine ⟨28169017424338923041041585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37558689899118564054722113 28169017424338923041041585)
                  ·
                    refine ⟨21126763068254192280781189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28169017424338923041041585 21126763068254192280781189)
                    ·
                      refine ⟨3961268075297661052646473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21126763068254192280781189 3961268075297661052646473)
                      ·
                        rfl

theorem cell23_7714542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7714542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714542 prefixEnd_7714542 := by exact prefixLift 7714542
  have htrace : WordTrace (prefixWord ++ tailWord_7714542) baseStart_7714542 baseEnd_7714542 := by
    simpa [prefixWord, tailWord_7714542, baseEnd_7714542] using wordTrace_append hprefix tailTrace_7714542
  have hstable : (prefixWord ++ tailWord_7714542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714542).length < 2 ^ (prefixWord ++ tailWord_7714542).sum := by decide
  have hdescent : baseEnd_7714542 < baseStart_7714542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714575 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_7714575 : Nat := 118140960795 + 7714575 * 2 ^ 59
def prefixEnd_7714575 : Nat := 4983230072969 + 3 ^ 40 * 7714575 * 2
def baseEnd_7714575 : Nat := 3961285020159259423533821

theorem tailTrace_7714575 : CollatzResearch.WordTrace tailWord_7714575 prefixEnd_7714575 3961285020159259423533821 := by
  unfold tailWord_7714575
  simp only [CollatzResearch.WordTrace]
  refine ⟨281373666026419794360033179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187582444017613196240022119 281373666026419794360033179)
  ·
    refine ⟨422060499039629691540049769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281373666026419794360033179 422060499039629691540049769)
    ·
      refine ⟨316545374279722268655037327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422060499039629691540049769 316545374279722268655037327)
      ·
        refine ⟨474818061419583402982555991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316545374279722268655037327 474818061419583402982555991)
        ·
          refine ⟨712227092129375104473833987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474818061419583402982555991 712227092129375104473833987)
          ·
            refine ⟨1068340638194062656710750981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712227092129375104473833987 1068340638194062656710750981)
            ·
              refine ⟨200313869661386748133265809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1068340638194062656710750981 200313869661386748133265809)
              ·
                refine ⟨150235402246040061099949357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200313869661386748133265809 150235402246040061099949357)
                ·
                  refine ⟨56338275842265022912481009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150235402246040061099949357 56338275842265022912481009)
                  ·
                    refine ⟨42253706881698767184360757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56338275842265022912481009 42253706881698767184360757)
                    ·
                      refine ⟨3961285020159259423533821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42253706881698767184360757 3961285020159259423533821)
                      ·
                        rfl

theorem cell23_7714575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_7714575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714575 prefixEnd_7714575 := by exact prefixLift 7714575
  have htrace : WordTrace (prefixWord ++ tailWord_7714575) baseStart_7714575 baseEnd_7714575 := by
    simpa [prefixWord, tailWord_7714575, baseEnd_7714575] using wordTrace_append hprefix tailTrace_7714575
  have hstable : (prefixWord ++ tailWord_7714575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714575).length < 2 ^ (prefixWord ++ tailWord_7714575).sum := by decide
  have hdescent : baseEnd_7714575 < baseStart_7714575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714635 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_7714635 : Nat := 118140960795 + 7714635 * 2 ^ 59
def prefixEnd_7714635 : Nat := 4983230072969 + 3 ^ 40 * 7714635 * 2
def baseEnd_7714635 : Nat := 3961315828998529188783545

theorem tailTrace_7714635 : CollatzResearch.WordTrace tailWord_7714635 prefixEnd_7714635 3961315828998529188783545 := by
  unfold tailWord_7714635
  simp only [CollatzResearch.WordTrace]
  refine ⟨281375854406202424607217359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187583902937468283071478239 281375854406202424607217359)
  ·
    refine ⟨422063781609303636910826039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281375854406202424607217359 422063781609303636910826039)
    ·
      refine ⟨633095672413955455366239059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422063781609303636910826039 633095672413955455366239059)
      ·
        refine ⟨949643508620933183049358589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633095672413955455366239059 949643508620933183049358589)
        ·
          refine ⟨356116315732849943643509471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949643508620933183049358589 356116315732849943643509471)
          ·
            refine ⟨534174473599274915465264207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356116315732849943643509471 534174473599274915465264207)
            ·
              refine ⟨801261710398912373197896311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534174473599274915465264207 801261710398912373197896311)
              ·
                refine ⟨1201892565598368559796844467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801261710398912373197896311 1201892565598368559796844467)
                ·
                  refine ⟨1802838848397552839695266701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201892565598368559796844467 1802838848397552839695266701)
                  ·
                    refine ⟨676064568149082314885725013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802838848397552839695266701 676064568149082314885725013)
                    ·
                      refine ⟨3961315828998529188783545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 676064568149082314885725013 3961315828998529188783545)
                      ·
                        rfl

theorem cell23_7714635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_7714635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714635 prefixEnd_7714635 := by exact prefixLift 7714635
  have htrace : WordTrace (prefixWord ++ tailWord_7714635) baseStart_7714635 baseEnd_7714635 := by
    simpa [prefixWord, tailWord_7714635, baseEnd_7714635] using wordTrace_append hprefix tailTrace_7714635
  have hstable : (prefixWord ++ tailWord_7714635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714635).length < 2 ^ (prefixWord ++ tailWord_7714635).sum := by decide
  have hdescent : baseEnd_7714635 < baseStart_7714635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714642 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_7714642 : Nat := 118140960795 + 7714642 * 2 ^ 59
def prefixEnd_7714642 : Nat := 4983230072969 + 3 ^ 40 * 7714642 * 2
def baseEnd_7714642 : Nat := 440146602595901184599557

theorem tailTrace_7714642 : CollatzResearch.WordTrace tailWord_7714642 prefixEnd_7714642 440146602595901184599557 := by
  unfold tailWord_7714642
  simp only [CollatzResearch.WordTrace]
  refine ⟨70344027429294266200680545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187584073144784709868481453 70344027429294266200680545)
  ·
    refine ⟨52758020571970699650510409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70344027429294266200680545 52758020571970699650510409)
    ·
      refine ⟨39568515428978024737882807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52758020571970699650510409 39568515428978024737882807)
      ·
        refine ⟨59352773143467037106824211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39568515428978024737882807 59352773143467037106824211)
        ·
          refine ⟨89029159715200555660236317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59352773143467037106824211 89029159715200555660236317)
          ·
            refine ⟨33385934893200208372588619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89029159715200555660236317 33385934893200208372588619)
            ·
              refine ⟨50078902339800312558882929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33385934893200208372588619 50078902339800312558882929)
              ·
                refine ⟨37559176754850234419162197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50078902339800312558882929 37559176754850234419162197)
                ·
                  refine ⟨440146602595901184599557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37559176754850234419162197 440146602595901184599557)
                  ·
                    rfl

theorem cell23_7714642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_7714642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714642 prefixEnd_7714642 := by exact prefixLift 7714642
  have htrace : WordTrace (prefixWord ++ tailWord_7714642) baseStart_7714642 baseEnd_7714642 := by
    simpa [prefixWord, tailWord_7714642, baseEnd_7714642] using wordTrace_append hprefix tailTrace_7714642
  have hstable : (prefixWord ++ tailWord_7714642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714642).length < 2 ^ (prefixWord ++ tailWord_7714642).sum := by decide
  have hdescent : baseEnd_7714642 < baseStart_7714642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714663 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 1, 4]
def baseStart_7714663 : Nat := 118140960795 + 7714663 * 2 ^ 59
def prefixEnd_7714663 : Nat := 4983230072969 + 3 ^ 40 * 7714663 * 2
def baseEnd_7714663 : Nat := 1320443402152285026411139

theorem tailTrace_7714663 : CollatzResearch.WordTrace tailWord_7714663 prefixEnd_7714663 1320443402152285026411139 := by
  unfold tailWord_7714663
  simp only [CollatzResearch.WordTrace]
  refine ⟨281376875650100985389236643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187584583766733990259491095 281376875650100985389236643)
  ·
    refine ⟨422065313475151478083854965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281376875650100985389236643 422065313475151478083854965)
    ·
      refine ⟨39568623138295451070361403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422065313475151478083854965 39568623138295451070361403)
      ·
        refine ⟨59352934707443176605542105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39568623138295451070361403 59352934707443176605542105)
        ·
          refine ⟨44514701030582382454156579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59352934707443176605542105 44514701030582382454156579)
          ·
            refine ⟨66772051545873573681234869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44514701030582382454156579 66772051545873573681234869)
            ·
              refine ⟨6259879832425647532615769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66772051545873573681234869 6259879832425647532615769)
              ·
                refine ⟨4694909874319235649461827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6259879832425647532615769 4694909874319235649461827)
                ·
                  refine ⟨7042364811478853474192741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694909874319235649461827 7042364811478853474192741)
                  ·
                    refine ⟨1320443402152285026411139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042364811478853474192741 1320443402152285026411139)
                    ·
                      rfl

theorem cell23_7714663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_7714663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714663 prefixEnd_7714663 := by exact prefixLift 7714663
  have htrace : WordTrace (prefixWord ++ tailWord_7714663) baseStart_7714663 baseEnd_7714663 := by
    simpa [prefixWord, tailWord_7714663, baseEnd_7714663] using wordTrace_append hprefix tailTrace_7714663
  have hstable : (prefixWord ++ tailWord_7714663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714663).length < 2 ^ (prefixWord ++ tailWord_7714663).sum := by decide
  have hdescent : baseEnd_7714663 < baseStart_7714663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714672 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_7714672 : Nat := 118140960795 + 7714672 * 2 ^ 59
def prefixEnd_7714672 : Nat := 4983230072969 + 3 ^ 40 * 7714672 * 2
def baseEnd_7714672 : Nat := 1320444942594248514673625

theorem tailTrace_7714672 : CollatzResearch.WordTrace tailWord_7714672 prefixEnd_7714672 1320444942594248514673625 := by
  unfold tailWord_7714672
  simp only [CollatzResearch.WordTrace]
  refine ⟨140688601953534189963157135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187584802604712253284209513 140688601953534189963157135)
  ·
    refine ⟨211032902930301284944735703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140688601953534189963157135 211032902930301284944735703)
    ·
      refine ⟨316549354395451927417103555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211032902930301284944735703 316549354395451927417103555)
      ·
        refine ⟨474824031593177891125655333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316549354395451927417103555 474824031593177891125655333)
        ·
          refine ⟨89029505923720854586060375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 474824031593177891125655333 89029505923720854586060375)
          ·
            refine ⟨133544258885581281879090563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89029505923720854586060375 133544258885581281879090563)
            ·
              refine ⟨200316388328371922818635845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133544258885581281879090563 200316388328371922818635845)
              ·
                refine ⟨37559322811569735528494221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200316388328371922818635845 37559322811569735528494221)
                ·
                  refine ⟨14084746054338650823185333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37559322811569735528494221 14084746054338650823185333)
                  ·
                    refine ⟨1320444942594248514673625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14084746054338650823185333 1320444942594248514673625)
                    ·
                      rfl

theorem cell23_7714672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_7714672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714672 prefixEnd_7714672 := by exact prefixLift 7714672
  have htrace : WordTrace (prefixWord ++ tailWord_7714672) baseStart_7714672 baseEnd_7714672 := by
    simpa [prefixWord, tailWord_7714672, baseEnd_7714672] using wordTrace_append hprefix tailTrace_7714672
  have hstable : (prefixWord ++ tailWord_7714672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714672).length < 2 ^ (prefixWord ++ tailWord_7714672).sum := by decide
  have hdescent : baseEnd_7714672 < baseStart_7714672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714710 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7714710 : Nat := 118140960795 + 7714710 * 2 ^ 59
def prefixEnd_7714710 : Nat := 4983230072969 + 3 ^ 40 * 7714710 * 2
def baseEnd_7714710 : Nat := 440150482227512932816189

theorem tailTrace_7714710 : CollatzResearch.WordTrace tailWord_7714710 prefixEnd_7714710 440150482227512932816189 := by
  unfold tailWord_7714710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17586161867558169526012349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187585726587287141610798389 17586161867558169526012349)
  ·
    refine ⟨6594810700334313572254631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17586161867558169526012349 6594810700334313572254631)
    ·
      refine ⟨9892216050501470358381947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6594810700334313572254631 9892216050501470358381947)
      ·
        refine ⟨14838324075752205537572921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9892216050501470358381947 14838324075752205537572921)
        ·
          refine ⟨11128743056814154153179691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14838324075752205537572921 11128743056814154153179691)
          ·
            refine ⟨16693114585221231229769537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128743056814154153179691 16693114585221231229769537)
            ·
              refine ⟨12519835938915923422327153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16693114585221231229769537 12519835938915923422327153)
              ·
                refine ⟨9389876954186942566745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12519835938915923422327153 9389876954186942566745365)
                ·
                  refine ⟨440150482227512932816189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9389876954186942566745365 440150482227512932816189)
                  ·
                    rfl

theorem cell23_7714710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7714710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714710 prefixEnd_7714710 := by exact prefixLift 7714710
  have htrace : WordTrace (prefixWord ++ tailWord_7714710) baseStart_7714710 baseEnd_7714710 := by
    simpa [prefixWord, tailWord_7714710, baseEnd_7714710] using wordTrace_append hprefix tailTrace_7714710
  have hstable : (prefixWord ++ tailWord_7714710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714710).length < 2 ^ (prefixWord ++ tailWord_7714710).sum := by decide
  have hdescent : baseEnd_7714710 < baseStart_7714710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714739 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4]
def baseStart_7714739 : Nat := 118140960795 + 7714739 * 2 ^ 59
def prefixEnd_7714739 : Nat := 4983230072969 + 3 ^ 40 * 7714739 * 2
def baseEnd_7714739 : Nat := 3961369230986596781883067

theorem tailTrace_7714739 : CollatzResearch.WordTrace tailWord_7714739 prefixEnd_7714739 3961369230986596781883067 := by
  unfold tailWord_7714739
  simp only [CollatzResearch.WordTrace]
  refine ⟨281379647597825650369003271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187586431731883766912668847 281379647597825650369003271)
  ·
    refine ⟨422069471396738475553504907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281379647597825650369003271 422069471396738475553504907)
    ·
      refine ⟨633104207095107713330257361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422069471396738475553504907 633104207095107713330257361)
      ·
        refine ⟨474828155321330784997693021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633104207095107713330257361 474828155321330784997693021)
        ·
          refine ⟨178060558245499044374134883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474828155321330784997693021 178060558245499044374134883)
          ·
            refine ⟨267090837368248566561202325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178060558245499044374134883 267090837368248566561202325)
            ·
              refine ⟨12519883001636651557556359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267090837368248566561202325 12519883001636651557556359)
              ·
                refine ⟨18779824502454977336334539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12519883001636651557556359 18779824502454977336334539)
                ·
                  refine ⟨28169736753682466004501809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18779824502454977336334539 28169736753682466004501809)
                  ·
                    refine ⟨21127302565261849503376357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28169736753682466004501809 21127302565261849503376357)
                    ·
                      refine ⟨3961369230986596781883067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21127302565261849503376357 3961369230986596781883067)
                      ·
                        rfl

theorem cell23_7714739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_7714739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714739 prefixEnd_7714739 := by exact prefixLift 7714739
  have htrace : WordTrace (prefixWord ++ tailWord_7714739) baseStart_7714739 baseEnd_7714739 := by
    simpa [prefixWord, tailWord_7714739, baseEnd_7714739] using wordTrace_append hprefix tailTrace_7714739
  have hstable : (prefixWord ++ tailWord_7714739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714739).length < 2 ^ (prefixWord ++ tailWord_7714739).sum := by decide
  have hdescent : baseEnd_7714739 < baseStart_7714739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714760 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_7714760 : Nat := 118140960795 + 7714760 * 2 ^ 59
def prefixEnd_7714760 : Nat := 4983230072969 + 3 ^ 40 * 7714760 * 2
def baseEnd_7714760 : Nat := 3961380014080341199720471

theorem tailTrace_7714760 : CollatzResearch.WordTrace tailWord_7714760 prefixEnd_7714760 3961380014080341199720471 := by
  unfold tailWord_7714760
  simp only [CollatzResearch.WordTrace]
  refine ⟨140690206765374785477758867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187586942353833047303678489 140690206765374785477758867)
  ·
    refine ⟨211035310148062178216638301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140690206765374785477758867 211035310148062178216638301)
    ·
      refine ⟨79138241305523316831239363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211035310148062178216638301 79138241305523316831239363)
      ·
        refine ⟨118707361958284975246859045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79138241305523316831239363 118707361958284975246859045)
        ·
          refine ⟨22257630367178432858786071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118707361958284975246859045 22257630367178432858786071)
          ·
            refine ⟨33386445550767649288179107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22257630367178432858786071 33386445550767649288179107)
            ·
              refine ⟨50079668326151473932268661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33386445550767649288179107 50079668326151473932268661)
              ·
                refine ⟨4694968905576700681150187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50079668326151473932268661 4694968905576700681150187)
                ·
                  refine ⟨7042453358365051021725281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694968905576700681150187 7042453358365051021725281)
                  ·
                    refine ⟨5281840018773788266293961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7042453358365051021725281 5281840018773788266293961)
                    ·
                      refine ⟨3961380014080341199720471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5281840018773788266293961 3961380014080341199720471)
                      ·
                        rfl

theorem cell23_7714760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_7714760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714760 prefixEnd_7714760 := by exact prefixLift 7714760
  have htrace : WordTrace (prefixWord ++ tailWord_7714760) baseStart_7714760 baseEnd_7714760 := by
    simpa [prefixWord, tailWord_7714760, baseEnd_7714760] using wordTrace_append hprefix tailTrace_7714760
  have hstable : (prefixWord ++ tailWord_7714760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714760).length < 2 ^ (prefixWord ++ tailWord_7714760).sum := by decide
  have hdescent : baseEnd_7714760 < baseStart_7714760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714770 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_7714770 : Nat := 118140960795 + 7714770 * 2 ^ 59
def prefixEnd_7714770 : Nat := 4983230072969 + 3 ^ 40 * 7714770 * 2
def baseEnd_7714770 : Nat := 1320461716295628720198475

theorem tailTrace_7714770 : CollatzResearch.WordTrace tailWord_7714770 prefixEnd_7714770 1320461716295628720198475 := by
  unfold tailWord_7714770
  simp only [CollatzResearch.WordTrace]
  refine ⟨70345194565178335665845441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187587185507142228442254509 70345194565178335665845441)
  ·
    refine ⟨52758895923883751749384081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70345194565178335665845441 52758895923883751749384081)
    ·
      refine ⟨39569171942912813812038061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52758895923883751749384081 39569171942912813812038061)
      ·
        refine ⟨14838439478592305179514273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39569171942912813812038061 14838439478592305179514273)
        ·
          refine ⟨11128829608944228884635705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14838439478592305179514273 11128829608944228884635705)
          ·
            refine ⟨8346622206708171663476779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11128829608944228884635705 8346622206708171663476779)
            ·
              refine ⟨12519933310062257495215169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8346622206708171663476779 12519933310062257495215169)
              ·
                refine ⟨9389949982546693121411377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12519933310062257495215169 9389949982546693121411377)
                ·
                  refine ⟨7042462486910019841058533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9389949982546693121411377 7042462486910019841058533)
                  ·
                    refine ⟨1320461716295628720198475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042462486910019841058533 1320461716295628720198475)
                    ·
                      rfl

theorem cell23_7714770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_7714770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714770 prefixEnd_7714770 := by exact prefixLift 7714770
  have htrace : WordTrace (prefixWord ++ tailWord_7714770) baseStart_7714770 baseEnd_7714770 := by
    simpa [prefixWord, tailWord_7714770, baseEnd_7714770] using wordTrace_append hprefix tailTrace_7714770
  have hstable : (prefixWord ++ tailWord_7714770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714770).length < 2 ^ (prefixWord ++ tailWord_7714770).sum := by decide
  have hdescent : baseEnd_7714770 < baseStart_7714770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714776 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_7714776 : Nat := 118140960795 + 7714776 * 2 ^ 59
def prefixEnd_7714776 : Nat := 4983230072969 + 3 ^ 40 * 7714776 * 2
def baseEnd_7714776 : Nat := 3961388229770813137120397

theorem tailTrace_7714776 : CollatzResearch.WordTrace tailWord_7714776 prefixEnd_7714776 3961388229770813137120397 := by
  unfold tailWord_7714776
  simp only [CollatzResearch.WordTrace]
  refine ⟨140690498549345802844050091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187587331399127737125400121 140690498549345802844050091)
  ·
    refine ⟨211035747824018704266075137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140690498549345802844050091 211035747824018704266075137)
    ·
      refine ⟨158276810868014028199556353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211035747824018704266075137 158276810868014028199556353)
      ·
        refine ⟨118707608151010521149667265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158276810868014028199556353 118707608151010521149667265)
        ·
          refine ⟨89030706113257890862250449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118707608151010521149667265 89030706113257890862250449)
          ·
            refine ⟨66773029584943418146687837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89030706113257890862250449 66773029584943418146687837)
            ·
              refine ⟨25039886094353781805007939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66773029584943418146687837 25039886094353781805007939)
              ·
                refine ⟨37559829141530672707511909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25039886094353781805007939 37559829141530672707511909)
                ·
                  refine ⟨7042467964037001132658483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37559829141530672707511909 7042467964037001132658483)
                  ·
                    refine ⟨10563701946055501698987725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042467964037001132658483 10563701946055501698987725)
                    ·
                      refine ⟨3961388229770813137120397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10563701946055501698987725 3961388229770813137120397)
                      ·
                        rfl

theorem cell23_7714776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_7714776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714776 prefixEnd_7714776 := by exact prefixLift 7714776
  have htrace : WordTrace (prefixWord ++ tailWord_7714776) baseStart_7714776 baseEnd_7714776 := by
    simpa [prefixWord, tailWord_7714776, baseEnd_7714776] using wordTrace_append hprefix tailTrace_7714776
  have hstable : (prefixWord ++ tailWord_7714776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714776).length < 2 ^ (prefixWord ++ tailWord_7714776).sum := by decide
  have hdescent : baseEnd_7714776 < baseStart_7714776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714780 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7714780 : Nat := 118140960795 + 7714780 * 2 ^ 59
def prefixEnd_7714780 : Nat := 4983230072969 + 3 ^ 40 * 7714780 * 2
def baseEnd_7714780 : Nat := 3961390283693431121470379

theorem tailTrace_7714780 : CollatzResearch.WordTrace tailWord_7714780 prefixEnd_7714780 3961390283693431121470379 := by
  unfold tailWord_7714780
  simp only [CollatzResearch.WordTrace]
  refine ⟨140690571495338557185622897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187587428660451409580830529 140690571495338557185622897)
  ·
    refine ⟨105517928621503917889217173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140690571495338557185622897 105517928621503917889217173)
    ·
      refine ⟨4946152904132996151057055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105517928621503917889217173 4946152904132996151057055)
      ·
        refine ⟨7419229356199494226585583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4946152904132996151057055 7419229356199494226585583)
        ·
          refine ⟨11128844034299241339878375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419229356199494226585583 11128844034299241339878375)
          ·
            refine ⟨16693266051448862009817563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128844034299241339878375 16693266051448862009817563)
            ·
              refine ⟨25039899077173293014726345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16693266051448862009817563 25039899077173293014726345)
              ·
                refine ⟨18779924307879969761044759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25039899077173293014726345 18779924307879969761044759)
                ·
                  refine ⟨28169886461819954641567139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18779924307879969761044759 28169886461819954641567139)
                  ·
                    refine ⟨42254829692729931962350709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28169886461819954641567139 42254829692729931962350709)
                    ·
                      refine ⟨3961390283693431121470379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42254829692729931962350709 3961390283693431121470379)
                      ·
                        rfl

theorem cell23_7714780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7714780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714780 prefixEnd_7714780 := by exact prefixLift 7714780
  have htrace : WordTrace (prefixWord ++ tailWord_7714780) baseStart_7714780 baseEnd_7714780 := by
    simpa [prefixWord, tailWord_7714780, baseEnd_7714780] using wordTrace_append hprefix tailTrace_7714780
  have hstable : (prefixWord ++ tailWord_7714780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714780).length < 2 ^ (prefixWord ++ tailWord_7714780).sum := by decide
  have hdescent : baseEnd_7714780 < baseStart_7714780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714850 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_7714850 : Nat := 118140960795 + 7714850 * 2 ^ 59
def prefixEnd_7714850 : Nat := 4983230072969 + 3 ^ 40 * 7714850 * 2
def baseEnd_7714850 : Nat := 3961426227339245847595057

theorem tailTrace_7714850 : CollatzResearch.WordTrace tailWord_7714850 prefixEnd_7714850 3961426227339245847595057 := by
  unfold tailWord_7714850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70345924025105879081573501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187589130733615677550862669 70345924025105879081573501)
  ·
    refine ⟨26379721509414704655590063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70345924025105879081573501 26379721509414704655590063)
    ·
      refine ⟨39569582264122056983385095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26379721509414704655590063 39569582264122056983385095)
      ·
        refine ⟨59354373396183085475077643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39569582264122056983385095 59354373396183085475077643)
        ·
          refine ⟨89031560094274628212616465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59354373396183085475077643 89031560094274628212616465)
          ·
            refine ⟨66773670070705971159462349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89031560094274628212616465 66773670070705971159462349)
            ·
              refine ⟨25040126276514739184798381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66773670070705971159462349 25040126276514739184798381)
              ·
                refine ⟨9390047353693027194299393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25040126276514739184798381 9390047353693027194299393)
                ·
                  refine ⟨7042535515269770395724545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390047353693027194299393 7042535515269770395724545)
                  ·
                    refine ⟨5281901636452327796793409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7042535515269770395724545 5281901636452327796793409)
                    ·
                      refine ⟨3961426227339245847595057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5281901636452327796793409 3961426227339245847595057)
                      ·
                        rfl

theorem cell23_7714850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_7714850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714850 prefixEnd_7714850 := by exact prefixLift 7714850
  have htrace : WordTrace (prefixWord ++ tailWord_7714850) baseStart_7714850 baseEnd_7714850 := by
    simpa [prefixWord, tailWord_7714850, baseEnd_7714850] using wordTrace_append hprefix tailTrace_7714850
  have hstable : (prefixWord ++ tailWord_7714850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714850).length < 2 ^ (prefixWord ++ tailWord_7714850).sum := by decide
  have hdescent : baseEnd_7714850 < baseStart_7714850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714869 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7714869 : Nat := 118140960795 + 7714869 * 2 ^ 59
def prefixEnd_7714869 : Nat := 4983230072969 + 3 ^ 40 * 7714869 * 2
def baseEnd_7714869 : Nat := 1320478661157227091085823

theorem tailTrace_7714869 : CollatzResearch.WordTrace tailWord_7714869 prefixEnd_7714869 1320478661157227091085823 := by
  unfold tailWord_7714869
  simp only [CollatzResearch.WordTrace]
  refine ⟨281384389087354682571235661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187589592724903121714157107 281384389087354682571235661)
  ·
    refine ⟨105519145907758005964213373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281384389087354682571235661 105519145907758005964213373)
    ·
      refine ⟨39569679715409252236580015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105519145907758005964213373 39569679715409252236580015)
      ·
        refine ⟨59354519573113878354870023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39569679715409252236580015 59354519573113878354870023)
        ·
          refine ⟨89031779359670817532305035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59354519573113878354870023 89031779359670817532305035)
          ·
            refine ⟨133547669039506226298457553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89031779359670817532305035 133547669039506226298457553)
            ·
              refine ⟨100160751779629669723843165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133547669039506226298457553 100160751779629669723843165)
              ·
                refine ⟨37560281917361126146441187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100160751779629669723843165 37560281917361126146441187)
                ·
                  refine ⟨56340422876041689219661781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37560281917361126146441187 56340422876041689219661781)
                  ·
                    refine ⟨1320478661157227091085823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56340422876041689219661781 1320478661157227091085823)
                    ·
                      rfl

theorem cell23_7714869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7714869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714869 prefixEnd_7714869 := by exact prefixLift 7714869
  have htrace : WordTrace (prefixWord ++ tailWord_7714869) baseStart_7714869 baseEnd_7714869 := by
    simpa [prefixWord, tailWord_7714869, baseEnd_7714869] using wordTrace_append hprefix tailTrace_7714869
  have hstable : (prefixWord ++ tailWord_7714869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714869).length < 2 ^ (prefixWord ++ tailWord_7714869).sum := by decide
  have hdescent : baseEnd_7714869 < baseStart_7714869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714879 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_7714879 : Nat := 118140960795 + 7714879 * 2 ^ 59
def prefixEnd_7714879 : Nat := 4983230072969 + 3 ^ 40 * 7714879 * 2
def baseEnd_7714879 : Nat := 3961441118278226234132423

theorem tailTrace_7714879 : CollatzResearch.WordTrace tailWord_7714879 prefixEnd_7714879 3961441118278226234132423 := by
  unfold tailWord_7714879
  simp only [CollatzResearch.WordTrace]
  refine ⟨281384753817318454279099691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187589835878212302852733127 281384753817318454279099691)
  ·
    refine ⟨422077130725977681418649537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281384753817318454279099691 422077130725977681418649537)
    ·
      refine ⟨316557848044483261063987153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422077130725977681418649537 316557848044483261063987153)
      ·
        refine ⟨237418386033362445797990365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316557848044483261063987153 237418386033362445797990365)
        ·
          refine ⟨89031894762510917174246387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237418386033362445797990365 89031894762510917174246387)
          ·
            refine ⟨133547842143766375761369581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89031894762510917174246387 133547842143766375761369581)
            ·
              refine ⟨50080440803912390910513593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133547842143766375761369581 50080440803912390910513593)
              ·
                refine ⟨37560330602934293182885195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50080440803912390910513593 37560330602934293182885195)
                ·
                  refine ⟨56340495904401439774327793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37560330602934293182885195 56340495904401439774327793)
                  ·
                    refine ⟨42255371928301079830745845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56340495904401439774327793 42255371928301079830745845)
                    ·
                      refine ⟨3961441118278226234132423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42255371928301079830745845 3961441118278226234132423)
                      ·
                        rfl

theorem cell23_7714879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_7714879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714879 prefixEnd_7714879 := by exact prefixLift 7714879
  have htrace : WordTrace (prefixWord ++ tailWord_7714879) baseStart_7714879 baseEnd_7714879 := by
    simpa [prefixWord, tailWord_7714879, baseEnd_7714879] using wordTrace_append hprefix tailTrace_7714879
  have hstable : (prefixWord ++ tailWord_7714879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714879).length < 2 ^ (prefixWord ++ tailWord_7714879).sum := by decide
  have hdescent : baseEnd_7714879 < baseStart_7714879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714893 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_7714893 : Nat := 118140960795 + 7714893 * 2 ^ 59
def prefixEnd_7714893 : Nat := 4983230072969 + 3 ^ 40 * 7714893 * 2
def baseEnd_7714893 : Nat := 3961448307007389179357359

theorem tailTrace_7714893 : CollatzResearch.WordTrace tailWord_7714893 prefixEnd_7714893 3961448307007389179357359 := by
  unfold tailWord_7714893
  simp only [CollatzResearch.WordTrace]
  refine ⟨281385264439267734670109333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187590176292845156446739555 281385264439267734670109333)
  ·
    refine ⟨13189934270590675062661375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281385264439267734670109333 13189934270590675062661375)
    ·
      refine ⟨19784901405886012593992063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189934270590675062661375 19784901405886012593992063)
      ·
        refine ⟨29677352108829018890988095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19784901405886012593992063 29677352108829018890988095)
        ·
          refine ⟨44516028163243528336482143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29677352108829018890988095 44516028163243528336482143)
          ·
            refine ⟨66774042244865292504723215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44516028163243528336482143 66774042244865292504723215)
            ·
              refine ⟨100161063367297938757084823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66774042244865292504723215 100161063367297938757084823)
              ·
                refine ⟨150241595050946908135627235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100161063367297938757084823 150241595050946908135627235)
                ·
                  refine ⟨225362392576420362203440853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150241595050946908135627235 225362392576420362203440853)
                  ·
                    refine ⟨5281931076009852239143145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225362392576420362203440853 5281931076009852239143145)
                    ·
                      refine ⟨3961448307007389179357359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5281931076009852239143145 3961448307007389179357359)
                      ·
                        rfl

theorem cell23_7714893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_7714893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714893 prefixEnd_7714893 := by exact prefixLift 7714893
  have htrace : WordTrace (prefixWord ++ tailWord_7714893) baseStart_7714893 baseEnd_7714893 := by
    simpa [prefixWord, tailWord_7714893, baseEnd_7714893] using wordTrace_append hprefix tailTrace_7714893
  have hstable : (prefixWord ++ tailWord_7714893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714893).length < 2 ^ (prefixWord ++ tailWord_7714893).sum := by decide
  have hdescent : baseEnd_7714893 < baseStart_7714893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714916 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_7714916 : Nat := 118140960795 + 7714916 * 2 ^ 59
def prefixEnd_7714916 : Nat := 4983230072969 + 3 ^ 40 * 7714916 * 2
def baseEnd_7714916 : Nat := 1320486705687480863123251

theorem tailTrace_7714916 : CollatzResearch.WordTrace tailWord_7714916 prefixEnd_7714916 1320486705687480863123251 := by
  unfold tailWord_7714916
  simp only [CollatzResearch.WordTrace]
  refine ⟨140693051659092204799098301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187590735545456273065464401 140693051659092204799098301)
  ·
    refine ⟨52759894372159576799661863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140693051659092204799098301 52759894372159576799661863)
    ·
      refine ⟨79139841558239365199492795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52759894372159576799661863 79139841558239365199492795)
      ·
        refine ⟨118709762337359047799239193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79139841558239365199492795 118709762337359047799239193)
        ·
          refine ⟨89032321753019285849429395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118709762337359047799239193 89032321753019285849429395)
          ·
            refine ⟨133548482629528928774144093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89032321753019285849429395 133548482629528928774144093)
            ·
              refine ⟨50080680986073348290304035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133548482629528928774144093 50080680986073348290304035)
              ·
                refine ⟨75121021479110022435456053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50080680986073348290304035 75121021479110022435456053)
                ·
                  refine ⟨7042595763666564603324005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75121021479110022435456053 7042595763666564603324005)
                  ·
                    refine ⟨1320486705687480863123251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042595763666564603324005 1320486705687480863123251)
                    ·
                      rfl

theorem cell23_7714916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_7714916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714916 prefixEnd_7714916 := by exact prefixLift 7714916
  have htrace : WordTrace (prefixWord ++ tailWord_7714916) baseStart_7714916 baseEnd_7714916 := by
    simpa [prefixWord, tailWord_7714916, baseEnd_7714916] using wordTrace_append hprefix tailTrace_7714916
  have hstable : (prefixWord ++ tailWord_7714916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714916).length < 2 ^ (prefixWord ++ tailWord_7714916).sum := by decide
  have hdescent : baseEnd_7714916 < baseStart_7714916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714929 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 8]
def baseStart_7714929 : Nat := 118140960795 + 7714929 * 2 ^ 59
def prefixEnd_7714929 : Nat := 4983230072969 + 3 ^ 40 * 7714929 * 2
def baseEnd_7714929 : Nat := 440162976923439004278577

theorem tailTrace_7714929 : CollatzResearch.WordTrace tailWord_7714929 prefixEnd_7714929 440162976923439004278577 := by
  unfold tailWord_7714929
  simp only [CollatzResearch.WordTrace]
  refine ⟨281386577467137312818419841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187591051644758208545613227 281386577467137312818419841)
  ·
    refine ⟨211039933100352984613814881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281386577467137312818419841 211039933100352984613814881)
    ·
      refine ⟨158279949825264738460361161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211039933100352984613814881 158279949825264738460361161)
      ·
        refine ⟨118709962368948553845270871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158279949825264738460361161 118709962368948553845270871)
        ·
          refine ⟨178064943553422830767906307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118709962368948553845270871 178064943553422830767906307)
          ·
            refine ⟨267097415330134246151859461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178064943553422830767906307 267097415330134246151859461)
            ·
              refine ⟨50080765374400171153473649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267097415330134246151859461 50080765374400171153473649)
              ·
                refine ⟨37560574030800128365105237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50080765374400171153473649 37560574030800128365105237)
                ·
                  refine ⟨440162976923439004278577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37560574030800128365105237 440162976923439004278577)
                  ·
                    rfl

theorem cell23_7714929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_7714929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714929 prefixEnd_7714929 := by exact prefixLift 7714929
  have htrace : WordTrace (prefixWord ++ tailWord_7714929) baseStart_7714929 baseEnd_7714929 := by
    simpa [prefixWord, tailWord_7714929, baseEnd_7714929] using wordTrace_append hprefix tailTrace_7714929
  have hstable : (prefixWord ++ tailWord_7714929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714929).length < 2 ^ (prefixWord ++ tailWord_7714929).sum := by decide
  have hdescent : baseEnd_7714929 < baseStart_7714929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7714969 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_7714969 : Nat := 118140960795 + 7714969 * 2 ^ 59
def prefixEnd_7714969 : Nat := 4983230072969 + 3 ^ 40 * 7714969 * 2
def baseEnd_7714969 : Nat := 3961487331537130882007009

theorem tailTrace_7714969 : CollatzResearch.WordTrace tailWord_7714969 prefixEnd_7714969 3961487331537130882007009 := by
  unfold tailWord_7714969
  simp only [CollatzResearch.WordTrace]
  refine ⟨281388036386992399649875961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187592024257994933099917307 281388036386992399649875961)
  ·
    refine ⟨211041027290244299737406971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281388036386992399649875961 211041027290244299737406971)
    ·
      refine ⟨316561540935366449606110457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211041027290244299737406971 316561540935366449606110457)
      ·
        refine ⟨237421155701524837204582843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316561540935366449606110457 237421155701524837204582843)
        ·
          refine ⟨356131733552287255806874265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237421155701524837204582843 356131733552287255806874265)
          ·
            refine ⟨267098800164215441855155699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356131733552287255806874265 267098800164215441855155699)
            ·
              refine ⟨400648200246323162782733549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267098800164215441855155699 400648200246323162782733549)
              ·
                refine ⟨150243075092371186043525081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400648200246323162782733549 150243075092371186043525081)
                ·
                  refine ⟨112682306319278389532643811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150243075092371186043525081 112682306319278389532643811)
                  ·
                    refine ⟨169023459478917584298965717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112682306319278389532643811 169023459478917584298965717)
                    ·
                      refine ⟨3961487331537130882007009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169023459478917584298965717 3961487331537130882007009)
                      ·
                        rfl

theorem cell23_7714969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_7714969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7714969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7714969 prefixEnd_7714969 := by exact prefixLift 7714969
  have htrace : WordTrace (prefixWord ++ tailWord_7714969) baseStart_7714969 baseEnd_7714969 := by
    simpa [prefixWord, tailWord_7714969, baseEnd_7714969] using wordTrace_append hprefix tailTrace_7714969
  have hstable : (prefixWord ++ tailWord_7714969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7714969).length < 2 ^ (prefixWord ++ tailWord_7714969).sum := by decide
  have hdescent : baseEnd_7714969 < baseStart_7714969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7714969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715016 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_7715016 : Nat := 118140960795 + 7715016 * 2 ^ 59
def prefixEnd_7715016 : Nat := 4983230072969 + 3 ^ 40 * 7715016 * 2
def baseEnd_7715016 : Nat := 3961511465127892198119293

theorem tailTrace_7715016 : CollatzResearch.WordTrace tailWord_7715016 prefixEnd_7715016 3961511465127892198119293 := by
  unfold tailWord_7715016
  simp only [CollatzResearch.WordTrace]
  refine ⟨140694875308911063338418451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187593167078548084451224601 140694875308911063338418451)
  ·
    refine ⟨211042312963366595007627677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140694875308911063338418451 211042312963366595007627677)
    ·
      refine ⟨79140867361262473127860379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211042312963366595007627677 79140867361262473127860379)
      ·
        refine ⟨118711301041893709691790569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79140867361262473127860379 118711301041893709691790569)
        ·
          refine ⟨89033475781420282268842927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118711301041893709691790569 89033475781420282268842927)
          ·
            refine ⟨133550213672130423403264391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89033475781420282268842927 133550213672130423403264391)
            ·
              refine ⟨200325320508195635104896587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133550213672130423403264391 200325320508195635104896587)
              ·
                refine ⟨300487980762293452657344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200325320508195635104896587 300487980762293452657344881)
                ·
                  refine ⟨225365985571720089493008661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300487980762293452657344881 225365985571720089493008661)
                  ·
                    refine ⟨10564030573674379194984781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225365985571720089493008661 10564030573674379194984781)
                    ·
                      refine ⟨3961511465127892198119293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564030573674379194984781 3961511465127892198119293)
                      ·
                        rfl

theorem cell23_7715016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_7715016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715016 prefixEnd_7715016 := by exact prefixLift 7715016
  have htrace : WordTrace (prefixWord ++ tailWord_7715016) baseStart_7715016 baseEnd_7715016 := by
    simpa [prefixWord, tailWord_7715016, baseEnd_7715016] using wordTrace_append hprefix tailTrace_7715016
  have hstable : (prefixWord ++ tailWord_7715016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715016).length < 2 ^ (prefixWord ++ tailWord_7715016).sum := by decide
  have hdescent : baseEnd_7715016 < baseStart_7715016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715023 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 2, 4]
def baseStart_7715023 : Nat := 118140960795 + 7715023 * 2 ^ 59
def prefixEnd_7715023 : Nat := 4983230072969 + 3 ^ 40 * 7715023 * 2
def baseEnd_7715023 : Nat := 1320505019830824556910587

theorem tailTrace_7715023 : CollatzResearch.WordTrace tailWord_7715023 prefixEnd_7715023 1320505019830824556910587 := by
  unfold tailWord_7715023
  simp only [CollatzResearch.WordTrace]
  refine ⟨281390005928796766872341723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187593337285864511248227815 281390005928796766872341723)
  ·
    refine ⟨422085008893195150308512585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281390005928796766872341723 422085008893195150308512585)
    ·
      refine ⟨316563756669896362731384439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422085008893195150308512585 316563756669896362731384439)
      ·
        refine ⟨474845635004844544097076659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316563756669896362731384439 474845635004844544097076659)
        ·
          refine ⟨712268452507266816145614989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474845635004844544097076659 712268452507266816145614989)
          ·
            refine ⟨267100669690225056054605621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712268452507266816145614989 267100669690225056054605621)
            ·
              refine ⟨25040687783458599005119277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267100669690225056054605621 25040687783458599005119277)
              ·
                refine ⟨9390257918796974626919729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25040687783458599005119277 9390257918796974626919729)
                ·
                  refine ⟨7042693439097730970189797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390257918796974626919729 7042693439097730970189797)
                  ·
                    refine ⟨1320505019830824556910587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042693439097730970189797 1320505019830824556910587)
                    ·
                      rfl

theorem cell23_7715023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_7715023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715023 prefixEnd_7715023 := by exact prefixLift 7715023
  have htrace : WordTrace (prefixWord ++ tailWord_7715023) baseStart_7715023 baseEnd_7715023 := by
    simpa [prefixWord, tailWord_7715023, baseEnd_7715023] using wordTrace_append hprefix tailTrace_7715023
  have hstable : (prefixWord ++ tailWord_7715023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715023).length < 2 ^ (prefixWord ++ tailWord_7715023).sum := by decide
  have hdescent : baseEnd_7715023 < baseStart_7715023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715047 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7715047 : Nat := 118140960795 + 7715047 * 2 ^ 59
def prefixEnd_7715047 : Nat := 4983230072969 + 3 ^ 40 * 7715047 * 2
def baseEnd_7715047 : Nat := 3961527383028181576831651

theorem tailTrace_7715047 : CollatzResearch.WordTrace tailWord_7715047 prefixEnd_7715047 3961527383028181576831651 := by
  unfold tailWord_7715047
  simp only [CollatzResearch.WordTrace]
  refine ⟨281390881280709818971215395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187593920853806545980810263 281390881280709818971215395)
  ·
    refine ⟨422086321921064728456823093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281390881280709818971215395 422086321921064728456823093)
    ·
      refine ⟨39570592680099818292827165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422086321921064728456823093 39570592680099818292827165)
      ·
        refine ⟨14838972255037431859810187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39570592680099818292827165 14838972255037431859810187)
        ·
          refine ⟨22258458382556147789715281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14838972255037431859810187 22258458382556147789715281)
          ·
            refine ⟨16693843786917110842286461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22258458382556147789715281 16693843786917110842286461)
            ·
              refine ⟨6260191420093916565857423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16693843786917110842286461 6260191420093916565857423)
              ·
                refine ⟨9390287130140874848786135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260191420093916565857423 9390287130140874848786135)
                ·
                  refine ⟨14085430695211312273179203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390287130140874848786135 14085430695211312273179203)
                  ·
                    refine ⟨21128146042816968409768805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14085430695211312273179203 21128146042816968409768805)
                    ·
                      refine ⟨3961527383028181576831651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21128146042816968409768805 3961527383028181576831651)
                      ·
                        rfl

theorem cell23_7715047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7715047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715047 prefixEnd_7715047 := by exact prefixLift 7715047
  have htrace : WordTrace (prefixWord ++ tailWord_7715047) baseStart_7715047 baseEnd_7715047 := by
    simpa [prefixWord, tailWord_7715047, baseEnd_7715047] using wordTrace_append hprefix tailTrace_7715047
  have hstable : (prefixWord ++ tailWord_7715047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715047).length < 2 ^ (prefixWord ++ tailWord_7715047).sum := by decide
  have hdescent : baseEnd_7715047 < baseStart_7715047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715053 : List Nat := [1, 5, 1, 2, 4, 10]
def baseStart_7715053 : Nat := 118140960795 + 7715053 * 2 ^ 59
def prefixEnd_7715053 : Nat := 4983230072969 + 3 ^ 40 * 7715053 * 2
def baseEnd_7715053 : Nat := 16302594501695919972661

theorem tailTrace_7715053 : CollatzResearch.WordTrace tailWord_7715053 prefixEnd_7715053 16302594501695919972661 := by
  unfold tailWord_7715053
  simp only [CollatzResearch.WordTrace]
  refine ⟨281391100118688081995933813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187594066745792054663955875 281391100118688081995933813)
  ·
    refine ⟨26380415636127007687118795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281391100118688081995933813 26380415636127007687118795)
    ·
      refine ⟨39570623454190511530678193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26380415636127007687118795 39570623454190511530678193)
      ·
        refine ⟨29677967590642883648008645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39570623454190511530678193 29677967590642883648008645)
        ·
          refine ⟨5564618923245540684001621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29677967590642883648008645 5564618923245540684001621)
          ·
            refine ⟨16302594501695919972661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5564618923245540684001621 16302594501695919972661)
            ·
              rfl

theorem cell23_7715053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 10].length) (baseStart_7715053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715053 prefixEnd_7715053 := by exact prefixLift 7715053
  have htrace : WordTrace (prefixWord ++ tailWord_7715053) baseStart_7715053 baseEnd_7715053 := by
    simpa [prefixWord, tailWord_7715053, baseEnd_7715053] using wordTrace_append hprefix tailTrace_7715053
  have hstable : (prefixWord ++ tailWord_7715053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715053).length < 2 ^ (prefixWord ++ tailWord_7715053).sum := by decide
  have hdescent : baseEnd_7715053 < baseStart_7715053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715066 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_7715066 : Nat := 118140960795 + 7715066 * 2 ^ 59
def prefixEnd_7715066 : Nat := 4983230072969 + 3 ^ 40 * 7715066 * 2
def baseEnd_7715066 : Nat := 1320512379720205667498021

theorem tailTrace_7715066 : CollatzResearch.WordTrace tailWord_7715066 prefixEnd_7715066 1320512379720205667498021 := by
  unfold tailWord_7715066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70347893566910246304039263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187594382845093990144104701 70347893566910246304039263)
  ·
    refine ⟨105521840350365369456058895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70347893566910246304039263 105521840350365369456058895)
    ·
      refine ⟨158282760525548054184088343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105521840350365369456058895 158282760525548054184088343)
      ·
        refine ⟨237424140788322081276132515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158282760525548054184088343 237424140788322081276132515)
        ·
          refine ⟨356136211182483121914198773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237424140788322081276132515 356136211182483121914198773)
          ·
            refine ⟨33387769798357792679456135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356136211182483121914198773 33387769798357792679456135)
            ·
              refine ⟨50081654697536689019184203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33387769798357792679456135 50081654697536689019184203)
              ·
                refine ⟨75122482046305033528776305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50081654697536689019184203 75122482046305033528776305)
                ·
                  refine ⟨56341861534728775146582229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75122482046305033528776305 56341861534728775146582229)
                  ·
                    refine ⟨1320512379720205667498021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56341861534728775146582229 1320512379720205667498021)
                    ·
                      rfl

theorem cell23_7715066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_7715066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715066 prefixEnd_7715066 := by exact prefixLift 7715066
  have htrace : WordTrace (prefixWord ++ tailWord_7715066) baseStart_7715066 baseEnd_7715066 := by
    simpa [prefixWord, tailWord_7715066, baseEnd_7715066] using wordTrace_append hprefix tailTrace_7715066
  have hstable : (prefixWord ++ tailWord_7715066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715066).length < 2 ^ (prefixWord ++ tailWord_7715066).sum := by decide
  have hdescent : baseEnd_7715066 < baseStart_7715066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715080 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_7715080 : Nat := 118140960795 + 7715080 * 2 ^ 59
def prefixEnd_7715080 : Nat := 4983230072969 + 3 ^ 40 * 7715080 * 2
def baseEnd_7715080 : Nat := 3961544327889779947718999

theorem tailTrace_7715080 : CollatzResearch.WordTrace tailWord_7715080 prefixEnd_7715080 3961544327889779947718999 := by
  unfold tailWord_7715080
  simp only [CollatzResearch.WordTrace]
  refine ⟨140696042444795132803583347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187594723259726843738111129 140696042444795132803583347)
  ·
    refine ⟨211044063667192699205375021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140696042444795132803583347 211044063667192699205375021)
    ·
      refine ⟨79141523875197262202015633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211044063667192699205375021 79141523875197262202015633)
      ·
        refine ⟨59356142906397946651511725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79141523875197262202015633 59356142906397946651511725)
        ·
          refine ⟨22258553589899229994316897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59356142906397946651511725 22258553589899229994316897)
          ·
            refine ⟨16693915192424422495737673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22258553589899229994316897 16693915192424422495737673)
            ·
              refine ⟨12520436394318316871803255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16693915192424422495737673 12520436394318316871803255)
              ·
                refine ⟨18780654591477475307704883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12520436394318316871803255 18780654591477475307704883)
                ·
                  refine ⟨28170981887216212961557325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18780654591477475307704883 28170981887216212961557325)
                  ·
                    refine ⟨10564118207706079860583997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28170981887216212961557325 10564118207706079860583997)
                    ·
                      refine ⟨3961544327889779947718999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564118207706079860583997 3961544327889779947718999)
                      ·
                        rfl

theorem cell23_7715080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_7715080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715080 prefixEnd_7715080 := by exact prefixLift 7715080
  have htrace : WordTrace (prefixWord ++ tailWord_7715080) baseStart_7715080 baseEnd_7715080 := by
    simpa [prefixWord, tailWord_7715080, baseEnd_7715080] using wordTrace_append hprefix tailTrace_7715080
  have hstable : (prefixWord ++ tailWord_7715080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715080).length < 2 ^ (prefixWord ++ tailWord_7715080).sum := by decide
  have hdescent : baseEnd_7715080 < baseStart_7715080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715096 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_7715096 : Nat := 118140960795 + 7715096 * 2 ^ 59
def prefixEnd_7715096 : Nat := 4983230072969 + 3 ^ 40 * 7715096 * 2
def baseEnd_7715096 : Nat := 1320517514526750628372975

theorem tailTrace_7715096 : CollatzResearch.WordTrace tailWord_7715096 prefixEnd_7715096 1320517514526750628372975 := by
  unfold tailWord_7715096
  simp only [CollatzResearch.WordTrace]
  refine ⟨140696334228766150169874571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187595112305021533559832761 140696334228766150169874571)
  ·
    refine ⟨211044501343149225254811857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140696334228766150169874571 211044501343149225254811857)
    ·
      refine ⟨158283376007361918941108893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211044501343149225254811857 158283376007361918941108893)
      ·
        refine ⟨59356266002760719602915835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158283376007361918941108893 59356266002760719602915835)
        ·
          refine ⟨89034399004141079404373753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59356266002760719602915835 89034399004141079404373753)
          ·
            refine ⟨66775799253105809553280315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89034399004141079404373753 66775799253105809553280315)
            ·
              refine ⟨100163698879658714329920473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66775799253105809553280315 100163698879658714329920473)
              ·
                refine ⟨75122774159744035747440355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100163698879658714329920473 75122774159744035747440355)
                ·
                  refine ⟨112684161239616053621160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75122774159744035747440355 112684161239616053621160533)
                  ·
                    refine ⟨1320517514526750628372975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112684161239616053621160533 1320517514526750628372975)
                    ·
                      rfl

theorem cell23_7715096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_7715096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715096 prefixEnd_7715096 := by exact prefixLift 7715096
  have htrace : WordTrace (prefixWord ++ tailWord_7715096) baseStart_7715096 baseEnd_7715096 := by
    simpa [prefixWord, tailWord_7715096, baseEnd_7715096] using wordTrace_append hprefix tailTrace_7715096
  have hstable : (prefixWord ++ tailWord_7715096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715096).length < 2 ^ (prefixWord ++ tailWord_7715096).sum := by decide
  have hdescent : baseEnd_7715096 < baseStart_7715096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715101 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7715101 : Nat := 118140960795 + 7715101 * 2 ^ 59
def prefixEnd_7715101 : Nat := 4983230072969 + 3 ^ 40 * 7715101 * 2
def baseEnd_7715101 : Nat := 3961555110983524365556403

theorem tailTrace_7715101 : CollatzResearch.WordTrace tailWord_7715101 prefixEnd_7715101 3961555110983524365556403 := by
  unfold tailWord_7715101
  simp only [CollatzResearch.WordTrace]
  refine ⟨281392850822514186193681157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187595233881676124129120771 281392850822514186193681157)
  ·
    refine ⟨52761159529221409911315217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281392850822514186193681157 52761159529221409911315217)
    ·
      refine ⟨39570869646916057433486413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52761159529221409911315217 39570869646916057433486413)
      ·
        refine ⟨14839076117593521537557405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39570869646916057433486413 14839076117593521537557405)
        ·
          refine ⟨5564653544097570576584027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14839076117593521537557405 5564653544097570576584027)
          ·
            refine ⟨8346980316146355864876041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564653544097570576584027 8346980316146355864876041)
            ·
              refine ⟨6260235237109766898657031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346980316146355864876041 6260235237109766898657031)
              ·
                refine ⟨9390352855664650347985547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260235237109766898657031 9390352855664650347985547)
                ·
                  refine ⟨14085529283496975521978321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390352855664650347985547 14085529283496975521978321)
                  ·
                    refine ⟨10564146962622731641483741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14085529283496975521978321 10564146962622731641483741)
                    ·
                      refine ⟨3961555110983524365556403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564146962622731641483741 3961555110983524365556403)
                      ·
                        rfl

theorem cell23_7715101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7715101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715101 prefixEnd_7715101 := by exact prefixLift 7715101
  have htrace : WordTrace (prefixWord ++ tailWord_7715101) baseStart_7715101 baseEnd_7715101 := by
    simpa [prefixWord, tailWord_7715101, baseEnd_7715101] using wordTrace_append hprefix tailTrace_7715101
  have hstable : (prefixWord ++ tailWord_7715101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715101).length < 2 ^ (prefixWord ++ tailWord_7715101).sum := by decide
  have hdescent : baseEnd_7715101 < baseStart_7715101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715173 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_7715173 : Nat := 118140960795 + 7715173 * 2 ^ 59
def prefixEnd_7715173 : Nat := 4983230072969 + 3 ^ 40 * 7715173 * 2
def baseEnd_7715173 : Nat := 1320530693863549361285357

theorem tailTrace_7715173 : CollatzResearch.WordTrace tailWord_7715173 prefixEnd_7715173 1320530693863549361285357 := by
  unfold tailWord_7715173
  simp only [CollatzResearch.WordTrace]
  refine ⟨281395476878253342490302173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187596984585502228326868115 281395476878253342490302173)
  ·
    refine ⟨105523303829345003433863315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281395476878253342490302173 105523303829345003433863315)
    ·
      refine ⟨158284955744017505150794973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105523303829345003433863315 158284955744017505150794973)
      ·
        refine ⟨59356858404006564431548115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158284955744017505150794973 59356858404006564431548115)
        ·
          refine ⟨89035287606009846647322173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59356858404006564431548115 89035287606009846647322173)
          ·
            refine ⟨33388232852253692492745815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89035287606009846647322173 33388232852253692492745815)
            ·
              refine ⟨50082349278380538739118723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33388232852253692492745815 50082349278380538739118723)
              ·
                refine ⟨75123523917570808108678085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50082349278380538739118723 75123523917570808108678085)
                ·
                  refine ⟨14085660734544526520377141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75123523917570808108678085 14085660734544526520377141)
                  ·
                    refine ⟨1320530693863549361285357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14085660734544526520377141 1320530693863549361285357)
                    ·
                      rfl

theorem cell23_7715173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_7715173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715173 prefixEnd_7715173 := by exact prefixLift 7715173
  have htrace : WordTrace (prefixWord ++ tailWord_7715173) baseStart_7715173 baseEnd_7715173 := by
    simpa [prefixWord, tailWord_7715173, baseEnd_7715173] using wordTrace_append hprefix tailTrace_7715173
  have hstable : (prefixWord ++ tailWord_7715173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715173).length < 2 ^ (prefixWord ++ tailWord_7715173).sum := by decide
  have hdescent : baseEnd_7715173 < baseStart_7715173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715193 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7715193 : Nat := 118140960795 + 7715193 * 2 ^ 59
def prefixEnd_7715193 : Nat := 4983230072969 + 3 ^ 40 * 7715193 * 2
def baseEnd_7715193 : Nat := 3961602351203738005605979

theorem tailTrace_7715193 : CollatzResearch.WordTrace tailWord_7715193 prefixEnd_7715193 3961602351203738005605979 := by
  unfold tailWord_7715193
  simp only [CollatzResearch.WordTrace]
  refine ⟨281396206338180885906030233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187597470892120590604020155 281396206338180885906030233)
  ·
    refine ⟨211047154753635664429522675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281396206338180885906030233 211047154753635664429522675)
    ·
      refine ⟨316570732130453496644284013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211047154753635664429522675 316570732130453496644284013)
      ·
        refine ⟨118714024548920061241606505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316570732130453496644284013 118714024548920061241606505)
        ·
          refine ⟨89035518411690045931204879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118714024548920061241606505 89035518411690045931204879)
          ·
            refine ⟨133553277617535068896807319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89035518411690045931204879 133553277617535068896807319)
            ·
              refine ⟨200329916426302603345210979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133553277617535068896807319 200329916426302603345210979)
              ·
                refine ⟨300494874639453905017816469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200329916426302603345210979 300494874639453905017816469)
                ·
                  refine ⟨14085697248724401797710147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300494874639453905017816469 14085697248724401797710147)
                  ·
                    refine ⟨21128545873086602696565221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14085697248724401797710147 21128545873086602696565221)
                    ·
                      refine ⟨3961602351203738005605979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21128545873086602696565221 3961602351203738005605979)
                      ·
                        rfl

theorem cell23_7715193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7715193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715193 prefixEnd_7715193 := by exact prefixLift 7715193
  have htrace : WordTrace (prefixWord ++ tailWord_7715193) baseStart_7715193 baseEnd_7715193 := by
    simpa [prefixWord, tailWord_7715193, baseEnd_7715193] using wordTrace_append hprefix tailTrace_7715193
  have hstable : (prefixWord ++ tailWord_7715193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715193).length < 2 ^ (prefixWord ++ tailWord_7715193).sum := by decide
  have hdescent : baseEnd_7715193 < baseStart_7715193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715237 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_7715237 : Nat := 118140960795 + 7715237 * 2 ^ 59
def prefixEnd_7715237 : Nat := 4983230072969 + 3 ^ 40 * 7715237 * 2
def baseEnd_7715237 : Nat := 1320541648117511944485259

theorem tailTrace_7715237 : CollatzResearch.WordTrace tailWord_7715237 prefixEnd_7715237 1320541648117511944485259 := by
  unfold tailWord_7715237
  simp only [CollatzResearch.WordTrace]
  refine ⟨281397811150021481420631965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187598540766680987613754643 281397811150021481420631965)
  ·
    refine ⟨105524179181258055532736987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281397811150021481420631965 105524179181258055532736987)
    ·
      refine ⟨158286268771887083299105481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105524179181258055532736987 158286268771887083299105481)
      ·
        refine ⟨118714701578915312474329111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158286268771887083299105481 118714701578915312474329111)
        ·
          refine ⟨178072052368372968711493667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118714701578915312474329111 178072052368372968711493667)
          ·
            refine ⟨267108078552559453067240501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178072052368372968711493667 267108078552559453067240501)
            ·
              refine ⟨25041382364302448725053797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267108078552559453067240501 25041382364302448725053797)
              ·
                refine ⟨4695259193306709135947587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25041382364302448725053797 4695259193306709135947587)
                ·
                  refine ⟨7042888789960063703921381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695259193306709135947587 7042888789960063703921381)
                  ·
                    refine ⟨1320541648117511944485259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7042888789960063703921381 1320541648117511944485259)
                    ·
                      rfl

theorem cell23_7715237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_7715237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715237 prefixEnd_7715237 := by exact prefixLift 7715237
  have htrace : WordTrace (prefixWord ++ tailWord_7715237) baseStart_7715237 baseEnd_7715237 := by
    simpa [prefixWord, tailWord_7715237, baseEnd_7715237] using wordTrace_append hprefix tailTrace_7715237
  have hstable : (prefixWord ++ tailWord_7715237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715237).length < 2 ^ (prefixWord ++ tailWord_7715237).sum := by decide
  have hdescent : baseEnd_7715237 < baseStart_7715237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715314 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_7715314 : Nat := 118140960795 + 7715314 * 2 ^ 59
def prefixEnd_7715314 : Nat := 4983230072969 + 3 ^ 40 * 7715314 * 2
def baseEnd_7715314 : Nat := 1320554827454310677397641

theorem tailTrace_7715314 : CollatzResearch.WordTrace tailWord_7715314 prefixEnd_7715314 1320554827454310677397641 := by
  unfold tailWord_7715314
  simp only [CollatzResearch.WordTrace]
  refine ⟨70350154892685630892796249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187600413047161682380789997 70350154892685630892796249)
  ·
    refine ⟨52762616169514223169597187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70350154892685630892796249 52762616169514223169597187)
    ·
      refine ⟨79143924254271334754395781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52762616169514223169597187 79143924254271334754395781)
      ·
        refine ⟨14839485797675875266449209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79143924254271334754395781 14839485797675875266449209)
        ·
          refine ⟨11129614348256906449836907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14839485797675875266449209 11129614348256906449836907)
          ·
            refine ⟨16694421522385359674755361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11129614348256906449836907 16694421522385359674755361)
            ·
              refine ⟨12520816141789019756066521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16694421522385359674755361 12520816141789019756066521)
              ·
                refine ⟨9390612106341764817049891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12520816141789019756066521 9390612106341764817049891)
                ·
                  refine ⟨14085918159512647225574837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390612106341764817049891 14085918159512647225574837)
                  ·
                    refine ⟨1320554827454310677397641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14085918159512647225574837 1320554827454310677397641)
                    ·
                      rfl

theorem cell23_7715314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_7715314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715314 prefixEnd_7715314 := by exact prefixLift 7715314
  have htrace : WordTrace (prefixWord ++ tailWord_7715314) baseStart_7715314 baseEnd_7715314 := by
    simpa [prefixWord, tailWord_7715314, baseEnd_7715314] using wordTrace_append hprefix tailTrace_7715314
  have hstable : (prefixWord ++ tailWord_7715314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715314).length < 2 ^ (prefixWord ++ tailWord_7715314).sum := by decide
  have hdescent : baseEnd_7715314 < baseStart_7715314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715340 : List Nat := [2, 2, 1, 2, 4, 3, 9]
def baseStart_7715340 : Nat := 118140960795 + 7715340 * 2 ^ 59
def prefixEnd_7715340 : Nat := 4983230072969 + 3 ^ 40 * 7715340 * 2
def baseEnd_7715340 : Nat := 48909602874814184326763

theorem tailTrace_7715340 : CollatzResearch.WordTrace tailWord_7715340 prefixEnd_7715340 48909602874814184326763 := by
  unfold tailWord_7715340
  simp only [CollatzResearch.WordTrace]
  refine ⟨140700783934324165005815737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187601045245765553341087649 140700783934324165005815737)
  ·
    refine ⟨105525587950743123754361803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140700783934324165005815737 105525587950743123754361803)
    ·
      refine ⟨158288381926114685631542705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105525587950743123754361803 158288381926114685631542705)
      ·
        refine ⟨118716286444586014223657029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158288381926114685631542705 118716286444586014223657029)
        ·
          refine ⟨22259303708359877666935693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118716286444586014223657029 22259303708359877666935693)
          ·
            refine ⟨8347238890634954125100885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22259303708359877666935693 8347238890634954125100885)
            ·
              refine ⟨48909602874814184326763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8347238890634954125100885 48909602874814184326763)
              ·
                rfl

theorem cell23_7715340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 9].length) (baseStart_7715340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715340 prefixEnd_7715340 := by exact prefixLift 7715340
  have htrace : WordTrace (prefixWord ++ tailWord_7715340) baseStart_7715340 baseEnd_7715340 := by
    simpa [prefixWord, tailWord_7715340, baseEnd_7715340] using wordTrace_append hprefix tailTrace_7715340
  have hstable : (prefixWord ++ tailWord_7715340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715340).length < 2 ^ (prefixWord ++ tailWord_7715340).sum := by decide
  have hdescent : baseEnd_7715340 < baseStart_7715340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715343 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_7715343 : Nat := 118140960795 + 7715343 * 2 ^ 59
def prefixEnd_7715343 : Nat := 4983230072969 + 3 ^ 40 * 7715343 * 2
def baseEnd_7715343 : Nat := 3961679373301912418730289

theorem tailTrace_7715343 : CollatzResearch.WordTrace tailWord_7715343 prefixEnd_7715343 3961679373301912418730289 := by
  unfold tailWord_7715343
  simp only [CollatzResearch.WordTrace]
  refine ⟨281401677287637461523990683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187601118191758307682660455 281401677287637461523990683)
  ·
    refine ⟨422102515931456192285986025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281401677287637461523990683 422102515931456192285986025)
    ·
      refine ⟨316576886948592144214489519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422102515931456192285986025 316576886948592144214489519)
      ·
        refine ⟨474865330422888216321734279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316576886948592144214489519 474865330422888216321734279)
        ·
          refine ⟨712297995634332324482601419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474865330422888216321734279 712297995634332324482601419)
          ·
            refine ⟨1068446993451498486723902129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712297995634332324482601419 1068446993451498486723902129)
            ·
              refine ⟨801335245088623865042926597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068446993451498486723902129 801335245088623865042926597)
              ·
                refine ⟨150250358454116974695548737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801335245088623865042926597 150250358454116974695548737)
                ·
                  refine ⟨112687768840587731021661553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150250358454116974695548737 112687768840587731021661553)
                  ·
                    refine ⟨84515826630440798266246165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112687768840587731021661553 84515826630440798266246165)
                    ·
                      refine ⟨3961679373301912418730289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84515826630440798266246165 3961679373301912418730289)
                      ·
                        rfl

theorem cell23_7715343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_7715343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715343 prefixEnd_7715343 := by exact prefixLift 7715343
  have htrace : WordTrace (prefixWord ++ tailWord_7715343) baseStart_7715343 baseEnd_7715343 := by
    simpa [prefixWord, tailWord_7715343, baseEnd_7715343] using wordTrace_append hprefix tailTrace_7715343
  have hstable : (prefixWord ++ tailWord_7715343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715343).length < 2 ^ (prefixWord ++ tailWord_7715343).sum := by decide
  have hdescent : baseEnd_7715343 < baseStart_7715343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715353 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_7715353 : Nat := 118140960795 + 7715353 * 2 ^ 59
def prefixEnd_7715353 : Nat := 4983230072969 + 3 ^ 40 * 7715353 * 2
def baseEnd_7715353 : Nat := 1320561502702819126535081

theorem tailTrace_7715353 : CollatzResearch.WordTrace tailWord_7715353 prefixEnd_7715353 1320561502702819126535081 := by
  unfold tailWord_7715353
  simp only [CollatzResearch.WordTrace]
  refine ⟨281402042017601233231854713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187601361345067488821236475 281402042017601233231854713)
  ·
    refine ⟨211051531513200924923891035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281402042017601233231854713 211051531513200924923891035)
    ·
      refine ⟨316577297269801387385836553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211051531513200924923891035 316577297269801387385836553)
      ·
        refine ⟨237432972952351040539377415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316577297269801387385836553 237432972952351040539377415)
        ·
          refine ⟨356149459428526560809066123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237432972952351040539377415 356149459428526560809066123)
          ·
            refine ⟨534224189142789841213599185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356149459428526560809066123 534224189142789841213599185)
            ·
              refine ⟨400668141857092380910199389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534224189142789841213599185 400668141857092380910199389)
              ·
                refine ⟨150250553196409642841324771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400668141857092380910199389 150250553196409642841324771)
                ·
                  refine ⟨225375829794614464261987157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150250553196409642841324771 225375829794614464261987157)
                  ·
                    refine ⟨1320561502702819126535081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 225375829794614464261987157 1320561502702819126535081)
                    ·
                      rfl

theorem cell23_7715353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_7715353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715353 prefixEnd_7715353 := by exact prefixLift 7715353
  have htrace : WordTrace (prefixWord ++ tailWord_7715353) baseStart_7715353 baseEnd_7715353 := by
    simpa [prefixWord, tailWord_7715353, baseEnd_7715353] using wordTrace_append hprefix tailTrace_7715353
  have hstable : (prefixWord ++ tailWord_7715353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715353).length < 2 ^ (prefixWord ++ tailWord_7715353).sum := by decide
  have hdescent : baseEnd_7715353 < baseStart_7715353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715445 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7715445 : Nat := 118140960795 + 7715445 * 2 ^ 59
def prefixEnd_7715445 : Nat := 4983230072969 + 3 ^ 40 * 7715445 * 2
def baseEnd_7715445 : Nat := 3961731748328671019654821

theorem tailTrace_7715445 : CollatzResearch.WordTrace tailWord_7715445 prefixEnd_7715445 3961731748328671019654821 := by
  unfold tailWord_7715445
  simp only [CollatzResearch.WordTrace]
  refine ⟨281405397533267932944203789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187603598355511955296135859 281405397533267932944203789)
  ·
    refine ⟨105527024074975474854076421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281405397533267932944203789 105527024074975474854076421)
    ·
      refine ⟨19786317014057901535139329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105527024074975474854076421 19786317014057901535139329)
      ·
        refine ⟨14839737760543426151354497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19786317014057901535139329 14839737760543426151354497)
        ·
          refine ⟨11129803320407569613515873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14839737760543426151354497 11129803320407569613515873)
          ·
            refine ⟨8347352490305677210136905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11129803320407569613515873 8347352490305677210136905)
            ·
              refine ⟨6260514367729257907602679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8347352490305677210136905 6260514367729257907602679)
              ·
                refine ⟨9390771551593886861404019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260514367729257907602679 9390771551593886861404019)
                ·
                  refine ⟨14086157327390830292106029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390771551593886861404019 14086157327390830292106029)
                  ·
                    refine ⟨5282308997771561359539761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14086157327390830292106029 5282308997771561359539761)
                    ·
                      refine ⟨3961731748328671019654821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282308997771561359539761 3961731748328671019654821)
                      ·
                        rfl

theorem cell23_7715445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7715445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715445 prefixEnd_7715445 := by exact prefixLift 7715445
  have htrace : WordTrace (prefixWord ++ tailWord_7715445) baseStart_7715445 baseEnd_7715445 := by
    simpa [prefixWord, tailWord_7715445, baseEnd_7715445] using wordTrace_append hprefix tailTrace_7715445
  have hstable : (prefixWord ++ tailWord_7715445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715445).length < 2 ^ (prefixWord ++ tailWord_7715445).sum := by decide
  have hdescent : baseEnd_7715445 < baseStart_7715445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715447 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 5]
def baseStart_7715447 : Nat := 118140960795 + 7715447 * 2 ^ 59
def prefixEnd_7715447 : Nat := 4983230072969 + 3 ^ 40 * 7715447 * 2
def baseEnd_7715447 : Nat := 440192530587775556869979

theorem tailTrace_7715447 : CollatzResearch.WordTrace tailWord_7715447 prefixEnd_7715447 440192530587775556869979 := by
  unfold tailWord_7715447
  simp only [CollatzResearch.WordTrace]
  refine ⟨281405470479260687285776595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187603646986173791523851063 281405470479260687285776595)
  ·
    refine ⟨422108205718891030928664893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281405470479260687285776595 422108205718891030928664893)
    ·
      refine ⟨158290577144584136598249335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422108205718891030928664893 158290577144584136598249335)
      ·
        refine ⟨237435865716876204897374003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158290577144584136598249335 237435865716876204897374003)
        ·
          refine ⟨356153798575314307346061005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237435865716876204897374003 356153798575314307346061005)
          ·
            refine ⟨133557674465742865254772877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356153798575314307346061005 133557674465742865254772877)
            ·
              refine ⟨50084127924653574470539829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133557674465742865254772877 50084127924653574470539829)
              ·
                refine ⟨4695386992936272606613109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50084127924653574470539829 4695386992936272606613109)
                ·
                  refine ⟨440192530587775556869979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4695386992936272606613109 440192530587775556869979)
                  ·
                    rfl

theorem cell23_7715447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 5].length) (baseStart_7715447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715447 prefixEnd_7715447 := by exact prefixLift 7715447
  have htrace : WordTrace (prefixWord ++ tailWord_7715447) baseStart_7715447 baseEnd_7715447 := by
    simpa [prefixWord, tailWord_7715447, baseEnd_7715447] using wordTrace_append hprefix tailTrace_7715447
  have hstable : (prefixWord ++ tailWord_7715447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715447).length < 2 ^ (prefixWord ++ tailWord_7715447).sum := by decide
  have hdescent : baseEnd_7715447 < baseStart_7715447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715457 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7715457 : Nat := 118140960795 + 7715457 * 2 ^ 59
def prefixEnd_7715457 : Nat := 4983230072969 + 3 ^ 40 * 7715457 * 2
def baseEnd_7715457 : Nat := 3961737910096524972704765

theorem tailTrace_7715457 : CollatzResearch.WordTrace tailWord_7715457 prefixEnd_7715457 3961737910096524972704765 := by
  unfold tailWord_7715457
  simp only [CollatzResearch.WordTrace]
  refine ⟨281405835209224458993640625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187603890139482972662427083 281405835209224458993640625)
  ·
    refine ⟨211054376406918344245230469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281405835209224458993640625 211054376406918344245230469)
    ·
      refine ⟨39572695576297189545980713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211054376406918344245230469 39572695576297189545980713)
      ·
        refine ⟨29679521682222892159485535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39572695576297189545980713 29679521682222892159485535)
        ·
          refine ⟨44519282523334338239228303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29679521682222892159485535 44519282523334338239228303)
          ·
            refine ⟨66778923785001507358842455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44519282523334338239228303 66778923785001507358842455)
            ·
              refine ⟨100168385677502261038263683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66778923785001507358842455 100168385677502261038263683)
              ·
                refine ⟨150252578516253391557395525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100168385677502261038263683 150252578516253391557395525)
                ·
                  refine ⟨28172358471797510917011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150252578516253391557395525 28172358471797510917011661)
                  ·
                    refine ⟨10564634426924066593879373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28172358471797510917011661 10564634426924066593879373)
                    ·
                      refine ⟨3961737910096524972704765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564634426924066593879373 3961737910096524972704765)
                      ·
                        rfl

theorem cell23_7715457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7715457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715457 prefixEnd_7715457 := by exact prefixLift 7715457
  have htrace : WordTrace (prefixWord ++ tailWord_7715457) baseStart_7715457 baseEnd_7715457 := by
    simpa [prefixWord, tailWord_7715457, baseEnd_7715457] using wordTrace_append hprefix tailTrace_7715457
  have hstable : (prefixWord ++ tailWord_7715457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715457).length < 2 ^ (prefixWord ++ tailWord_7715457).sum := by decide
  have hdescent : baseEnd_7715457 < baseStart_7715457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715467 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 5, 2]
def baseStart_7715467 : Nat := 118140960795 + 7715467 * 2 ^ 59
def prefixEnd_7715467 : Nat := 4983230072969 + 3 ^ 40 * 7715467 * 2
def baseEnd_7715467 : Nat := 3961743044903069933579719

theorem tailTrace_7715467 : CollatzResearch.WordTrace tailWord_7715467 prefixEnd_7715467 3961743044903069933579719 := by
  unfold tailWord_7715467
  simp only [CollatzResearch.WordTrace]
  refine ⟨281406199939188230701504655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187604133292792153801003103 281406199939188230701504655)
  ·
    refine ⟨422109299908782346052256983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281406199939188230701504655 422109299908782346052256983)
    ·
      refine ⟨633163949863173519078385475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422109299908782346052256983 633163949863173519078385475)
      ·
        refine ⟨949745924794760278617578213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633163949863173519078385475 949745924794760278617578213)
        ·
          refine ⟨178077360899017552240795915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 949745924794760278617578213 178077360899017552240795915)
          ·
            refine ⟨267116041348526328361193873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178077360899017552240795915 267116041348526328361193873)
            ·
              refine ⟨200337031011394746270895405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267116041348526328361193873 200337031011394746270895405)
              ·
                refine ⟨75126386629273029851585777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200337031011394746270895405 75126386629273029851585777)
                ·
                  refine ⟨56344789971954772388689333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75126386629273029851585777 56344789971954772388689333)
                  ·
                    refine ⟨5282324059870759911439625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56344789971954772388689333 5282324059870759911439625)
                    ·
                      refine ⟨3961743044903069933579719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282324059870759911439625 3961743044903069933579719)
                      ·
                        rfl

theorem cell23_7715467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5, 2].length) (baseStart_7715467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715467 prefixEnd_7715467 := by exact prefixLift 7715467
  have htrace : WordTrace (prefixWord ++ tailWord_7715467) baseStart_7715467 baseEnd_7715467 := by
    simpa [prefixWord, tailWord_7715467, baseEnd_7715467] using wordTrace_append hprefix tailTrace_7715467
  have hstable : (prefixWord ++ tailWord_7715467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715467).length < 2 ^ (prefixWord ++ tailWord_7715467).sum := by decide
  have hdescent : baseEnd_7715467 < baseStart_7715467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715474 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_7715474 : Nat := 118140960795 + 7715474 * 2 ^ 59
def prefixEnd_7715474 : Nat := 4983230072969 + 3 ^ 40 * 7715474 * 2
def baseEnd_7715474 : Nat := 3961746639267651406192187

theorem tailTrace_7715474 : CollatzResearch.WordTrace tailWord_7715474 prefixEnd_7715474 3961746639267651406192187 := by
  unfold tailWord_7715474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70351613812540717724252369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187604303500108580598006317 70351613812540717724252369)
  ·
    refine ⟨52763710359405538293189277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70351613812540717724252369 52763710359405538293189277)
    ·
      refine ⟨19786391384777076859945979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52763710359405538293189277 19786391384777076859945979)
      ·
        refine ⟨29679587077165615289918969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19786391384777076859945979 29679587077165615289918969)
        ·
          refine ⟨22259690307874211467439227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29679587077165615289918969 22259690307874211467439227)
          ·
            refine ⟨33389535461811317201158841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22259690307874211467439227 33389535461811317201158841)
            ·
              refine ⟨25042151596358487900869131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33389535461811317201158841 25042151596358487900869131)
              ·
                refine ⟨37563227394537731851303697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25042151596358487900869131 37563227394537731851303697)
                ·
                  refine ⟨28172420545903298888477773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37563227394537731851303697 28172420545903298888477773)
                  ·
                    refine ⟨10564657704713737083179165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28172420545903298888477773 10564657704713737083179165)
                    ·
                      refine ⟨3961746639267651406192187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564657704713737083179165 3961746639267651406192187)
                      ·
                        rfl

theorem cell23_7715474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_7715474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715474 prefixEnd_7715474 := by exact prefixLift 7715474
  have htrace : WordTrace (prefixWord ++ tailWord_7715474) baseStart_7715474 baseEnd_7715474 := by
    simpa [prefixWord, tailWord_7715474, baseEnd_7715474] using wordTrace_append hprefix tailTrace_7715474
  have hstable : (prefixWord ++ tailWord_7715474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715474).length < 2 ^ (prefixWord ++ tailWord_7715474).sum := by decide
  have hdescent : baseEnd_7715474 < baseStart_7715474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715497 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 6, 2]
def baseStart_7715497 : Nat := 118140960795 + 7715497 * 2 ^ 59
def prefixEnd_7715497 : Nat := 4983230072969 + 3 ^ 40 * 7715497 * 2
def baseEnd_7715497 : Nat := 3961758449322704816204581

theorem tailTrace_7715497 : CollatzResearch.WordTrace tailWord_7715497 prefixEnd_7715497 3961758449322704816204581 := by
  unfold tailWord_7715497
  simp only [CollatzResearch.WordTrace]
  refine ⟨281407294129079545825096745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187604862752719697216731163 281407294129079545825096745)
  ·
    refine ⟨211055470596809659368822559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281407294129079545825096745 211055470596809659368822559)
    ·
      refine ⟨316583205895214489053233839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211055470596809659368822559 316583205895214489053233839)
      ·
        refine ⟨474874808842821733579850759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316583205895214489053233839 474874808842821733579850759)
        ·
          refine ⟨712312213264232600369776139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474874808842821733579850759 712312213264232600369776139)
          ·
            refine ⟨1068468319896348900554664209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712312213264232600369776139 1068468319896348900554664209)
            ·
              refine ⟨801351239922261675415998157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068468319896348900554664209 801351239922261675415998157)
              ·
                refine ⟨300506714970848128280999309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801351239922261675415998157 300506714970848128280999309)
                ·
                  refine ⟨112690018114068048105374741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300506714970848128280999309 112690018114068048105374741)
                  ·
                    refine ⟨5282344599096939754939441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112690018114068048105374741 5282344599096939754939441)
                    ·
                      refine ⟨3961758449322704816204581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282344599096939754939441 3961758449322704816204581)
                      ·
                        rfl

theorem cell23_7715497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6, 2].length) (baseStart_7715497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715497 prefixEnd_7715497 := by exact prefixLift 7715497
  have htrace : WordTrace (prefixWord ++ tailWord_7715497) baseStart_7715497 baseEnd_7715497 := by
    simpa [prefixWord, tailWord_7715497, baseEnd_7715497] using wordTrace_append hprefix tailTrace_7715497
  have hstable : (prefixWord ++ tailWord_7715497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715497).length < 2 ^ (prefixWord ++ tailWord_7715497).sum := by decide
  have hdescent : baseEnd_7715497 < baseStart_7715497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715521 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7715521 : Nat := 118140960795 + 7715521 * 2 ^ 59
def prefixEnd_7715521 : Nat := 4983230072969 + 3 ^ 40 * 7715521 * 2
def baseEnd_7715521 : Nat := 3961770772858412722304471

theorem tailTrace_7715521 : CollatzResearch.WordTrace tailWord_7715521 prefixEnd_7715521 3961770772858412722304471 := by
  unfold tailWord_7715521
  simp only [CollatzResearch.WordTrace]
  refine ⟨281408169480992597923970417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187605446320661731949313611 281408169480992597923970417)
  ·
    refine ⟨211056127110744448442977813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281408169480992597923970417 211056127110744448442977813)
    ·
      refine ⟨9893255958316146020764585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211056127110744448442977813 9893255958316146020764585)
      ·
        refine ⟨7419941968737109515573439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9893255958316146020764585 7419941968737109515573439)
        ·
          refine ⟨11129912953105664273360159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7419941968737109515573439 11129912953105664273360159)
          ·
            refine ⟨16694869429658496410040239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11129912953105664273360159 16694869429658496410040239)
            ·
              refine ⟨25042304144487744615060359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16694869429658496410040239 25042304144487744615060359)
              ·
                refine ⟨37563456216731616922590539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25042304144487744615060359 37563456216731616922590539)
                ·
                  refine ⟨56345184325097425383885809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37563456216731616922590539 56345184325097425383885809)
                  ·
                    refine ⟨42258888243823069037914357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56345184325097425383885809 42258888243823069037914357)
                    ·
                      refine ⟨3961770772858412722304471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42258888243823069037914357 3961770772858412722304471)
                      ·
                        rfl

theorem cell23_7715521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7715521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715521 prefixEnd_7715521 := by exact prefixLift 7715521
  have htrace : WordTrace (prefixWord ++ tailWord_7715521) baseStart_7715521 baseEnd_7715521 := by
    simpa [prefixWord, tailWord_7715521, baseEnd_7715521] using wordTrace_append hprefix tailTrace_7715521
  have hstable : (prefixWord ++ tailWord_7715521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715521).length < 2 ^ (prefixWord ++ tailWord_7715521).sum := by decide
  have hdescent : baseEnd_7715521 < baseStart_7715521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715526 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7715526 : Nat := 118140960795 + 7715526 * 2 ^ 59
def prefixEnd_7715526 : Nat := 4983230072969 + 3 ^ 40 * 7715526 * 2
def baseEnd_7715526 : Nat := 3961773340261685202741949

theorem tailTrace_7715526 : CollatzResearch.WordTrace tailWord_7715526 prefixEnd_7715526 3961773340261685202741949 := by
  unfold tailWord_7715526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794010995186702618059451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187605567897316322518601621 8794010995186702618059451)
  ·
    refine ⟨13191016492780053927089177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794010995186702618059451 13191016492780053927089177)
    ·
      refine ⟨9893262369585040445316883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13191016492780053927089177 9893262369585040445316883)
      ·
        refine ⟨14839893554377560667975325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9893262369585040445316883 14839893554377560667975325)
        ·
          refine ⟨5564960082891585250490747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14839893554377560667975325 5564960082891585250490747)
          ·
            refine ⟨8347440124337377875736121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564960082891585250490747 8347440124337377875736121)
            ·
              refine ⟨6260580093253033406802091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8347440124337377875736121 6260580093253033406802091)
              ·
                refine ⟨9390870139879550110203137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260580093253033406802091 9390870139879550110203137)
                ·
                  refine ⟨7043152604909662582652353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390870139879550110203137 7043152604909662582652353)
                  ·
                    refine ⟨5282364453682246936989265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043152604909662582652353 5282364453682246936989265)
                    ·
                      refine ⟨3961773340261685202741949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282364453682246936989265 3961773340261685202741949)
                      ·
                        rfl

theorem cell23_7715526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7715526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715526 prefixEnd_7715526 := by exact prefixLift 7715526
  have htrace : WordTrace (prefixWord ++ tailWord_7715526) baseStart_7715526 baseEnd_7715526 := by
    simpa [prefixWord, tailWord_7715526, baseEnd_7715526] using wordTrace_append hprefix tailTrace_7715526
  have hstable : (prefixWord ++ tailWord_7715526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715526).length < 2 ^ (prefixWord ++ tailWord_7715526).sum := by decide
  have hdescent : baseEnd_7715526 < baseStart_7715526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715537 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 6]
def baseStart_7715537 : Nat := 118140960795 + 7715537 * 2 ^ 59
def prefixEnd_7715537 : Nat := 4983230072969 + 3 ^ 40 * 7715537 * 2
def baseEnd_7715537 : Nat := 440197665394320517744933

theorem tailTrace_7715537 : CollatzResearch.WordTrace tailWord_7715537 prefixEnd_7715537 440197665394320517744933 := by
  unfold tailWord_7715537
  simp only [CollatzResearch.WordTrace]
  refine ⟨281408753048934632656552865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187605835365956421771035243 281408753048934632656552865)
  ·
    refine ⟨211056564786700974492414649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281408753048934632656552865 211056564786700974492414649)
    ·
      refine ⟨158292423590025730869310987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211056564786700974492414649 158292423590025730869310987)
      ·
        refine ⟨237438635385038596303966481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158292423590025730869310987 237438635385038596303966481)
        ·
          refine ⟨178078976538778947227974861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237438635385038596303966481 178078976538778947227974861)
          ·
            refine ⟨66779616202042105210490573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178078976538778947227974861 66779616202042105210490573)
            ·
              refine ⟨25042356075765789453933965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66779616202042105210490573 25042356075765789453933965)
              ·
                refine ⟨9390883528412171045225237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25042356075765789453933965 9390883528412171045225237)
                ·
                  refine ⟨440197665394320517744933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9390883528412171045225237 440197665394320517744933)
                  ·
                    rfl

theorem cell23_7715537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_7715537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715537 prefixEnd_7715537 := by exact prefixLift 7715537
  have htrace : WordTrace (prefixWord ++ tailWord_7715537) baseStart_7715537 baseEnd_7715537 := by
    simpa [prefixWord, tailWord_7715537, baseEnd_7715537] using wordTrace_append hprefix tailTrace_7715537
  have hstable : (prefixWord ++ tailWord_7715537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715537).length < 2 ^ (prefixWord ++ tailWord_7715537).sum := by decide
  have hdescent : baseEnd_7715537 < baseStart_7715537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715618 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7715618 : Nat := 118140960795 + 7715618 * 2 ^ 59
def prefixEnd_7715618 : Nat := 4983230072969 + 3 ^ 40 * 7715618 * 2
def baseEnd_7715618 : Nat := 1320606860160632947597175

theorem tailTrace_7715618 : CollatzResearch.WordTrace tailWord_7715618 prefixEnd_7715618 1320606860160632947597175 := by
  unfold tailWord_7715618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70352926840410295872562877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187607804907760788993501005 70352926840410295872562877)
  ·
    refine ⟨26382347565153860952211079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70352926840410295872562877 26382347565153860952211079)
    ·
      refine ⟨39573521347730791428316619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26382347565153860952211079 39573521347730791428316619)
      ·
        refine ⟨59360282021596187142474929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39573521347730791428316619 59360282021596187142474929)
        ·
          refine ⟨44520211516197140356856197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59360282021596187142474929 44520211516197140356856197)
          ·
            refine ⟨8347539659286963816910537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44520211516197140356856197 8347539659286963816910537)
            ·
              refine ⟨6260654744465222862682903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8347539659286963816910537 6260654744465222862682903)
              ·
                refine ⟨9390982116697834294024355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260654744465222862682903 9390982116697834294024355)
                ·
                  refine ⟨14086473175046751441036533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9390982116697834294024355 14086473175046751441036533)
                  ·
                    refine ⟨1320606860160632947597175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14086473175046751441036533 1320606860160632947597175)
                    ·
                      rfl

theorem cell23_7715618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7715618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715618 prefixEnd_7715618 := by exact prefixLift 7715618
  have htrace : WordTrace (prefixWord ++ tailWord_7715618) baseStart_7715618 baseEnd_7715618 := by
    simpa [prefixWord, tailWord_7715618, baseEnd_7715618] using wordTrace_append hprefix tailTrace_7715618
  have hstable : (prefixWord ++ tailWord_7715618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715618).length < 2 ^ (prefixWord ++ tailWord_7715618).sum := by decide
  have hdescent : baseEnd_7715618 < baseStart_7715618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715621 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_7715621 : Nat := 118140960795 + 7715621 * 2 ^ 59
def prefixEnd_7715621 : Nat := 4983230072969 + 3 ^ 40 * 7715621 * 2
def baseEnd_7715621 : Nat := 3961822120923862331054011

theorem tailTrace_7715621 : CollatzResearch.WordTrace tailWord_7715621 prefixEnd_7715621 3961822120923862331054011 := by
  unfold tailWord_7715621
  simp only [CollatzResearch.WordTrace]
  refine ⟨281411816780630315002610717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187607877853753543335073811 281411816780630315002610717)
  ·
    refine ⟨105529431292736368125979019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281411816780630315002610717 105529431292736368125979019)
    ·
      refine ⟨158294146939104552188968529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105529431292736368125979019 158294146939104552188968529)
      ·
        refine ⟨118720610204328414141726397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158294146939104552188968529 118720610204328414141726397)
        ·
          refine ⟨44520228826623155303147399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118720610204328414141726397 44520228826623155303147399)
          ·
            refine ⟨66780343239934732954721099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44520228826623155303147399 66780343239934732954721099)
            ·
              refine ⟨100170514859902099432081649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66780343239934732954721099 100170514859902099432081649)
              ·
                refine ⟨75127886144926574574061237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100170514859902099432081649 75127886144926574574061237)
                ·
                  refine ⟨7043239326086866366318241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75127886144926574574061237 7043239326086866366318241)
                  ·
                    refine ⟨5282429494565149774738681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043239326086866366318241 5282429494565149774738681)
                    ·
                      refine ⟨3961822120923862331054011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282429494565149774738681 3961822120923862331054011)
                      ·
                        rfl

theorem cell23_7715621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_7715621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715621 prefixEnd_7715621 := by exact prefixLift 7715621
  have htrace : WordTrace (prefixWord ++ tailWord_7715621) baseStart_7715621 baseEnd_7715621 := by
    simpa [prefixWord, tailWord_7715621, baseEnd_7715621] using wordTrace_append hprefix tailTrace_7715621
  have hstable : (prefixWord ++ tailWord_7715621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715621).length < 2 ^ (prefixWord ++ tailWord_7715621).sum := by decide
  have hdescent : baseEnd_7715621 < baseStart_7715621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715624 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7715624 : Nat := 118140960795 + 7715624 * 2 ^ 59
def prefixEnd_7715624 : Nat := 4983230072969 + 3 ^ 40 * 7715624 * 2
def baseEnd_7715624 : Nat := 3961823661365825819316497

theorem tailTrace_7715624 : CollatzResearch.WordTrace tailWord_7715624 prefixEnd_7715624 3961823661365825819316497 := by
  unfold tailWord_7715624
  simp only [CollatzResearch.WordTrace]
  refine ⟨140705963099809723257484963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187607950799746297676646617 140705963099809723257484963)
  ·
    refine ⟨211058944649714584886227445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140705963099809723257484963 211058944649714584886227445)
    ·
      refine ⟨19786776060910742333083823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211058944649714584886227445 19786776060910742333083823)
      ·
        refine ⟨29680164091366113499625735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19786776060910742333083823 29680164091366113499625735)
        ·
          refine ⟨44520246137049170249438603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29680164091366113499625735 44520246137049170249438603)
          ·
            refine ⟨66780369205573755374157905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44520246137049170249438603 66780369205573755374157905)
            ·
              refine ⟨50085276904180316530618429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66780369205573755374157905 50085276904180316530618429)
              ·
                refine ⟨18781978839067618698981911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50085276904180316530618429 18781978839067618698981911)
                ·
                  refine ⟨28172968258601428048472867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18781978839067618698981911 28172968258601428048472867)
                  ·
                    refine ⟨42259452387902142072709301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28172968258601428048472867 42259452387902142072709301)
                    ·
                      refine ⟨3961823661365825819316497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42259452387902142072709301 3961823661365825819316497)
                      ·
                        rfl

theorem cell23_7715624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7715624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715624 prefixEnd_7715624 := by exact prefixLift 7715624
  have htrace : WordTrace (prefixWord ++ tailWord_7715624) baseStart_7715624 baseEnd_7715624 := by
    simpa [prefixWord, tailWord_7715624, baseEnd_7715624] using wordTrace_append hprefix tailTrace_7715624
  have hstable : (prefixWord ++ tailWord_7715624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715624).length < 2 ^ (prefixWord ++ tailWord_7715624).sum := by decide
  have hdescent : baseEnd_7715624 < baseStart_7715624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715661 : List Nat := [1, 6, 1, 2, 2, 1, 1, 9]
def baseStart_7715661 : Nat := 118140960795 + 7715661 * 2 ^ 59
def prefixEnd_7715661 : Nat := 4983230072969 + 3 ^ 40 * 7715661 * 2
def baseEnd_7715661 : Nat := 146734913338890450909401

theorem tailTrace_7715661 : CollatzResearch.WordTrace tailWord_7715661 prefixEnd_7715661 146734913338890450909401 := by
  unfold tailWord_7715661
  simp only [CollatzResearch.WordTrace]
  refine ⟨281413275700485401834066837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187608850466990267889377891 281413275700485401834066837)
  ·
    refine ⟨13191247298460253210971883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281413275700485401834066837 13191247298460253210971883)
    ·
      refine ⟨19786870947690379816457825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191247298460253210971883 19786870947690379816457825)
      ·
        refine ⟨14840153210767784862343369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19786870947690379816457825 14840153210767784862343369)
        ·
          refine ⟨11130114908075838646757527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14840153210767784862343369 11130114908075838646757527)
          ·
            refine ⟨16695172362113757970136291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130114908075838646757527 16695172362113757970136291)
            ·
              refine ⟨25042758543170636955204437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695172362113757970136291 25042758543170636955204437)
              ·
                refine ⟨146734913338890450909401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25042758543170636955204437 146734913338890450909401)
                ·
                  rfl

theorem cell23_7715661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 9].length) (baseStart_7715661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715661 prefixEnd_7715661 := by exact prefixLift 7715661
  have htrace : WordTrace (prefixWord ++ tailWord_7715661) baseStart_7715661 baseEnd_7715661 := by
    simpa [prefixWord, tailWord_7715661, baseEnd_7715661] using wordTrace_append hprefix tailTrace_7715661
  have hstable : (prefixWord ++ tailWord_7715661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715661).length < 2 ^ (prefixWord ++ tailWord_7715661).sum := by decide
  have hdescent : baseEnd_7715661 < baseStart_7715661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715671 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_7715671 : Nat := 118140960795 + 7715671 * 2 ^ 59
def prefixEnd_7715671 : Nat := 4983230072969 + 3 ^ 40 * 7715671 * 2
def baseEnd_7715671 : Nat := 3961847794956587135428781

theorem tailTrace_7715671 : CollatzResearch.WordTrace tailWord_7715671 prefixEnd_7715671 3961847794956587135428781 := by
  unfold tailWord_7715671
  simp only [CollatzResearch.WordTrace]
  refine ⟨281413640430449173541930867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187609093620299449027953911 281413640430449173541930867)
  ·
    refine ⟨422120460645673760312896301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281413640430449173541930867 422120460645673760312896301)
    ·
      refine ⟨158295172742127660117336113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422120460645673760312896301 158295172742127660117336113)
      ·
        refine ⟨118721379556595745088002085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158295172742127660117336113 118721379556595745088002085)
        ·
          refine ⟨22260258666861702204000391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118721379556595745088002085 22260258666861702204000391)
          ·
            refine ⟨33390388000292553306000587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22260258666861702204000391 33390388000292553306000587)
            ·
              refine ⟨50085582000438829959000881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33390388000292553306000587 50085582000438829959000881)
              ·
                refine ⟨37564186500329122469250661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50085582000438829959000881 37564186500329122469250661)
                ·
                  refine ⟨7043284968811710462984499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37564186500329122469250661 7043284968811710462984499)
                  ·
                    refine ⟨10564927453217565694476749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7043284968811710462984499 10564927453217565694476749)
                    ·
                      refine ⟨3961847794956587135428781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564927453217565694476749 3961847794956587135428781)
                      ·
                        rfl

theorem cell23_7715671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_7715671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715671 prefixEnd_7715671 := by exact prefixLift 7715671
  have htrace : WordTrace (prefixWord ++ tailWord_7715671) baseStart_7715671 baseEnd_7715671 := by
    simpa [prefixWord, tailWord_7715671, baseEnd_7715671] using wordTrace_append hprefix tailTrace_7715671
  have hstable : (prefixWord ++ tailWord_7715671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715671).length < 2 ^ (prefixWord ++ tailWord_7715671).sum := by decide
  have hdescent : baseEnd_7715671 < baseStart_7715671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715705 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 2, 1, 3]
def baseStart_7715705 : Nat := 118140960795 + 7715705 * 2 ^ 59
def prefixEnd_7715705 : Nat := 4983230072969 + 3 ^ 40 * 7715705 * 2
def baseEnd_7715705 : Nat := 3961865253298840002403625

theorem tailTrace_7715705 : CollatzResearch.WordTrace tailWord_7715705 prefixEnd_7715705 3961865253298840002403625 := by
  unfold tailWord_7715705
  simp only [CollatzResearch.WordTrace]
  refine ⟨281414880512325997348668569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187609920341550664899112379 281414880512325997348668569)
  ·
    refine ⟨211061160384244498011501427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281414880512325997348668569 211061160384244498011501427)
    ·
      refine ⟨316591740576366747017252141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211061160384244498011501427 316591740576366747017252141)
      ·
        refine ⟨118721902716137530131469553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316591740576366747017252141 118721902716137530131469553)
        ·
          refine ⟨89041427037103147598602165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118721902716137530131469553 89041427037103147598602165)
          ·
            refine ⟨8347633784728420087368953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89041427037103147598602165 8347633784728420087368953)
            ·
              refine ⟨6260725338546315065526715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8347633784728420087368953 6260725338546315065526715)
              ·
                refine ⟨9391088007819472598290073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260725338546315065526715 9391088007819472598290073)
                ·
                  refine ⟨7043316005864604448717555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9391088007819472598290073 7043316005864604448717555)
                  ·
                    refine ⟨10564974008796906673076333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7043316005864604448717555 10564974008796906673076333)
                    ·
                      refine ⟨3961865253298840002403625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10564974008796906673076333 3961865253298840002403625)
                      ·
                        rfl

theorem cell23_7715705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_7715705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715705 prefixEnd_7715705 := by exact prefixLift 7715705
  have htrace : WordTrace (prefixWord ++ tailWord_7715705) baseStart_7715705 baseEnd_7715705 := by
    simpa [prefixWord, tailWord_7715705, baseEnd_7715705] using wordTrace_append hprefix tailTrace_7715705
  have hstable : (prefixWord ++ tailWord_7715705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715705).length < 2 ^ (prefixWord ++ tailWord_7715705).sum := by decide
  have hdescent : baseEnd_7715705 < baseStart_7715705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715745 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7715745 : Nat := 118140960795 + 7715745 * 2 ^ 59
def prefixEnd_7715745 : Nat := 4983230072969 + 3 ^ 40 * 7715745 * 2
def baseEnd_7715745 : Nat := 3961885792525019845903441

theorem tailTrace_7715745 : CollatzResearch.WordTrace tailWord_7715745 prefixEnd_7715745 3961885792525019845903441 := by
  unfold tailWord_7715745
  simp only [CollatzResearch.WordTrace]
  refine ⟨281416339432181084180124689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187610892954787389453416459 281416339432181084180124689)
  ·
    refine ⟨211062254574135813135093517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281416339432181084180124689 211062254574135813135093517)
    ·
      refine ⟨79148345465300929925660069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211062254574135813135093517 79148345465300929925660069)
      ·
        refine ⟨14840314774743924361061263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79148345465300929925660069 14840314774743924361061263)
        ·
          refine ⟨22260472162115886541591895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14840314774743924361061263 22260472162115886541591895)
          ·
            refine ⟨33390708243173829812387843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22260472162115886541591895 33390708243173829812387843)
            ·
              refine ⟨50086062364760744718581765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33390708243173829812387843 50086062364760744718581765)
              ·
                refine ⟨9391136693392639634734081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50086062364760744718581765 9391136693392639634734081)
                ·
                  refine ⟨7043352520044479726050561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9391136693392639634734081 7043352520044479726050561)
                  ·
                    refine ⟨5282514390033359794537921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043352520044479726050561 5282514390033359794537921)
                    ·
                      refine ⟨3961885792525019845903441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282514390033359794537921 3961885792525019845903441)
                      ·
                        rfl

theorem cell23_7715745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7715745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715745 prefixEnd_7715745 := by exact prefixLift 7715745
  have htrace : WordTrace (prefixWord ++ tailWord_7715745) baseStart_7715745 baseEnd_7715745 := by
    simpa [prefixWord, tailWord_7715745, baseEnd_7715745] using wordTrace_append hprefix tailTrace_7715745
  have hstable : (prefixWord ++ tailWord_7715745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715745).length < 2 ^ (prefixWord ++ tailWord_7715745).sum := by decide
  have hdescent : baseEnd_7715745 < baseStart_7715745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715818 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_7715818 : Nat := 118140960795 + 7715818 * 2 ^ 59
def prefixEnd_7715818 : Nat := 4983230072969 + 3 ^ 40 * 7715818 * 2
def baseEnd_7715818 : Nat := 3961923276612798060290605

theorem tailTrace_7715818 : CollatzResearch.WordTrace tailWord_7715818 prefixEnd_7715818 3961923276612798060290605 := by
  unfold tailWord_7715818
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354750490229154411883027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187612667973944411765021405 70354750490229154411883027)
  ·
    refine ⟨105532125735343731617824541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70354750490229154411883027 105532125735343731617824541)
    ·
      refine ⟨39574547150753899356684203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105532125735343731617824541 39574547150753899356684203)
      ·
        refine ⟨59361820726130849035026305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39574547150753899356684203 59361820726130849035026305)
        ·
          refine ⟨44521365544598136776269729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59361820726130849035026305 44521365544598136776269729)
          ·
            refine ⟨33391024158448602582202297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44521365544598136776269729 33391024158448602582202297)
            ·
              refine ⟨25043268118836451936651723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33391024158448602582202297 25043268118836451936651723)
              ·
                refine ⟨37564902178254677904977585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25043268118836451936651723 37564902178254677904977585)
                ·
                  refine ⟨28173676633691008428733189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37564902178254677904977585 28173676633691008428733189)
                  ·
                    refine ⟨5282564368817064080387473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28173676633691008428733189 5282564368817064080387473)
                    ·
                      refine ⟨3961923276612798060290605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282564368817064080387473 3961923276612798060290605)
                      ·
                        rfl

theorem cell23_7715818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_7715818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715818 prefixEnd_7715818 := by exact prefixLift 7715818
  have htrace : WordTrace (prefixWord ++ tailWord_7715818) baseStart_7715818 baseEnd_7715818 := by
    simpa [prefixWord, tailWord_7715818, baseEnd_7715818] using wordTrace_append hprefix tailTrace_7715818
  have hstable : (prefixWord ++ tailWord_7715818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715818).length < 2 ^ (prefixWord ++ tailWord_7715818).sum := by decide
  have hdescent : baseEnd_7715818 < baseStart_7715818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715901 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_7715901 : Nat := 118140960795 + 7715901 * 2 ^ 59
def prefixEnd_7715901 : Nat := 4983230072969 + 3 ^ 40 * 7715901 * 2
def baseEnd_7715901 : Nat := 1320655298502373745184241

theorem tailTrace_7715901 : CollatzResearch.WordTrace tailWord_7715901 prefixEnd_7715901 1320655298502373745184241 := by
  unfold tailWord_7715901
  simp only [CollatzResearch.WordTrace]
  refine ⟨281422029219615922822803557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187614686146410615215202371 281422029219615922822803557)
  ·
    refine ⟨52766630478677985529275667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281422029219615922822803557 52766630478677985529275667)
    ·
      refine ⟨79149945718016978293913501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52766630478677985529275667 79149945718016978293913501)
      ·
        refine ⟨29681229644256366860217563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79149945718016978293913501 29681229644256366860217563)
        ·
          refine ⟨44521844466384550290326345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29681229644256366860217563 44521844466384550290326345)
          ·
            refine ⟨33391383349788412717744759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44521844466384550290326345 33391383349788412717744759)
            ·
              refine ⟨50087075024682619076617139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33391383349788412717744759 50087075024682619076617139)
              ·
                refine ⟨75130612537023928614925709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50087075024682619076617139 75130612537023928614925709)
                ·
                  refine ⟨28173979701383973230597141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75130612537023928614925709 28173979701383973230597141)
                  ·
                    refine ⟨1320655298502373745184241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28173979701383973230597141 1320655298502373745184241)
                    ·
                      rfl

theorem cell23_7715901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_7715901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715901 prefixEnd_7715901 := by exact prefixLift 7715901
  have htrace : WordTrace (prefixWord ++ tailWord_7715901) baseStart_7715901 baseEnd_7715901 := by
    simpa [prefixWord, tailWord_7715901, baseEnd_7715901] using wordTrace_append hprefix tailTrace_7715901
  have hstable : (prefixWord ++ tailWord_7715901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715901).length < 2 ^ (prefixWord ++ tailWord_7715901).sum := by decide
  have hdescent : baseEnd_7715901 < baseStart_7715901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7715925 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7715925 : Nat := 118140960795 + 7715925 * 2 ^ 59
def prefixEnd_7715925 : Nat := 4983230072969 + 3 ^ 40 * 7715925 * 2
def baseEnd_7715925 : Nat := 3961978219042829141652613

theorem tailTrace_7715925 : CollatzResearch.WordTrace tailWord_7715925 prefixEnd_7715925 3961978219042829141652613 := by
  unfold tailWord_7715925
  simp only [CollatzResearch.WordTrace]
  refine ⟨281422904571528974921677229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187615269714352649947784819 281422904571528974921677229)
  ·
    refine ⟨105533589214323365595628961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281422904571528974921677229 105533589214323365595628961)
    ·
      refine ⟨79150191910742524196721721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105533589214323365595628961 79150191910742524196721721)
      ·
        refine ⟨59362643933056893147541291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79150191910742524196721721 59362643933056893147541291)
        ·
          refine ⟨89043965899585339721311937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59362643933056893147541291 89043965899585339721311937)
          ·
            refine ⟨66782974424689004790983953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89043965899585339721311937 66782974424689004790983953)
            ·
              refine ⟨50087230818516753593237965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66782974424689004790983953 50087230818516753593237965)
              ·
                refine ⟨18782711556943782597464237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50087230818516753593237965 18782711556943782597464237)
                ·
                  refine ⟨7043516833853918474049089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18782711556943782597464237 7043516833853918474049089)
                  ·
                    refine ⟨5282637625390438855536817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043516833853918474049089 5282637625390438855536817)
                    ·
                      refine ⟨3961978219042829141652613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282637625390438855536817 3961978219042829141652613)
                      ·
                        rfl

theorem cell23_7715925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7715925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7715925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7715925 prefixEnd_7715925 := by exact prefixLift 7715925
  have htrace : WordTrace (prefixWord ++ tailWord_7715925) baseStart_7715925 baseEnd_7715925 := by
    simpa [prefixWord, tailWord_7715925, baseEnd_7715925] using wordTrace_append hprefix tailTrace_7715925
  have hstable : (prefixWord ++ tailWord_7715925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7715925).length < 2 ^ (prefixWord ++ tailWord_7715925).sum := by decide
  have hdescent : baseEnd_7715925 < baseStart_7715925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7715925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716015 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 4, 2, 2]
def baseStart_7716015 : Nat := 118140960795 + 7716015 * 2 ^ 59
def prefixEnd_7716015 : Nat := 4983230072969 + 3 ^ 40 * 7716015 * 2
def baseEnd_7716015 : Nat := 3962024432301733789527199

theorem tailTrace_7716015 : CollatzResearch.WordTrace tailWord_7716015 prefixEnd_7716015 3962024432301733789527199 := by
  unfold tailWord_7716015
  simp only [CollatzResearch.WordTrace]
  refine ⟨281426187141202920292453499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187617458094135280194968999 281426187141202920292453499)
  ·
    refine ⟨422139280711804380438680249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281426187141202920292453499 422139280711804380438680249)
    ·
      refine ⟨316604460533853285329010187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422139280711804380438680249 316604460533853285329010187)
      ·
        refine ⟨474906690800779927993515281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316604460533853285329010187 474906690800779927993515281)
        ·
          refine ⟨356180018100584945995136461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474906690800779927993515281 356180018100584945995136461)
          ·
            refine ⟨133567506787719354748176173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356180018100584945995136461 133567506787719354748176173)
            ·
              refine ⟨50087815045394758030566065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133567506787719354748176173 50087815045394758030566065)
              ·
                refine ⟨37565861284046068522924549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50087815045394758030566065 37565861284046068522924549)
                ·
                  refine ⟨7043598990758637848048353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37565861284046068522924549 7043598990758637848048353)
                  ·
                    refine ⟨5282699243068978386036265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043598990758637848048353 5282699243068978386036265)
                    ·
                      refine ⟨3962024432301733789527199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282699243068978386036265 3962024432301733789527199)
                      ·
                        rfl

theorem cell23_7716015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2, 2].length) (baseStart_7716015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716015 prefixEnd_7716015 := by exact prefixLift 7716015
  have htrace : WordTrace (prefixWord ++ tailWord_7716015) baseStart_7716015 baseEnd_7716015 := by
    simpa [prefixWord, tailWord_7716015, baseEnd_7716015] using wordTrace_append hprefix tailTrace_7716015
  have hstable : (prefixWord ++ tailWord_7716015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716015).length < 2 ^ (prefixWord ++ tailWord_7716015).sum := by decide
  have hdescent : baseEnd_7716015 < baseStart_7716015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716018 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_7716018 : Nat := 118140960795 + 7716018 * 2 ^ 59
def prefixEnd_7716018 : Nat := 4983230072969 + 3 ^ 40 * 7716018 * 2
def baseEnd_7716018 : Nat := 3962025972743697277789685

theorem tailTrace_7716018 : CollatzResearch.WordTrace tailWord_7716018 prefixEnd_7716018 3962025972743697277789685 := by
  unfold tailWord_7716018
  simp only [CollatzResearch.WordTrace]
  refine ⟨70356574140048012951203177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187617531040128034536541805 70356574140048012951203177)
  ·
    refine ⟨52767430605036009713402383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70356574140048012951203177 52767430605036009713402383)
    ·
      refine ⟨79151145907554014570103575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52767430605036009713402383 79151145907554014570103575)
      ·
        refine ⟨118726718861331021855155363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79151145907554014570103575 118726718861331021855155363)
        ·
          refine ⟨178090078291996532782733045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118726718861331021855155363 178090078291996532782733045)
          ·
            refine ⟨16695944839874674948381223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178090078291996532782733045 16695944839874674948381223)
            ·
              refine ⟨25043917259812012422571835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695944839874674948381223 25043917259812012422571835)
              ·
                refine ⟨37565875889718018633857753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25043917259812012422571835 37565875889718018633857753)
                ·
                  refine ⟨28174406917288513975393315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37565875889718018633857753 28174406917288513975393315)
                  ·
                    refine ⟨42261610375932770963089973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28174406917288513975393315 42261610375932770963089973)
                    ·
                      refine ⟨3962025972743697277789685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42261610375932770963089973 3962025972743697277789685)
                      ·
                        rfl

theorem cell23_7716018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_7716018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716018 prefixEnd_7716018 := by exact prefixLift 7716018
  have htrace : WordTrace (prefixWord ++ tailWord_7716018) baseStart_7716018 baseEnd_7716018 := by
    simpa [prefixWord, tailWord_7716018, baseEnd_7716018] using wordTrace_append hprefix tailTrace_7716018
  have hstable : (prefixWord ++ tailWord_7716018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716018).length < 2 ^ (prefixWord ++ tailWord_7716018).sum := by decide
  have hdescent : baseEnd_7716018 < baseStart_7716018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716068 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_7716068 : Nat := 118140960795 + 7716068 * 2 ^ 59
def prefixEnd_7716068 : Nat := 4983230072969 + 3 ^ 40 * 7716068 * 2
def baseEnd_7716068 : Nat := 1320683882258807360721485

theorem tailTrace_7716068 : CollatzResearch.WordTrace tailWord_7716068 prefixEnd_7716068 1320683882258807360721485 := by
  unfold tailWord_7716068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140714060105005455172066429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187618746806673940229421905 140714060105005455172066429)
  ·
    refine ⟨52767772539377045689524911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140714060105005455172066429 52767772539377045689524911)
    ·
      refine ⟨79151658809065568534287367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52767772539377045689524911 79151658809065568534287367)
      ·
        refine ⟨118727488213598352801431051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79151658809065568534287367 118727488213598352801431051)
        ·
          refine ⟨178091232320397529202146577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118727488213598352801431051 178091232320397529202146577)
          ·
            refine ⟨133568424240298146901609933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178091232320397529202146577 133568424240298146901609933)
            ·
              refine ⟨50088159090111805088103725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133568424240298146901609933 50088159090111805088103725)
              ·
                refine ⟨18783059658791926908038897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50088159090111805088103725 18783059658791926908038897)
                ·
                  refine ⟨14087294744093945181029173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18783059658791926908038897 14087294744093945181029173)
                  ·
                    refine ⟨1320683882258807360721485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087294744093945181029173 1320683882258807360721485)
                    ·
                      rfl

theorem cell23_7716068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_7716068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716068 prefixEnd_7716068 := by exact prefixLift 7716068
  have htrace : WordTrace (prefixWord ++ tailWord_7716068) baseStart_7716068 baseEnd_7716068 := by
    simpa [prefixWord, tailWord_7716068, baseEnd_7716068] using wordTrace_append hprefix tailTrace_7716068
  have hstable : (prefixWord ++ tailWord_7716068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716068).length < 2 ^ (prefixWord ++ tailWord_7716068).sum := by decide
  have hdescent : baseEnd_7716068 < baseStart_7716068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716078 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7716078 : Nat := 118140960795 + 7716078 * 2 ^ 59
def prefixEnd_7716078 : Nat := 4983230072969 + 3 ^ 40 * 7716078 * 2
def baseEnd_7716078 : Nat := 3962056781582967043039409

theorem tailTrace_7716078 : CollatzResearch.WordTrace tailWord_7716078 prefixEnd_7716078 3962056781582967043039409 := by
  unfold tailWord_7716078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35178560617496835256499611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187618989959983121367997925 35178560617496835256499611)
  ·
    refine ⟨52767840926245252884749417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35178560617496835256499611 52767840926245252884749417)
    ·
      refine ⟨39575880694683939663562063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52767840926245252884749417 39575880694683939663562063)
      ·
        refine ⟨59363821042025909495343095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39575880694683939663562063 59363821042025909495343095)
        ·
          refine ⟨89045731563038864243014643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59363821042025909495343095 89045731563038864243014643)
          ·
            refine ⟨133568597344558296364521965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89045731563038864243014643 133568597344558296364521965)
            ·
              refine ⟨50088224004209361136695737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133568597344558296364521965 50088224004209361136695737)
              ·
                refine ⟨37566168003157020852521803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50088224004209361136695737 37566168003157020852521803)
                ·
                  refine ⟨56349252004735531278782705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37566168003157020852521803 56349252004735531278782705)
                  ·
                    refine ⟨42261939003551648459087029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56349252004735531278782705 42261939003551648459087029)
                    ·
                      refine ⟨3962056781582967043039409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42261939003551648459087029 3962056781582967043039409)
                      ·
                        rfl

theorem cell23_7716078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7716078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716078 prefixEnd_7716078 := by exact prefixLift 7716078
  have htrace : WordTrace (prefixWord ++ tailWord_7716078) baseStart_7716078 baseEnd_7716078 := by
    simpa [prefixWord, tailWord_7716078, baseEnd_7716078] using wordTrace_append hprefix tailTrace_7716078
  have hstable : (prefixWord ++ tailWord_7716078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716078).length < 2 ^ (prefixWord ++ tailWord_7716078).sum := by decide
  have hdescent : baseEnd_7716078 < baseStart_7716078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716105 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 2, 4, 2]
def baseStart_7716105 : Nat := 118140960795 + 7716105 * 2 ^ 59
def prefixEnd_7716105 : Nat := 4983230072969 + 3 ^ 40 * 7716105 * 2
def baseEnd_7716105 : Nat := 3962070645560638437401785

theorem tailTrace_7716105 : CollatzResearch.WordTrace tailWord_7716105 prefixEnd_7716105 3962070645560638437401785 := by
  unfold tailWord_7716105
  simp only [CollatzResearch.WordTrace]
  refine ⟨281429469710876865663229769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187619646473917910442153179 281429469710876865663229769)
  ·
    refine ⟨211072102283157649247422327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281429469710876865663229769 211072102283157649247422327)
    ·
      refine ⟨316608153424736473871133491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211072102283157649247422327 316608153424736473871133491)
      ·
        refine ⟨474912230137104710806700237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316608153424736473871133491 474912230137104710806700237)
        ·
          refine ⟨178092086301414266552512589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474912230137104710806700237 178092086301414266552512589)
          ·
            refine ⟨66784532363030349957192221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178092086301414266552512589 66784532363030349957192221)
            ·
              refine ⟨25044199636136381233947083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66784532363030349957192221 25044199636136381233947083)
              ·
                refine ⟨37566299454204571850920625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25044199636136381233947083 37566299454204571850920625)
                ·
                  refine ⟨28174724590653428888190469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37566299454204571850920625 28174724590653428888190469)
                  ·
                    refine ⟨5282760860747517916535713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28174724590653428888190469 5282760860747517916535713)
                    ·
                      refine ⟨3962070645560638437401785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282760860747517916535713 3962070645560638437401785)
                      ·
                        rfl

theorem cell23_7716105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4, 2].length) (baseStart_7716105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716105 prefixEnd_7716105 := by exact prefixLift 7716105
  have htrace : WordTrace (prefixWord ++ tailWord_7716105) baseStart_7716105 baseEnd_7716105 := by
    simpa [prefixWord, tailWord_7716105, baseEnd_7716105] using wordTrace_append hprefix tailTrace_7716105
  have hstable : (prefixWord ++ tailWord_7716105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716105).length < 2 ^ (prefixWord ++ tailWord_7716105).sum := by decide
  have hdescent : baseEnd_7716105 < baseStart_7716105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716111 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 12]
def baseStart_7716111 : Nat := 118140960795 + 7716111 * 2 ^ 59
def prefixEnd_7716111 : Nat := 4983230072969 + 3 ^ 40 * 7716111 * 2
def baseEnd_7716111 : Nat := 440230414049396157102973

theorem tailTrace_7716111 : CollatzResearch.WordTrace tailWord_7716111 prefixEnd_7716111 440230414049396157102973 := by
  unfold tailWord_7716111
  simp only [CollatzResearch.WordTrace]
  refine ⟨281429688548855128687948187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187619792365903419125298791 281429688548855128687948187)
  ·
    refine ⟨422144532823282693031922281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281429688548855128687948187 422144532823282693031922281)
    ·
      refine ⟨316608399617462019773941711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422144532823282693031922281 316608399617462019773941711)
      ·
        refine ⟨474912599426193029660912567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316608399617462019773941711 474912599426193029660912567)
        ·
          refine ⟨712368899139289544491368851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474912599426193029660912567 712368899139289544491368851)
          ·
            refine ⟨1068553348708934316737053277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712368899139289544491368851 1068553348708934316737053277)
            ·
              refine ⟨400707505765850368776394979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068553348708934316737053277 400707505765850368776394979)
              ·
                refine ⟨601061258648775553164592469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400707505765850368776394979 601061258648775553164592469)
                ·
                  refine ⟨440230414049396157102973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 601061258648775553164592469 440230414049396157102973)
                  ·
                    rfl

theorem cell23_7716111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 12].length) (baseStart_7716111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716111 prefixEnd_7716111 := by exact prefixLift 7716111
  have htrace : WordTrace (prefixWord ++ tailWord_7716111) baseStart_7716111 baseEnd_7716111 := by
    simpa [prefixWord, tailWord_7716111, baseEnd_7716111] using wordTrace_append hprefix tailTrace_7716111
  have hstable : (prefixWord ++ tailWord_7716111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716111).length < 2 ^ (prefixWord ++ tailWord_7716111).sum := by decide
  have hdescent : baseEnd_7716111 < baseStart_7716111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716122 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_7716122 : Nat := 118140960795 + 7716122 * 2 ^ 59
def prefixEnd_7716122 : Nat := 4983230072969 + 3 ^ 40 * 7716122 * 2
def baseEnd_7716122 : Nat := 3962079374731764870889207

theorem tailTrace_7716122 : CollatzResearch.WordTrace tailWord_7716122 prefixEnd_7716122 3962079374731764870889207 := by
  unfold tailWord_7716122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70357522437953819391649655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187620059834543518377732413 70357522437953819391649655)
  ·
    refine ⟨105536283656930729087474483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70357522437953819391649655 105536283656930729087474483)
    ·
      refine ⟨158304425485396093631211725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105536283656930729087474483 158304425485396093631211725)
      ·
        refine ⟨59364159557023535111704397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158304425485396093631211725 59364159557023535111704397)
        ·
          refine ⟨22261559833883825666889149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59364159557023535111704397 22261559833883825666889149)
          ·
            refine ⟨8348084937706434625083431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22261559833883825666889149 8348084937706434625083431)
            ·
              refine ⟨12522127406559651937625147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8348084937706434625083431 12522127406559651937625147)
              ·
                refine ⟨18783191109839477906437721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522127406559651937625147 18783191109839477906437721)
                ·
                  refine ⟨14087393332379608429828291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18783191109839477906437721 14087393332379608429828291)
                  ·
                    refine ⟨21131089998569412644742437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14087393332379608429828291 21131089998569412644742437)
                    ·
                      refine ⟨3962079374731764870889207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21131089998569412644742437 3962079374731764870889207)
                      ·
                        rfl

theorem cell23_7716122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_7716122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716122 prefixEnd_7716122 := by exact prefixLift 7716122
  have htrace : WordTrace (prefixWord ++ tailWord_7716122) baseStart_7716122 baseEnd_7716122 := by
    simpa [prefixWord, tailWord_7716122, baseEnd_7716122] using wordTrace_append hprefix tailTrace_7716122
  have hstable : (prefixWord ++ tailWord_7716122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716122).length < 2 ^ (prefixWord ++ tailWord_7716122).sum := by decide
  have hdescent : baseEnd_7716122 < baseStart_7716122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716145 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 6]
def baseStart_7716145 : Nat := 118140960795 + 7716145 * 2 ^ 59
def prefixEnd_7716145 : Nat := 4983230072969 + 3 ^ 40 * 7716145 * 2
def baseEnd_7716145 : Nat := 440232353865202031211289

theorem tailTrace_7716145 : CollatzResearch.WordTrace tailWord_7716145 prefixEnd_7716145 440232353865202031211289 := by
  unfold tailWord_7716145
  simp only [CollatzResearch.WordTrace]
  refine ⟨281430928630731952494685889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187620619087154634996457259 281430928630731952494685889)
  ·
    refine ⟨211073196473048964371014417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281430928630731952494685889 211073196473048964371014417)
    ·
      refine ⟨158304897354786723278260813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211073196473048964371014417 158304897354786723278260813)
      ·
        refine ⟨59364336508045021229347805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158304897354786723278260813 59364336508045021229347805)
        ·
          refine ⟨22261626190516882961005427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59364336508045021229347805 22261626190516882961005427)
          ·
            refine ⟨33392439285775324441508141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22261626190516882961005427 33392439285775324441508141)
            ·
              refine ⟨12522164732165746665565553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33392439285775324441508141 12522164732165746665565553)
              ·
                refine ⟨9391623549124309999174165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522164732165746665565553 9391623549124309999174165)
                ·
                  refine ⟨440232353865202031211289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9391623549124309999174165 440232353865202031211289)
                  ·
                    rfl

theorem cell23_7716145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_7716145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716145 prefixEnd_7716145 := by exact prefixLift 7716145
  have htrace : WordTrace (prefixWord ++ tailWord_7716145) baseStart_7716145 baseEnd_7716145 := by
    simpa [prefixWord, tailWord_7716145, baseEnd_7716145] using wordTrace_append hprefix tailTrace_7716145
  have hstable : (prefixWord ++ tailWord_7716145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716145).length < 2 ^ (prefixWord ++ tailWord_7716145).sum := by decide
  have hdescent : baseEnd_7716145 < baseStart_7716145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716172 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_7716172 : Nat := 118140960795 + 7716172 * 2 ^ 59
def prefixEnd_7716172 : Nat := 4983230072969 + 3 ^ 40 * 7716172 * 2
def baseEnd_7716172 : Nat := 3962105048764489675263977

theorem tailTrace_7716172 : CollatzResearch.WordTrace tailWord_7716172 prefixEnd_7716172 3962105048764489675263977 := by
  unfold tailWord_7716172
  simp only [CollatzResearch.WordTrace]
  refine ⟨140715956700817068052959385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187621275601089424070612513 140715956700817068052959385)
  ·
    refine ⟨105536967525612801039719539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140715956700817068052959385 105536967525612801039719539)
    ·
      refine ⟨158305451288419201559579309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105536967525612801039719539 158305451288419201559579309)
      ·
        refine ⟨59364544233157200584842241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158305451288419201559579309 59364544233157200584842241)
        ·
          refine ⟨44523408174867900438631681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59364544233157200584842241 44523408174867900438631681)
          ·
            refine ⟨33392556131150925328973761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44523408174867900438631681 33392556131150925328973761)
            ·
              refine ⟨25044417098363193996730321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33392556131150925328973761 25044417098363193996730321)
              ·
                refine ⟨18783312823772395497547741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25044417098363193996730321 18783312823772395497547741)
                ·
                  refine ⟨7043742308914648311580403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18783312823772395497547741 7043742308914648311580403)
                  ·
                    refine ⟨10565613463371972467370605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7043742308914648311580403 10565613463371972467370605)
                    ·
                      refine ⟨3962105048764489675263977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10565613463371972467370605 3962105048764489675263977)
                      ·
                        rfl

theorem cell23_7716172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_7716172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716172 prefixEnd_7716172 := by exact prefixLift 7716172
  have htrace : WordTrace (prefixWord ++ tailWord_7716172) baseStart_7716172 baseEnd_7716172 := by
    simpa [prefixWord, tailWord_7716172, baseEnd_7716172] using wordTrace_append hprefix tailTrace_7716172
  have hstable : (prefixWord ++ tailWord_7716172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716172).length < 2 ^ (prefixWord ++ tailWord_7716172).sum := by decide
  have hdescent : baseEnd_7716172 < baseStart_7716172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716199 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_7716199 : Nat := 118140960795 + 7716199 * 2 ^ 59
def prefixEnd_7716199 : Nat := 4983230072969 + 3 ^ 40 * 7716199 * 2
def baseEnd_7716199 : Nat := 3962118912742161069626353

theorem tailTrace_7716199 : CollatzResearch.WordTrace tailWord_7716199 prefixEnd_7716199 3962118912742161069626353 := by
  unfold tailWord_7716199
  simp only [CollatzResearch.WordTrace]
  refine ⟨281432898172536319717151651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187621932115024213144767767 281432898172536319717151651)
  ·
    refine ⟨422149347258804479575727477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281432898172536319717151651 422149347258804479575727477)
    ·
      refine ⟨39576501305512919960224451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422149347258804479575727477 39576501305512919960224451)
      ·
        refine ⟨59364751958269379940336677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39576501305512919960224451 59364751958269379940336677)
        ·
          refine ⟨11130890992175508738813127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59364751958269379940336677 11130890992175508738813127)
          ·
            refine ⟨16696336488263263108219691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130890992175508738813127 16696336488263263108219691)
            ·
              refine ⟨25044504732394894662329537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16696336488263263108219691 25044504732394894662329537)
              ·
                refine ⟨18783378549296170996747153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25044504732394894662329537 18783378549296170996747153)
                ·
                  refine ⟨14087533911972128247560365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18783378549296170996747153 14087533911972128247560365)
                  ·
                    refine ⟨5282825216989548092835137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14087533911972128247560365 5282825216989548092835137)
                    ·
                      refine ⟨3962118912742161069626353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282825216989548092835137 3962118912742161069626353)
                      ·
                        rfl

theorem cell23_7716199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_7716199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716199 prefixEnd_7716199 := by exact prefixLift 7716199
  have htrace : WordTrace (prefixWord ++ tailWord_7716199) baseStart_7716199 baseEnd_7716199 := by
    simpa [prefixWord, tailWord_7716199, baseEnd_7716199] using wordTrace_append hprefix tailTrace_7716199
  have hstable : (prefixWord ++ tailWord_7716199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716199).length < 2 ^ (prefixWord ++ tailWord_7716199).sum := by decide
  have hdescent : baseEnd_7716199 < baseStart_7716199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716208 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_7716208 : Nat := 118140960795 + 7716208 * 2 ^ 59
def prefixEnd_7716208 : Nat := 4983230072969 + 3 ^ 40 * 7716208 * 2
def baseEnd_7716208 : Nat := 3962123534068051534413811

theorem tailTrace_7716208 : CollatzResearch.WordTrace tailWord_7716208 prefixEnd_7716208 3962123534068051534413811 := by
  unfold tailWord_7716208
  simp only [CollatzResearch.WordTrace]
  refine ⟨140716613214751857127114639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187622150953002476169486185 140716613214751857127114639)
  ·
    refine ⟨211074919822127785690671959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140716613214751857127114639 211074919822127785690671959)
    ·
      refine ⟨316612379733191678536007939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211074919822127785690671959 316612379733191678536007939)
      ·
        refine ⟨474918569599787517804011909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316612379733191678536007939 474918569599787517804011909)
        ·
          refine ⟨89047231799960159588252233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 474918569599787517804011909 89047231799960159588252233)
          ·
            refine ⟨66785423849970119691189175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89047231799960159588252233 66785423849970119691189175)
            ·
              refine ⟨100178135774955179536783763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66785423849970119691189175 100178135774955179536783763)
              ·
                refine ⟨150267203662432769305175645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100178135774955179536783763 150267203662432769305175645)
                ·
                  refine ⟨56350201373412288489440867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150267203662432769305175645 56350201373412288489440867)
                  ·
                    refine ⟨84525302060118432734161301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56350201373412288489440867 84525302060118432734161301)
                    ·
                      refine ⟨3962123534068051534413811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84525302060118432734161301 3962123534068051534413811)
                      ·
                        rfl

theorem cell23_7716208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_7716208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716208 prefixEnd_7716208 := by exact prefixLift 7716208
  have htrace : WordTrace (prefixWord ++ tailWord_7716208) baseStart_7716208 baseEnd_7716208 := by
    simpa [prefixWord, tailWord_7716208, baseEnd_7716208] using wordTrace_append hprefix tailTrace_7716208
  have hstable : (prefixWord ++ tailWord_7716208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716208).length < 2 ^ (prefixWord ++ tailWord_7716208).sum := by decide
  have hdescent : baseEnd_7716208 < baseStart_7716208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716215 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_7716215 : Nat := 118140960795 + 7716215 * 2 ^ 59
def prefixEnd_7716215 : Nat := 4983230072969 + 3 ^ 40 * 7716215 * 2
def baseEnd_7716215 : Nat := 3962127128432633007026279

theorem tailTrace_7716215 : CollatzResearch.WordTrace tailWord_7716215 prefixEnd_7716215 3962127128432633007026279 := by
  unfold tailWord_7716215
  simp only [CollatzResearch.WordTrace]
  refine ⟨281433481740478354449734099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187622321160318902966489399 281433481740478354449734099)
  ·
    refine ⟨422150222610717531674601149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281433481740478354449734099 422150222610717531674601149)
    ·
      refine ⟨158306333479019074377975431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422150222610717531674601149 158306333479019074377975431)
      ·
        refine ⟨237459500218528611566963147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158306333479019074377975431 237459500218528611566963147)
        ·
          refine ⟨356189250327792917350444721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237459500218528611566963147 356189250327792917350444721)
          ·
            refine ⟨267141937745844688012833541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356189250327792917350444721 267141937745844688012833541)
            ·
              refine ⟨50089113327345879002406289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267141937745844688012833541 50089113327345879002406289)
              ·
                refine ⟨37566834995509409251804717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50089113327345879002406289 37566834995509409251804717)
                ·
                  refine ⟨14087563123316028469426769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37566834995509409251804717 14087563123316028469426769)
                  ·
                    refine ⟨10565672342487021352070077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14087563123316028469426769 10565672342487021352070077)
                    ·
                      refine ⟨3962127128432633007026279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10565672342487021352070077 3962127128432633007026279)
                      ·
                        rfl

theorem cell23_7716215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_7716215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716215 prefixEnd_7716215 := by exact prefixLift 7716215
  have htrace : WordTrace (prefixWord ++ tailWord_7716215) baseStart_7716215 baseEnd_7716215 := by
    simpa [prefixWord, tailWord_7716215, baseEnd_7716215] using wordTrace_append hprefix tailTrace_7716215
  have hstable : (prefixWord ++ tailWord_7716215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716215).length < 2 ^ (prefixWord ++ tailWord_7716215).sum := by decide
  have hdescent : baseEnd_7716215 < baseStart_7716215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716226 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7716226 : Nat := 118140960795 + 7716226 * 2 ^ 59
def prefixEnd_7716226 : Nat := 4983230072969 + 3 ^ 40 * 7716226 * 2
def baseEnd_7716226 : Nat := 1320710925573277487996243

theorem tailTrace_7716226 : CollatzResearch.WordTrace tailWord_7716226 prefixEnd_7716226 1320710925573277487996243 := by
  unfold tailWord_7716226
  simp only [CollatzResearch.WordTrace]
  refine ⟨70358470735859625832096133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187622588628959002218923021 70358470735859625832096133)
  ·
    refine ⟨13192213262973679843518025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70358470735859625832096133 13192213262973679843518025)
    ·
      refine ⟨9894159947230259882638519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13192213262973679843518025 9894159947230259882638519)
      ·
        refine ⟨14841239920845389823957779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9894159947230259882638519 14841239920845389823957779)
        ·
          refine ⟨22261859881268084735936669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14841239920845389823957779 22261859881268084735936669)
          ·
            refine ⟨8348197455475531775976251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22261859881268084735936669 8348197455475531775976251)
            ·
              refine ⟨12522296183213297663964377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8348197455475531775976251 12522296183213297663964377)
              ·
                refine ⟨9391722137409973247973283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522296183213297663964377 9391722137409973247973283)
                ·
                  refine ⟨14087583206114959871959925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391722137409973247973283 14087583206114959871959925)
                  ·
                    refine ⟨1320710925573277487996243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087583206114959871959925 1320710925573277487996243)
                    ·
                      rfl

theorem cell23_7716226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7716226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716226 prefixEnd_7716226 := by exact prefixLift 7716226
  have htrace : WordTrace (prefixWord ++ tailWord_7716226) baseStart_7716226 baseEnd_7716226 := by
    simpa [prefixWord, tailWord_7716226, baseEnd_7716226] using wordTrace_append hprefix tailTrace_7716226
  have hstable : (prefixWord ++ tailWord_7716226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716226).length < 2 ^ (prefixWord ++ tailWord_7716226).sum := by decide
  have hdescent : baseEnd_7716226 < baseStart_7716226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716232 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7716232 : Nat := 118140960795 + 7716232 * 2 ^ 59
def prefixEnd_7716232 : Nat := 4983230072969 + 3 ^ 40 * 7716232 * 2
def baseEnd_7716232 : Nat := 3962135857603759440513701

theorem tailTrace_7716232 : CollatzResearch.WordTrace tailWord_7716232 prefixEnd_7716232 3962135857603759440513701 := by
  unfold tailWord_7716232
  simp only [CollatzResearch.WordTrace]
  refine ⟨140717050890708383176551475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187622734520944510902068633 140717050890708383176551475)
  ·
    refine ⟨211075576336062574764827213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140717050890708383176551475 211075576336062574764827213)
    ·
      refine ⟨79153341126023465536810205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211075576336062574764827213 79153341126023465536810205)
      ·
        refine ⟨29682502922258799576303827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79153341126023465536810205 29682502922258799576303827)
        ·
          refine ⟨44523754383388199364455741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29682502922258799576303827 44523754383388199364455741)
          ·
            refine ⟨16696407893770574761670903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44523754383388199364455741 16696407893770574761670903)
            ·
              refine ⟨25044611840655862142506355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16696407893770574761670903 25044611840655862142506355)
              ·
                refine ⟨37566917760983793213759533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25044611840655862142506355 37566917760983793213759533)
                ·
                  refine ⟨14087594160368922455159825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37566917760983793213759533 14087594160368922455159825)
                  ·
                    refine ⟨10565695620276691841369869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14087594160368922455159825 10565695620276691841369869)
                    ·
                      refine ⟨3962135857603759440513701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10565695620276691841369869 3962135857603759440513701)
                      ·
                        rfl

theorem cell23_7716232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7716232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716232 prefixEnd_7716232 := by exact prefixLift 7716232
  have htrace : WordTrace (prefixWord ++ tailWord_7716232) baseStart_7716232 baseEnd_7716232 := by
    simpa [prefixWord, tailWord_7716232, baseEnd_7716232] using wordTrace_append hprefix tailTrace_7716232
  have hstable : (prefixWord ++ tailWord_7716232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716232).length < 2 ^ (prefixWord ++ tailWord_7716232).sum := by decide
  have hdescent : baseEnd_7716232 < baseStart_7716232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716245 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_7716245 : Nat := 118140960795 + 7716245 * 2 ^ 59
def prefixEnd_7716245 : Nat := 4983230072969 + 3 ^ 40 * 7716245 * 2
def baseEnd_7716245 : Nat := 3962142532852267889651141

theorem tailTrace_7716245 : CollatzResearch.WordTrace tailWord_7716245 prefixEnd_7716245 3962142532852267889651141 := by
  unfold tailWord_7716245
  simp only [CollatzResearch.WordTrace]
  refine ⟨281434575930369669573326189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187623050620246446382217459 281434575930369669573326189)
  ·
    refine ⟨105537965973888626089997321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281434575930369669573326189 105537965973888626089997321)
    ·
      refine ⟨79153474480416469567497991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105537965973888626089997321 79153474480416469567497991)
      ·
        refine ⟨118730211720624704351246987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79153474480416469567497991 118730211720624704351246987)
        ·
          refine ⟨178095317580937056526870481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118730211720624704351246987 178095317580937056526870481)
          ·
            refine ⟨133571488185702792395152861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178095317580937056526870481 133571488185702792395152861)
            ·
              refine ⟨50089308069638547148182323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133571488185702792395152861 50089308069638547148182323)
              ·
                refine ⟨75133962104457820722273485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50089308069638547148182323 75133962104457820722273485)
                ·
                  refine ⟨28175235789171682770852557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75133962104457820722273485 28175235789171682770852557)
                  ·
                    refine ⟨10565713420939381039069709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28175235789171682770852557 10565713420939381039069709)
                    ·
                      refine ⟨3962142532852267889651141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10565713420939381039069709 3962142532852267889651141)
                      ·
                        rfl

theorem cell23_7716245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_7716245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716245 prefixEnd_7716245 := by exact prefixLift 7716245
  have htrace : WordTrace (prefixWord ++ tailWord_7716245) baseStart_7716245 baseEnd_7716245 := by
    simpa [prefixWord, tailWord_7716245, baseEnd_7716245] using wordTrace_append hprefix tailTrace_7716245
  have hstable : (prefixWord ++ tailWord_7716245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716245).length < 2 ^ (prefixWord ++ tailWord_7716245).sum := by decide
  have hdescent : baseEnd_7716245 < baseStart_7716245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716249 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 1, 2, 3]
def baseStart_7716249 : Nat := 118140960795 + 7716249 * 2 ^ 59
def prefixEnd_7716249 : Nat := 4983230072969 + 3 ^ 40 * 7716249 * 2
def baseEnd_7716249 : Nat := 3962144586774885874001123

theorem tailTrace_7716249 : CollatzResearch.WordTrace tailWord_7716249 prefixEnd_7716249 3962144586774885874001123 := by
  unfold tailWord_7716249
  simp only [CollatzResearch.WordTrace]
  refine ⟨281434721822355178256471801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187623147881570118837647867 281434721822355178256471801)
  ·
    refine ⟨211076041366766383692353851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281434721822355178256471801 211076041366766383692353851)
    ·
      refine ⟨316614062050149575538530777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211076041366766383692353851 316614062050149575538530777)
      ·
        refine ⟨237460546537612181653898083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316614062050149575538530777 237460546537612181653898083)
        ·
          refine ⟨356190819806418272480847125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237460546537612181653898083 356190819806418272480847125)
          ·
            refine ⟨16696444678425856522539709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356190819806418272480847125 16696444678425856522539709)
            ·
              refine ⟨6261166754409696195952391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16696444678425856522539709 6261166754409696195952391)
              ·
                refine ⟨9391750131614544293928587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261166754409696195952391 9391750131614544293928587)
                ·
                  refine ⟨14087625197421816440892881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391750131614544293928587 14087625197421816440892881)
                  ·
                    refine ⟨10565718898066362330669661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14087625197421816440892881 10565718898066362330669661)
                    ·
                      refine ⟨3962144586774885874001123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10565718898066362330669661 3962144586774885874001123)
                      ·
                        rfl

theorem cell23_7716249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_7716249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716249 prefixEnd_7716249 := by exact prefixLift 7716249
  have htrace : WordTrace (prefixWord ++ tailWord_7716249) baseStart_7716249 baseEnd_7716249 := by
    simpa [prefixWord, tailWord_7716249, baseEnd_7716249] using wordTrace_append hprefix tailTrace_7716249
  have hstable : (prefixWord ++ tailWord_7716249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716249).length < 2 ^ (prefixWord ++ tailWord_7716249).sum := by decide
  have hdescent : baseEnd_7716249 < baseStart_7716249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716252 : List Nat := [2, 2, 3, 4, 2, 10]
def baseStart_7716252 : Nat := 118140960795 + 7716252 * 2 ^ 59
def prefixEnd_7716252 : Nat := 4983230072969 + 3 ^ 40 * 7716252 * 2
def baseEnd_7716252 : Nat := 16305128095542589968163

theorem tailTrace_7716252 : CollatzResearch.WordTrace tailWord_7716252 prefixEnd_7716252 16305128095542589968163 := by
  unfold tailWord_7716252
  simp only [CollatzResearch.WordTrace]
  refine ⟨140717415620672154884415505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187623220827562873179220673 140717415620672154884415505)
  ·
    refine ⟨105538061715504116163311629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140717415620672154884415505 105538061715504116163311629)
    ·
      refine ⟨39576773143314043561241861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105538061715504116163311629 39576773143314043561241861)
      ·
        refine ⟨7420644964371383167732849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39576773143314043561241861 7420644964371383167732849)
        ·
          refine ⟨5565483723278537375799637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7420644964371383167732849 5565483723278537375799637)
          ·
            refine ⟨16305128095542589968163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5565483723278537375799637 16305128095542589968163)
            ·
              rfl

theorem cell23_7716252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 10].length) (baseStart_7716252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716252 prefixEnd_7716252 := by exact prefixLift 7716252
  have htrace : WordTrace (prefixWord ++ tailWord_7716252) baseStart_7716252 baseEnd_7716252 := by
    simpa [prefixWord, tailWord_7716252, baseEnd_7716252] using wordTrace_append hprefix tailTrace_7716252
  have hstable : (prefixWord ++ tailWord_7716252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716252).length < 2 ^ (prefixWord ++ tailWord_7716252).sum := by decide
  have hdescent : baseEnd_7716252 < baseStart_7716252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716285 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7716285 : Nat := 118140960795 + 7716285 * 2 ^ 59
def prefixEnd_7716285 : Nat := 4983230072969 + 3 ^ 40 * 7716285 * 2
def baseEnd_7716285 : Nat := 3962163072078447733150957

theorem tailTrace_7716285 : CollatzResearch.WordTrace tailWord_7716285 prefixEnd_7716285 3962163072078447733150957 := by
  unfold tailWord_7716285
  simp only [CollatzResearch.WordTrace]
  refine ⟨281436034850224756404782309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187624023233483170936521539 281436034850224756404782309)
  ·
    refine ⟨52769256534417141825896683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281436034850224756404782309 52769256534417141825896683)
    ·
      refine ⟨79153884801625712738845025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52769256534417141825896683 79153884801625712738845025)
      ·
        refine ⟨59365413601219284554133769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79153884801625712738845025 59365413601219284554133769)
        ·
          refine ⟨44524060200914463415600327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59365413601219284554133769 44524060200914463415600327)
          ·
            refine ⟨66786090301371695123400491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44524060200914463415600327 66786090301371695123400491)
            ·
              refine ⟨100179135452057542685100737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66786090301371695123400491 100179135452057542685100737)
              ·
                refine ⟨75134351589043157013825553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100179135452057542685100737 75134351589043157013825553)
                ·
                  refine ⟨56350763691782367760369165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75134351589043157013825553 56350763691782367760369165)
                  ·
                    refine ⟨21131536384418387910138437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56350763691782367760369165 21131536384418387910138437)
                    ·
                      refine ⟨3962163072078447733150957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21131536384418387910138437 3962163072078447733150957)
                      ·
                        rfl

theorem cell23_7716285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7716285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716285 prefixEnd_7716285 := by exact prefixLift 7716285
  have htrace : WordTrace (prefixWord ++ tailWord_7716285) baseStart_7716285 baseEnd_7716285 := by
    simpa [prefixWord, tailWord_7716285, baseEnd_7716285] using wordTrace_append hprefix tailTrace_7716285
  have hstable : (prefixWord ++ tailWord_7716285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716285).length < 2 ^ (prefixWord ++ tailWord_7716285).sum := by decide
  have hdescent : baseEnd_7716285 < baseStart_7716285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716319 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 4, 2, 2]
def baseStart_7716319 : Nat := 118140960795 + 7716319 * 2 ^ 59
def prefixEnd_7716319 : Nat := 4983230072969 + 3 ^ 40 * 7716319 * 2
def baseEnd_7716319 : Nat := 3962180530420700600125801

theorem tailTrace_7716319 : CollatzResearch.WordTrace tailWord_7716319 prefixEnd_7716319 3962180530420700600125801 := by
  unfold tailWord_7716319
  simp only [CollatzResearch.WordTrace]
  refine ⟨281437274932101580211520011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187624849954734386807680007 281437274932101580211520011)
  ·
    refine ⟨422155912398152370317280017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281437274932101580211520011 422155912398152370317280017)
    ·
      refine ⟨316616934298614277737960013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422155912398152370317280017 316616934298614277737960013)
      ·
        refine ⟨118731350361980354151735005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316616934298614277737960013 118731350361980354151735005)
        ·
          refine ⟨44524256385742632806900627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118731350361980354151735005 44524256385742632806900627)
          ·
            refine ⟨66786384578613949210350941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44524256385742632806900627 66786384578613949210350941)
            ·
              refine ⟨25044894216980230953881603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66786384578613949210350941 25044894216980230953881603)
              ·
                refine ⟨37567341325470346430822405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25044894216980230953881603 37567341325470346430822405)
                ·
                  refine ⟨7043876498525689955779201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37567341325470346430822405 7043876498525689955779201)
                  ·
                    refine ⟨5282907373894267466834401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043876498525689955779201 5282907373894267466834401)
                    ·
                      refine ⟨3962180530420700600125801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5282907373894267466834401 3962180530420700600125801)
                      ·
                        rfl

theorem cell23_7716319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_7716319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716319 prefixEnd_7716319 := by exact prefixLift 7716319
  have htrace : WordTrace (prefixWord ++ tailWord_7716319) baseStart_7716319 baseEnd_7716319 := by
    simpa [prefixWord, tailWord_7716319, baseEnd_7716319] using wordTrace_append hprefix tailTrace_7716319
  have hstable : (prefixWord ++ tailWord_7716319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716319).length < 2 ^ (prefixWord ++ tailWord_7716319).sum := by decide
  have hdescent : baseEnd_7716319 < baseStart_7716319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716342 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_7716342 : Nat := 118140960795 + 7716342 * 2 ^ 59
def prefixEnd_7716342 : Nat := 4983230072969 + 3 ^ 40 * 7716342 * 2
def baseEnd_7716342 : Nat := 440243593386194890015355

theorem tailTrace_7716342 : CollatzResearch.WordTrace tailWord_7716342 prefixEnd_7716342 440243593386194890015355 := by
  unfold tailWord_7716342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17589882113188640946225455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187625409207345503426404853 17589882113188640946225455)
  ·
    refine ⟨26384823169782961419338183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17589882113188640946225455 26384823169782961419338183)
    ·
      refine ⟨39577234754674442129007275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26384823169782961419338183 39577234754674442129007275)
      ·
        refine ⟨59365852132011663193510913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39577234754674442129007275 59365852132011663193510913)
        ·
          refine ⟨44524389099008747395133185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59365852132011663193510913 44524389099008747395133185)
          ·
            refine ⟨33393291824256560546349889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44524389099008747395133185 33393291824256560546349889)
            ·
              refine ⟨25044968868192420409762417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33393291824256560546349889 25044968868192420409762417)
              ·
                refine ⟨18783726651144315307321813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25044968868192420409762417 18783726651144315307321813)
                ·
                  refine ⟨440243593386194890015355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18783726651144315307321813 440243593386194890015355)
                  ·
                    rfl

theorem cell23_7716342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_7716342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716342 prefixEnd_7716342 := by exact prefixLift 7716342
  have htrace : WordTrace (prefixWord ++ tailWord_7716342) baseStart_7716342 baseEnd_7716342 := by
    simpa [prefixWord, tailWord_7716342, baseEnd_7716342] using wordTrace_append hprefix tailTrace_7716342
  have hstable : (prefixWord ++ tailWord_7716342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716342).length < 2 ^ (prefixWord ++ tailWord_7716342).sum := by decide
  have hdescent : baseEnd_7716342 < baseStart_7716342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716359 : List Nat := [1, 1, 4, 3, 2, 1, 3, 3, 5]
def baseStart_7716359 : Nat := 118140960795 + 7716359 * 2 ^ 59
def prefixEnd_7716359 : Nat := 4983230072969 + 3 ^ 40 * 7716359 * 2
def baseEnd_7716359 : Nat := 440244563294097827069513

theorem tailTrace_7716359 : CollatzResearch.WordTrace tailWord_7716359 prefixEnd_7716359 440244563294097827069513 := by
  unfold tailWord_7716359
  simp only [CollatzResearch.WordTrace]
  refine ⟨281438733851956667042976131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187625822567971111361984087 281438733851956667042976131)
  ·
    refine ⟨422158100777935000564464197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281438733851956667042976131 422158100777935000564464197)
    ·
      refine ⟨79154643895862812605837037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422158100777935000564464197 79154643895862812605837037)
      ·
        refine ⟨29682991460948554727188889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79154643895862812605837037 29682991460948554727188889)
        ·
          refine ⟨22262243595711416045391667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29682991460948554727188889 22262243595711416045391667)
          ·
            refine ⟨33393365393567124068087501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22262243595711416045391667 33393365393567124068087501)
            ·
              refine ⟨12522512022587671525532813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33393365393567124068087501 12522512022587671525532813)
              ·
                refine ⟨4695942008470376822074805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12522512022587671525532813 4695942008470376822074805)
                ·
                  refine ⟨440244563294097827069513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4695942008470376822074805 440244563294097827069513)
                  ·
                    rfl

theorem cell23_7716359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 5].length) (baseStart_7716359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716359 prefixEnd_7716359 := by exact prefixLift 7716359
  have htrace : WordTrace (prefixWord ++ tailWord_7716359) baseStart_7716359 baseEnd_7716359 := by
    simpa [prefixWord, tailWord_7716359, baseEnd_7716359] using wordTrace_append hprefix tailTrace_7716359
  have hstable : (prefixWord ++ tailWord_7716359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716359).length < 2 ^ (prefixWord ++ tailWord_7716359).sum := by decide
  have hdescent : baseEnd_7716359 < baseStart_7716359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716376 : List Nat := [2, 1, 2, 3, 4, 1, 3, 2, 5]
def baseStart_7716376 : Nat := 118140960795 + 7716376 * 2 ^ 59
def prefixEnd_7716376 : Nat := 4983230072969 + 3 ^ 40 * 7716376 * 2
def baseEnd_7716376 : Nat := 440245533202000764123671

theorem tailTrace_7716376 : CollatzResearch.WordTrace tailWord_7716376 prefixEnd_7716376 440245533202000764123671 := by
  unfold tailWord_7716376
  simp only [CollatzResearch.WordTrace]
  refine ⟨140719676946447539473172491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187626235928596719297563321 140719676946447539473172491)
  ·
    refine ⟨211079515419671309209758737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140719676946447539473172491 211079515419671309209758737)
    ·
      refine ⟨158309636564753481907319053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211079515419671309209758737 158309636564753481907319053)
      ·
        refine ⟨59366113711782555715244645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158309636564753481907319053 59366113711782555715244645)
        ·
          refine ⟨11131146320959229196608371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59366113711782555715244645 11131146320959229196608371)
          ·
            refine ⟨16696719481438843794912557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131146320959229196608371 16696719481438843794912557)
            ·
              refine ⟨6261269805539566423092209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16696719481438843794912557 6261269805539566423092209)
              ·
                refine ⟨4695952354154674817319157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261269805539566423092209 4695952354154674817319157)
                ·
                  refine ⟨440245533202000764123671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4695952354154674817319157 440245533202000764123671)
                  ·
                    rfl

theorem cell23_7716376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 5].length) (baseStart_7716376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716376 prefixEnd_7716376 := by exact prefixLift 7716376
  have htrace : WordTrace (prefixWord ++ tailWord_7716376) baseStart_7716376 baseEnd_7716376 := by
    simpa [prefixWord, tailWord_7716376, baseEnd_7716376] using wordTrace_append hprefix tailTrace_7716376
  have hstable : (prefixWord ++ tailWord_7716376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716376).length < 2 ^ (prefixWord ++ tailWord_7716376).sum := by decide
  have hdescent : baseEnd_7716376 < baseStart_7716376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716402 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_7716402 : Nat := 118140960795 + 7716402 * 2 ^ 59
def prefixEnd_7716402 : Nat := 4983230072969 + 3 ^ 40 * 7716402 * 2
def baseEnd_7716402 : Nat := 1320741049771674591795973

theorem tailTrace_7716402 : CollatzResearch.WordTrace tailWord_7716402 prefixEnd_7716402 1320741049771674591795973 := by
  unfold tailWord_7716402
  simp only [CollatzResearch.WordTrace]
  refine ⟨70360075547700221346697865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187626868127200590257860973 70360075547700221346697865)
  ·
    refine ⟨52770056660775166010023399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70360075547700221346697865 52770056660775166010023399)
    ·
      refine ⟨79155084991162749015035099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52770056660775166010023399 79155084991162749015035099)
      ·
        refine ⟨118732627486744123522552649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79155084991162749015035099 118732627486744123522552649)
        ·
          refine ⟨89049470615058092641914487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118732627486744123522552649 89049470615058092641914487)
          ·
            refine ⟨133574205922587138962871731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89049470615058092641914487 133574205922587138962871731)
            ·
              refine ⟨200361308883880708444307597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133574205922587138962871731 200361308883880708444307597)
              ·
                refine ⟨75135490831455265666615349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200361308883880708444307597 75135490831455265666615349)
                ·
                  refine ⟨7043952265448931156245189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75135490831455265666615349 7043952265448931156245189)
                  ·
                    refine ⟨1320741049771674591795973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7043952265448931156245189 1320741049771674591795973)
                    ·
                      rfl

theorem cell23_7716402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_7716402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716402 prefixEnd_7716402 := by exact prefixLift 7716402
  have htrace : WordTrace (prefixWord ++ tailWord_7716402) baseStart_7716402 baseEnd_7716402 := by
    simpa [prefixWord, tailWord_7716402, baseEnd_7716402] using wordTrace_append hprefix tailTrace_7716402
  have hstable : (prefixWord ++ tailWord_7716402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716402).length < 2 ^ (prefixWord ++ tailWord_7716402).sum := by decide
  have hdescent : baseEnd_7716402 < baseStart_7716402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716406 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_7716406 : Nat := 118140960795 + 7716406 * 2 ^ 59
def prefixEnd_7716406 : Nat := 4983230072969 + 3 ^ 40 * 7716406 * 2
def baseEnd_7716406 : Nat := 1320741734412547253245967

theorem tailTrace_7716406 : CollatzResearch.WordTrace tailWord_7716406 prefixEnd_7716406 1320741734412547253245967 := by
  unfold tailWord_7716406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590028005174149629371067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187626965388524262713291381 17590028005174149629371067)
  ·
    refine ⟨26385042007761224444056601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17590028005174149629371067 26385042007761224444056601)
    ·
      refine ⟨19788781505820918333042451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26385042007761224444056601 19788781505820918333042451)
      ·
        refine ⟨29683172258731377499563677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19788781505820918333042451 29683172258731377499563677)
        ·
          refine ⟨11131189597024266562336379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29683172258731377499563677 11131189597024266562336379)
          ·
            refine ⟨16696784395536399843504569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131189597024266562336379 16696784395536399843504569)
            ·
              refine ⟨12522588296652299882628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16696784395536399843504569 12522588296652299882628427)
              ·
                refine ⟨18783882444978449823942641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522588296652299882628427 18783882444978449823942641)
                ·
                  refine ⟨14087911833733837367956981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18783882444978449823942641 14087911833733837367956981)
                  ·
                    refine ⟨1320741734412547253245967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14087911833733837367956981 1320741734412547253245967)
                    ·
                      rfl

theorem cell23_7716406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_7716406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716406 prefixEnd_7716406 := by exact prefixLift 7716406
  have htrace : WordTrace (prefixWord ++ tailWord_7716406) baseStart_7716406 baseEnd_7716406 := by
    simpa [prefixWord, tailWord_7716406, baseEnd_7716406] using wordTrace_append hprefix tailTrace_7716406
  have hstable : (prefixWord ++ tailWord_7716406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716406).length < 2 ^ (prefixWord ++ tailWord_7716406).sum := by decide
  have hdescent : baseEnd_7716406 < baseStart_7716406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716409 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7716409 : Nat := 118140960795 + 7716409 * 2 ^ 59
def prefixEnd_7716409 : Nat := 4983230072969 + 3 ^ 40 * 7716409 * 2
def baseEnd_7716409 : Nat := 3962226743679605248000387

theorem tailTrace_7716409 : CollatzResearch.WordTrace tailWord_7716409 prefixEnd_7716409 3962226743679605248000387 := by
  unfold tailWord_7716409
  simp only [CollatzResearch.WordTrace]
  refine ⟨281440557501775525582296281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187627038334517017054864187 281440557501775525582296281)
  ·
    refine ⟨211080418126331644186722211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281440557501775525582296281 211080418126331644186722211)
    ·
      refine ⟨316620627189497466280083317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211080418126331644186722211 316620627189497466280083317)
      ·
        refine ⟨29683183799015387463757811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316620627189497466280083317 29683183799015387463757811)
        ·
          refine ⟨44524775698523081195636717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29683183799015387463757811 44524775698523081195636717)
          ·
            refine ⟨16696790886946155448363769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44524775698523081195636717 16696790886946155448363769)
            ·
              refine ⟨12522593165209616586272827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16696790886946155448363769 12522593165209616586272827)
              ·
                refine ⟨18783889747814424879409241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522593165209616586272827 18783889747814424879409241)
                ·
                  refine ⟨14087917310860818659556931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18783889747814424879409241 14087917310860818659556931)
                  ·
                    refine ⟨21131875966291227989335397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14087917310860818659556931 21131875966291227989335397)
                    ·
                      refine ⟨3962226743679605248000387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21131875966291227989335397 3962226743679605248000387)
                      ·
                        rfl

theorem cell23_7716409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7716409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716409 prefixEnd_7716409 := by exact prefixLift 7716409
  have htrace : WordTrace (prefixWord ++ tailWord_7716409) baseStart_7716409 baseEnd_7716409 := by
    simpa [prefixWord, tailWord_7716409, baseEnd_7716409] using wordTrace_append hprefix tailTrace_7716409
  have hstable : (prefixWord ++ tailWord_7716409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716409).length < 2 ^ (prefixWord ++ tailWord_7716409).sum := by decide
  have hdescent : baseEnd_7716409 < baseStart_7716409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716432 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 6]
def baseStart_7716432 : Nat := 118140960795 + 7716432 * 2 ^ 59
def prefixEnd_7716432 : Nat := 4983230072969 + 3 ^ 40 * 7716432 * 2
def baseEnd_7716432 : Nat := 440248728192739850890309

theorem tailTrace_7716432 : CollatzResearch.WordTrace tailWord_7716432 prefixEnd_7716432 440248728192739850890309 := by
  unfold tailWord_7716432
  simp only [CollatzResearch.WordTrace]
  refine ⟨140720698190346100255191775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187627597587128133673589033 140720698190346100255191775)
  ·
    refine ⟨211081047285519150382787663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140720698190346100255191775 211081047285519150382787663)
    ·
      refine ⟨316621570928278725574181495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211081047285519150382787663 316621570928278725574181495)
      ·
        refine ⟨474932356392418088361272243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316621570928278725574181495 474932356392418088361272243)
        ·
          refine ⟨712398534588627132541908365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474932356392418088361272243 712398534588627132541908365)
          ·
            refine ⟨267149450470735174703215637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712398534588627132541908365 267149450470735174703215637)
            ·
              refine ⟨12522630490815711314213233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267149450470735174703215637 12522630490815711314213233)
              ·
                refine ⟨9391972868111783485659925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522630490815711314213233 9391972868111783485659925)
                ·
                  refine ⟨440248728192739850890309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9391972868111783485659925 440248728192739850890309)
                  ·
                    rfl

theorem cell23_7716432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_7716432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716432 prefixEnd_7716432 := by exact prefixLift 7716432
  have htrace : WordTrace (prefixWord ++ tailWord_7716432) baseStart_7716432 baseEnd_7716432 := by
    simpa [prefixWord, tailWord_7716432, baseEnd_7716432] using wordTrace_append hprefix tailTrace_7716432
  have hstable : (prefixWord ++ tailWord_7716432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716432).length < 2 ^ (prefixWord ++ tailWord_7716432).sum := by decide
  have hdescent : baseEnd_7716432 < baseStart_7716432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716436 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_7716436 : Nat := 118140960795 + 7716436 * 2 ^ 59
def prefixEnd_7716436 : Nat := 4983230072969 + 3 ^ 40 * 7716436 * 2
def baseEnd_7716436 : Nat := 1320746869219092214120921

theorem tailTrace_7716436 : CollatzResearch.WordTrace tailWord_7716436 prefixEnd_7716436 1320746869219092214120921 := by
  unfold tailWord_7716436
  simp only [CollatzResearch.WordTrace]
  refine ⟨140720771136338854596764581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187627694848451806129019441 140720771136338854596764581)
  ·
    refine ⟨26385144588063535236893359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140720771136338854596764581 26385144588063535236893359)
    ·
      refine ⟨39577716882095302855340039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26385144588063535236893359 39577716882095302855340039)
      ·
        refine ⟨59366575323142954283010059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39577716882095302855340039 59366575323142954283010059)
        ·
          refine ⟨89049862984714431424515089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59366575323142954283010059 89049862984714431424515089)
          ·
            refine ⟨66787397238535823568386317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89049862984714431424515089 66787397238535823568386317)
            ·
              refine ⟨25045273964450933838144869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66787397238535823568386317 25045273964450933838144869)
              ·
                refine ⟨4695988868334550094652163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25045273964450933838144869 4695988868334550094652163)
                ·
                  refine ⟨7043983302501825141978245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695988868334550094652163 7043983302501825141978245)
                  ·
                    refine ⟨1320746869219092214120921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7043983302501825141978245 1320746869219092214120921)
                    ·
                      rfl

theorem cell23_7716436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_7716436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716436 prefixEnd_7716436 := by exact prefixLift 7716436
  have htrace : WordTrace (prefixWord ++ tailWord_7716436) baseStart_7716436 baseEnd_7716436 := by
    simpa [prefixWord, tailWord_7716436, baseEnd_7716436] using wordTrace_append hprefix tailTrace_7716436
  have hstable : (prefixWord ++ tailWord_7716436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716436).length < 2 ^ (prefixWord ++ tailWord_7716436).sum := by decide
  have hdescent : baseEnd_7716436 < baseStart_7716436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716516 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_7716516 : Nat := 118140960795 + 7716516 * 2 ^ 59
def prefixEnd_7716516 : Nat := 4983230072969 + 3 ^ 40 * 7716516 * 2
def baseEnd_7716516 : Nat := 3962281686109636329362395

theorem tailTrace_7716516 : CollatzResearch.WordTrace tailWord_7716516 prefixEnd_7716516 3962281686109636329362395 := by
  unfold tailWord_7716516
  simp only [CollatzResearch.WordTrace]
  refine ⟨140722230056193941428220701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187629640074925255237627601 140722230056193941428220701)
  ·
    refine ⟨52770836271072728035582763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140722230056193941428220701 52770836271072728035582763)
    ·
      refine ⟨79156254406609092053374145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52770836271072728035582763 79156254406609092053374145)
      ·
        refine ⟨59367190804956819040030609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79156254406609092053374145 59367190804956819040030609)
        ·
          refine ⟨44525393103717614280022957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59367190804956819040030609 44525393103717614280022957)
          ·
            refine ⟨16697022413894105355008609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44525393103717614280022957 16697022413894105355008609)
            ·
              refine ⟨12522766810420579016256457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16697022413894105355008609 12522766810420579016256457)
              ·
                refine ⟨9392075107815434262192343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522766810420579016256457 9392075107815434262192343)
                ·
                  refine ⟨14088112661723151393288515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9392075107815434262192343 14088112661723151393288515)
                  ·
                    refine ⟨21132168992584727089932773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14088112661723151393288515 21132168992584727089932773)
                    ·
                      refine ⟨3962281686109636329362395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21132168992584727089932773 3962281686109636329362395)
                      ·
                        rfl

theorem cell23_7716516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_7716516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716516 prefixEnd_7716516 := by exact prefixLift 7716516
  have htrace : WordTrace (prefixWord ++ tailWord_7716516) baseStart_7716516 baseEnd_7716516 := by
    simpa [prefixWord, tailWord_7716516, baseEnd_7716516] using wordTrace_append hprefix tailTrace_7716516
  have hstable : (prefixWord ++ tailWord_7716516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716516).length < 2 ^ (prefixWord ++ tailWord_7716516).sum := by decide
  have hdescent : baseEnd_7716516 < baseStart_7716516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716552 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_7716552 : Nat := 118140960795 + 7716552 * 2 ^ 59
def prefixEnd_7716552 : Nat := 4983230072969 + 3 ^ 40 * 7716552 * 2
def baseEnd_7716552 : Nat := 1320766723804399396170743

theorem tailTrace_7716552 : CollatzResearch.WordTrace tailWord_7716552 prefixEnd_7716552 1320766723804399396170743 := by
  unfold tailWord_7716552
  simp only [CollatzResearch.WordTrace]
  refine ⟨140722886570128730502375955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187630515426838307336501273 140722886570128730502375955)
  ·
    refine ⟨211084329855193095753563933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140722886570128730502375955 211084329855193095753563933)
    ·
      refine ⟨79156623695697410907586475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211084329855193095753563933 79156623695697410907586475)
      ·
        refine ⟨118734935543546116361379713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79156623695697410907586475 118734935543546116361379713)
        ·
          refine ⟨89051201657659587271034785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118734935543546116361379713 89051201657659587271034785)
          ·
            refine ⟨66788401243244690453276089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89051201657659587271034785 66788401243244690453276089)
            ·
              refine ⟨50091300932433517839957067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66788401243244690453276089 50091300932433517839957067)
              ·
                refine ⟨75136951398650276759935601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50091300932433517839957067 75136951398650276759935601)
                ·
                  refine ⟨56352713548987707569951701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75136951398650276759935601 56352713548987707569951701)
                  ·
                    refine ⟨1320766723804399396170743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56352713548987707569951701 1320766723804399396170743)
                    ·
                      rfl

theorem cell23_7716552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_7716552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716552 prefixEnd_7716552 := by exact prefixLift 7716552
  have htrace : WordTrace (prefixWord ++ tailWord_7716552) baseStart_7716552 baseEnd_7716552 := by
    simpa [prefixWord, tailWord_7716552, baseEnd_7716552] using wordTrace_append hprefix tailTrace_7716552
  have hstable : (prefixWord ++ tailWord_7716552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716552).length < 2 ^ (prefixWord ++ tailWord_7716552).sum := by decide
  have hdescent : baseEnd_7716552 < baseStart_7716552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716583 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7716583 : Nat := 118140960795 + 7716583 * 2 ^ 59
def prefixEnd_7716583 : Nat := 4983230072969 + 3 ^ 40 * 7716583 * 2
def baseEnd_7716583 : Nat := 3962316089313487567224587

theorem tailTrace_7716583 : CollatzResearch.WordTrace tailWord_7716583 prefixEnd_7716583 3962316089313487567224587 := by
  unfold tailWord_7716583
  simp only [CollatzResearch.WordTrace]
  refine ⟨281446903803145153299130403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187631269202096768866086935 281446903803145153299130403)
  ·
    refine ⟨422170355704717729948695605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281446903803145153299130403 422170355704717729948695605)
    ·
      refine ⟨39578470847317287182690213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422170355704717729948695605 39578470847317287182690213)
      ·
        refine ⟨7420963283871991346754415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39578470847317287182690213 7420963283871991346754415)
        ·
          refine ⟨11131444925807987020131623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420963283871991346754415 11131444925807987020131623)
          ·
            refine ⟨16697167388711980530197435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131444925807987020131623 16697167388711980530197435)
            ·
              refine ⟨25045751083067970795296153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16697167388711980530197435 25045751083067970795296153)
              ·
                refine ⟨18784313312300978096472115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25045751083067970795296153 18784313312300978096472115)
                ·
                  refine ⟨28176469968451467144708173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18784313312300978096472115 28176469968451467144708173)
                  ·
                    refine ⟨10566176238169300179265565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28176469968451467144708173 10566176238169300179265565)
                    ·
                      refine ⟨3962316089313487567224587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566176238169300179265565 3962316089313487567224587)
                      ·
                        rfl

theorem cell23_7716583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7716583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716583 prefixEnd_7716583 := by exact prefixLift 7716583
  have htrace : WordTrace (prefixWord ++ tailWord_7716583) baseStart_7716583 baseEnd_7716583 := by
    simpa [prefixWord, tailWord_7716583, baseEnd_7716583] using wordTrace_append hprefix tailTrace_7716583
  have hstable : (prefixWord ++ tailWord_7716583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716583).length < 2 ^ (prefixWord ++ tailWord_7716583).sum := by decide
  have hdescent : baseEnd_7716583 < baseStart_7716583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716592 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_7716592 : Nat := 118140960795 + 7716592 * 2 ^ 59
def prefixEnd_7716592 : Nat := 4983230072969 + 3 ^ 40 * 7716592 * 2
def baseEnd_7716592 : Nat := 3962320710639378032012045

theorem tailTrace_7716592 : CollatzResearch.WordTrace tailWord_7716592 prefixEnd_7716592 3962320710639378032012045 := by
  unfold tailWord_7716592
  simp only [CollatzResearch.WordTrace]
  refine ⟨140723616030056273918104015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187631488040075031890805353 140723616030056273918104015)
  ·
    refine ⟨211085424045084410877156023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140723616030056273918104015 211085424045084410877156023)
    ·
      refine ⟨316628136067626616315734035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211085424045084410877156023 316628136067626616315734035)
      ·
        refine ⟨474942204101439924473601053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316628136067626616315734035 474942204101439924473601053)
        ·
          refine ⟨178103326538039971677600395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474942204101439924473601053 178103326538039971677600395)
          ·
            refine ⟨267154989807059957516400593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178103326538039971677600395 267154989807059957516400593)
            ·
              refine ⟨200366242355294968137300445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267154989807059957516400593 200366242355294968137300445)
              ·
                refine ⟨75137340883235613051487667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200366242355294968137300445 75137340883235613051487667)
                ·
                  refine ⟨112706011324853419577231501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75137340883235613051487667 112706011324853419577231501)
                  ·
                    refine ⟨42264754246820032341461813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112706011324853419577231501 42264754246820032341461813)
                    ·
                      refine ⟨3962320710639378032012045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42264754246820032341461813 3962320710639378032012045)
                      ·
                        rfl

theorem cell23_7716592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_7716592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716592 prefixEnd_7716592 := by exact prefixLift 7716592
  have htrace : WordTrace (prefixWord ++ tailWord_7716592) baseStart_7716592 baseEnd_7716592 := by
    simpa [prefixWord, tailWord_7716592, baseEnd_7716592] using wordTrace_append hprefix tailTrace_7716592
  have hstable : (prefixWord ++ tailWord_7716592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716592).length < 2 ^ (prefixWord ++ tailWord_7716592).sum := by decide
  have hdescent : baseEnd_7716592 < baseStart_7716592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716602 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_7716602 : Nat := 118140960795 + 7716602 * 2 ^ 59
def prefixEnd_7716602 : Nat := 4983230072969 + 3 ^ 40 * 7716602 * 2
def baseEnd_7716602 : Nat := 3962325845445922992886999

theorem tailTrace_7716602 : CollatzResearch.WordTrace tailWord_7716602 prefixEnd_7716602 3962325845445922992886999 := by
  unfold tailWord_7716602
  simp only [CollatzResearch.WordTrace]
  refine ⟨70361899197519079886018015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187631731193384213029381373 70361899197519079886018015)
  ·
    refine ⟨105542848796278619829027023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70361899197519079886018015 105542848796278619829027023)
    ·
      refine ⟨158314273194417929743540535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105542848796278619829027023 158314273194417929743540535)
      ·
        refine ⟨237471409791626894615310803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158314273194417929743540535 237471409791626894615310803)
        ·
          refine ⟨356207114687440341922966205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237471409791626894615310803 356207114687440341922966205)
          ·
            refine ⟨133577668007790128221112327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356207114687440341922966205 133577668007790128221112327)
            ·
              refine ⟨200366502011685192331668491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133577668007790128221112327 200366502011685192331668491)
              ·
                refine ⟨300549753017527788497502737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200366502011685192331668491 300549753017527788497502737)
                ·
                  refine ⟨225412314763145841373127053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300549753017527788497502737 225412314763145841373127053)
                  ·
                    refine ⟨84529618036179690514922645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225412314763145841373127053 84529618036179690514922645)
                    ·
                      refine ⟨3962325845445922992886999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84529618036179690514922645 3962325845445922992886999)
                      ·
                        rfl

theorem cell23_7716602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_7716602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716602 prefixEnd_7716602 := by exact prefixLift 7716602
  have htrace : WordTrace (prefixWord ++ tailWord_7716602) baseStart_7716602 baseEnd_7716602 := by
    simpa [prefixWord, tailWord_7716602, baseEnd_7716602] using wordTrace_append hprefix tailTrace_7716602
  have hstable : (prefixWord ++ tailWord_7716602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716602).length < 2 ^ (prefixWord ++ tailWord_7716602).sum := by decide
  have hdescent : baseEnd_7716602 < baseStart_7716602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716609 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_7716609 : Nat := 118140960795 + 7716609 * 2 ^ 59
def prefixEnd_7716609 : Nat := 4983230072969 + 3 ^ 40 * 7716609 * 2
def baseEnd_7716609 : Nat := 3962329439810504465499467

theorem tailTrace_7716609 : CollatzResearch.WordTrace tailWord_7716609 prefixEnd_7716609 3962329439810504465499467 := by
  unfold tailWord_7716609
  simp only [CollatzResearch.WordTrace]
  refine ⟨281447852101050959739576881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187631901400700639826384587 281447852101050959739576881)
  ·
    refine ⟨211085889075788219804682661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281447852101050959739576881 211085889075788219804682661)
    ·
      refine ⟨39578604201710291213377999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211085889075788219804682661 39578604201710291213377999)
      ·
        refine ⟨59367906302565436820066999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39578604201710291213377999 59367906302565436820066999)
        ·
          refine ⟨89051859453848155230100499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59367906302565436820066999 89051859453848155230100499)
          ·
            refine ⟨133577789180772232845150749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89051859453848155230100499 133577789180772232845150749)
            ·
              refine ⟨50091670942789587316931531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133577789180772232845150749 50091670942789587316931531)
              ·
                refine ⟨75137506414184380975397297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50091670942789587316931531 75137506414184380975397297)
                ·
                  refine ⟨56353129810638285731547973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75137506414184380975397297 56353129810638285731547973)
                  ·
                    refine ⟨10566211839494678574665245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56353129810638285731547973 10566211839494678574665245)
                    ·
                      refine ⟨3962329439810504465499467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566211839494678574665245 3962329439810504465499467)
                      ·
                        rfl

theorem cell23_7716609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_7716609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716609 prefixEnd_7716609 := by exact prefixLift 7716609
  have htrace : WordTrace (prefixWord ++ tailWord_7716609) baseStart_7716609 baseEnd_7716609 := by
    simpa [prefixWord, tailWord_7716609, baseEnd_7716609] using wordTrace_append hprefix tailTrace_7716609
  have hstable : (prefixWord ++ tailWord_7716609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716609).length < 2 ^ (prefixWord ++ tailWord_7716609).sum := by decide
  have hdescent : baseEnd_7716609 < baseStart_7716609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716614 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7716614 : Nat := 118140960795 + 7716614 * 2 ^ 59
def prefixEnd_7716614 : Nat := 4983230072969 + 3 ^ 40 * 7716614 * 2
def baseEnd_7716614 : Nat := 3962332007213776945936945

theorem tailTrace_7716614 : CollatzResearch.WordTrace tailWord_7716614 prefixEnd_7716614 3962332007213776945936945 := by
  unfold tailWord_7716614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795251077063526424797153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187632022977355230395672597 8795251077063526424797153)
  ·
    refine ⟨6596438307797644818597865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8795251077063526424797153 6596438307797644818597865)
    ·
      refine ⟨4947328730848233613948399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6596438307797644818597865 4947328730848233613948399)
      ·
        refine ⟨7420993096272350420922599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947328730848233613948399 7420993096272350420922599)
        ·
          refine ⟨11131489644408525631383899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420993096272350420922599 11131489644408525631383899)
          ·
            refine ⟨16697234466612788447075849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131489644408525631383899 16697234466612788447075849)
            ·
              refine ⟨12522925849959591335306887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16697234466612788447075849 12522925849959591335306887)
              ·
                refine ⟨18784388774939387002960331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522925849959591335306887 18784388774939387002960331)
                ·
                  refine ⟨28176583162409080504440497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18784388774939387002960331 28176583162409080504440497)
                  ·
                    refine ⟨21132437371806810378330373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28176583162409080504440497 21132437371806810378330373)
                    ·
                      refine ⟨3962332007213776945936945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21132437371806810378330373 3962332007213776945936945)
                      ·
                        rfl

theorem cell23_7716614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7716614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716614 prefixEnd_7716614 := by exact prefixLift 7716614
  have htrace : WordTrace (prefixWord ++ tailWord_7716614) baseStart_7716614 baseEnd_7716614 := by
    simpa [prefixWord, tailWord_7716614, baseEnd_7716614] using wordTrace_append hprefix tailTrace_7716614
  have hstable : (prefixWord ++ tailWord_7716614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716614).length < 2 ^ (prefixWord ++ tailWord_7716614).sum := by decide
  have hdescent : baseEnd_7716614 < baseStart_7716614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716629 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 7]
def baseStart_7716629 : Nat := 118140960795 + 7716629 * 2 ^ 59
def prefixEnd_7716629 : Nat := 4983230072969 + 3 ^ 40 * 7716629 * 2
def baseEnd_7716629 : Nat := 440259967713732709694375

theorem tailTrace_7716629 : CollatzResearch.WordTrace tailWord_7716629 prefixEnd_7716629 440259967713732709694375 := by
  unfold tailWord_7716629
  simp only [CollatzResearch.WordTrace]
  refine ⟨281448581560978503155304941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187632387707319002103536627 281448581560978503155304941)
  ·
    refine ⟨105543218085366938683239353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281448581560978503155304941 105543218085366938683239353)
    ·
      refine ⟨79157413564025204012429515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105543218085366938683239353 79157413564025204012429515)
      ·
        refine ⟨118736120346037806018644273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79157413564025204012429515 118736120346037806018644273)
        ·
          refine ⟨89052090259528354513983205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118736120346037806018644273 89052090259528354513983205)
          ·
            refine ⟨16697266923661566471371851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89052090259528354513983205 16697266923661566471371851)
            ·
              refine ⟨25045900385492349707057777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16697266923661566471371851 25045900385492349707057777)
              ·
                refine ⟨18784425289119262280293333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25045900385492349707057777 18784425289119262280293333)
                ·
                  refine ⟨440259967713732709694375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18784425289119262280293333 440259967713732709694375)
                  ·
                    rfl

theorem cell23_7716629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_7716629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716629 prefixEnd_7716629 := by exact prefixLift 7716629
  have htrace : WordTrace (prefixWord ++ tailWord_7716629) baseStart_7716629 baseEnd_7716629 := by
    simpa [prefixWord, tailWord_7716629, baseEnd_7716629] using wordTrace_append hprefix tailTrace_7716629
  have hstable : (prefixWord ++ tailWord_7716629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716629).length < 2 ^ (prefixWord ++ tailWord_7716629).sum := by decide
  have hdescent : baseEnd_7716629 < baseStart_7716629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716639 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_7716639 : Nat := 118140960795 + 7716639 * 2 ^ 59
def prefixEnd_7716639 : Nat := 4983230072969 + 3 ^ 40 * 7716639 * 2
def baseEnd_7716639 : Nat := 3962344844230139348124329

theorem tailTrace_7716639 : CollatzResearch.WordTrace tailWord_7716639 prefixEnd_7716639 3962344844230139348124329 := by
  unfold tailWord_7716639
  simp only [CollatzResearch.WordTrace]
  refine ⟨281448946290942274863168971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187632630860628183242112647 281448946290942274863168971)
  ·
    refine ⟨422173419436413412294753457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281448946290942274863168971 422173419436413412294753457)
    ·
      refine ⟨316630064577310059221065093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422173419436413412294753457 316630064577310059221065093)
      ·
        refine ⟨59368137108245636103949705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316630064577310059221065093 59368137108245636103949705)
        ·
          refine ⟨44526102831184227077962279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59368137108245636103949705 44526102831184227077962279)
          ·
            refine ⟨66789154246776340616943419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44526102831184227077962279 66789154246776340616943419)
            ·
              refine ⟨100183731370164510925415129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66789154246776340616943419 100183731370164510925415129)
              ·
                refine ⟨75137798527623383194061347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100183731370164510925415129 75137798527623383194061347)
                ·
                  refine ⟨112706697791435074791092021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75137798527623383194061347 112706697791435074791092021)
                  ·
                    refine ⟨10566252917947038261664877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112706697791435074791092021 10566252917947038261664877)
                    ·
                      refine ⟨3962344844230139348124329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566252917947038261664877 3962344844230139348124329)
                      ·
                        rfl

theorem cell23_7716639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_7716639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716639 prefixEnd_7716639 := by exact prefixLift 7716639
  have htrace : WordTrace (prefixWord ++ tailWord_7716639) baseStart_7716639 baseEnd_7716639 := by
    simpa [prefixWord, tailWord_7716639, baseEnd_7716639] using wordTrace_append hprefix tailTrace_7716639
  have hstable : (prefixWord ++ tailWord_7716639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716639).length < 2 ^ (prefixWord ++ tailWord_7716639).sum := by decide
  have hdescent : baseEnd_7716639 < baseStart_7716639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716679 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_7716679 : Nat := 118140960795 + 7716679 * 2 ^ 59
def prefixEnd_7716679 : Nat := 4983230072969 + 3 ^ 40 * 7716679 * 2
def baseEnd_7716679 : Nat := 3962365383456319191624145

theorem tailTrace_7716679 : CollatzResearch.WordTrace tailWord_7716679 prefixEnd_7716679 3962365383456319191624145 := by
  unfold tailWord_7716679
  simp only [CollatzResearch.WordTrace]
  refine ⟨281450405210797361694625091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187633603473864907796416727 281450405210797361694625091)
  ·
    refine ⟨422175607816196042541937637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281450405210797361694625091 422175607816196042541937637)
    ·
      refine ⟨79157926465536757976613307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422175607816196042541937637 79157926465536757976613307)
      ·
        refine ⟨118736889698305136964919961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79157926465536757976613307 118736889698305136964919961)
        ·
          refine ⟨89052667273728852723689971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118736889698305136964919961 89052667273728852723689971)
          ·
            refine ⟨133579000910593279085534957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89052667273728852723689971 133579000910593279085534957)
            ·
              refine ⟨50092125341472479657075609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133579000910593279085534957 50092125341472479657075609)
              ·
                refine ⟨37569094006104359742806707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50092125341472479657075609 37569094006104359742806707)
                ·
                  refine ⟨56353641009156539614210061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37569094006104359742806707 56353641009156539614210061)
                  ·
                    refine ⟨21132615378433702355328773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56353641009156539614210061 21132615378433702355328773)
                    ·
                      refine ⟨3962365383456319191624145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21132615378433702355328773 3962365383456319191624145)
                      ·
                        rfl

theorem cell23_7716679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_7716679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716679 prefixEnd_7716679 := by exact prefixLift 7716679
  have htrace : WordTrace (prefixWord ++ tailWord_7716679) baseStart_7716679 baseEnd_7716679 := by
    simpa [prefixWord, tailWord_7716679, baseEnd_7716679] using wordTrace_append hprefix tailTrace_7716679
  have hstable : (prefixWord ++ tailWord_7716679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716679).length < 2 ^ (prefixWord ++ tailWord_7716679).sum := by decide
  have hdescent : baseEnd_7716679 < baseStart_7716679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716716 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_7716716 : Nat := 118140960795 + 7716716 * 2 ^ 59
def prefixEnd_7716716 : Nat := 4983230072969 + 3 ^ 40 * 7716716 * 2
def baseEnd_7716716 : Nat := 3962384382240535546861475

theorem tailTrace_7716716 : CollatzResearch.WordTrace tailWord_7716716 prefixEnd_7716716 3962384382240535546861475 := by
  unfold tailWord_7716716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140725877355831658506861001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187634503141108878009148001 140725877355831658506861001)
  ·
    refine ⟨105544408016873743880145751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140725877355831658506861001 105544408016873743880145751)
    ·
      refine ⟨158316612025310615820218627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105544408016873743880145751 158316612025310615820218627)
      ·
        refine ⟨237474918037965923730327941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158316612025310615820218627 237474918037965923730327941)
        ·
          refine ⟨44526547132118610699436489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237474918037965923730327941 44526547132118610699436489)
          ·
            refine ⟨33394910349088958024577367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44526547132118610699436489 33394910349088958024577367)
            ·
              refine ⟨50092365523633437036866051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33394910349088958024577367 50092365523633437036866051)
              ·
                refine ⟨75138548285450155555299077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50092365523633437036866051 75138548285450155555299077)
                ·
                  refine ⟨14088477803521904166618577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75138548285450155555299077 14088477803521904166618577)
                  ·
                    refine ⟨10566358352641428124963933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14088477803521904166618577 10566358352641428124963933)
                    ·
                      refine ⟨3962384382240535546861475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566358352641428124963933 3962384382240535546861475)
                      ·
                        rfl

theorem cell23_7716716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_7716716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716716 prefixEnd_7716716 := by exact prefixLift 7716716
  have htrace : WordTrace (prefixWord ++ tailWord_7716716) baseStart_7716716 baseEnd_7716716 := by
    simpa [prefixWord, tailWord_7716716, baseEnd_7716716] using wordTrace_append hprefix tailTrace_7716716
  have hstable : (prefixWord ++ tailWord_7716716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716716).length < 2 ^ (prefixWord ++ tailWord_7716716).sum := by decide
  have hdescent : baseEnd_7716716 < baseStart_7716716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716816 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_7716816 : Nat := 118140960795 + 7716816 * 2 ^ 59
def prefixEnd_7716816 : Nat := 4983230072969 + 3 ^ 40 * 7716816 * 2
def baseEnd_7716816 : Nat := 3962435730305985155611015

theorem tailTrace_7716816 : CollatzResearch.WordTrace tailWord_7716816 prefixEnd_7716816 3962435730305985155611015 := by
  unfold tailWord_7716816
  simp only [CollatzResearch.WordTrace]
  refine ⟨140727701005650517046181151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187636934674200689394908201 140727701005650517046181151)
  ·
    refine ⟨211091551508475775569271727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140727701005650517046181151 211091551508475775569271727)
    ·
      refine ⟨316637327262713663353907591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211091551508475775569271727 316637327262713663353907591)
      ·
        refine ⟨474955990894070495030861387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316637327262713663353907591 474955990894070495030861387)
        ·
          refine ⟨712433986341105742546292081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474955990894070495030861387 712433986341105742546292081)
          ·
            refine ⟨534325489755829306909719061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712433986341105742546292081 534325489755829306909719061)
            ·
              refine ⟨25046507332304498761393081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 534325489755829306909719061 25046507332304498761393081)
              ·
                refine ⟨18784880499228374071044811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25046507332304498761393081 18784880499228374071044811)
                ·
                  refine ⟨28177320748842561106567217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18784880499228374071044811 28177320748842561106567217)
                  ·
                    refine ⟨21132990561631920829925413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28177320748842561106567217 21132990561631920829925413)
                    ·
                      refine ⟨3962435730305985155611015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21132990561631920829925413 3962435730305985155611015)
                      ·
                        rfl

theorem cell23_7716816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_7716816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716816 prefixEnd_7716816 := by exact prefixLift 7716816
  have htrace : WordTrace (prefixWord ++ tailWord_7716816) baseStart_7716816 baseEnd_7716816 := by
    simpa [prefixWord, tailWord_7716816, baseEnd_7716816] using wordTrace_append hprefix tailTrace_7716816
  have hstable : (prefixWord ++ tailWord_7716816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716816).length < 2 ^ (prefixWord ++ tailWord_7716816).sum := by decide
  have hdescent : baseEnd_7716816 < baseStart_7716816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716820 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_7716820 : Nat := 118140960795 + 7716820 * 2 ^ 59
def prefixEnd_7716820 : Nat := 4983230072969 + 3 ^ 40 * 7716820 * 2
def baseEnd_7716820 : Nat := 3962437784228603139960997

theorem tailTrace_7716820 : CollatzResearch.WordTrace tailWord_7716820 prefixEnd_7716820 3962437784228603139960997 := by
  unfold tailWord_7716820
  simp only [CollatzResearch.WordTrace]
  refine ⟨140727773951643271387753957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187637031935524361850338609 140727773951643271387753957)
  ·
    refine ⟨26386457615933113385203867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140727773951643271387753957 26386457615933113385203867)
    ·
      refine ⟨39579686423899670077805801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26386457615933113385203867 39579686423899670077805801)
      ·
        refine ⟨29684764817924752558354351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39579686423899670077805801 29684764817924752558354351)
        ·
          refine ⟨44527147226887128837531527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684764817924752558354351 44527147226887128837531527)
          ·
            refine ⟨66790720840330693256297291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44527147226887128837531527 66790720840330693256297291)
            ·
              refine ⟨100186081260496039884445937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66790720840330693256297291 100186081260496039884445937)
              ·
                refine ⟨75139560945372029913334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100186081260496039884445937 75139560945372029913334453)
                ·
                  refine ⟨7044333838628627804375105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75139560945372029913334453 7044333838628627804375105)
                  ·
                    refine ⟨5283250378971470853281329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7044333838628627804375105 5283250378971470853281329)
                    ·
                      refine ⟨3962437784228603139960997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5283250378971470853281329 3962437784228603139960997)
                      ·
                        rfl

theorem cell23_7716820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_7716820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716820 prefixEnd_7716820 := by exact prefixLift 7716820
  have htrace : WordTrace (prefixWord ++ tailWord_7716820) baseStart_7716820 baseEnd_7716820 := by
    simpa [prefixWord, tailWord_7716820, baseEnd_7716820] using wordTrace_append hprefix tailTrace_7716820
  have hstable : (prefixWord ++ tailWord_7716820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716820).length < 2 ^ (prefixWord ++ tailWord_7716820).sum := by decide
  have hdescent : baseEnd_7716820 < baseStart_7716820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716823 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_7716823 : Nat := 118140960795 + 7716823 * 2 ^ 59
def prefixEnd_7716823 : Nat := 4983230072969 + 3 ^ 40 * 7716823 * 2
def baseEnd_7716823 : Nat := 3962439324670566628223483

theorem tailTrace_7716823 : CollatzResearch.WordTrace tailWord_7716823 prefixEnd_7716823 3962439324670566628223483 := by
  unfold tailWord_7716823
  simp only [CollatzResearch.WordTrace]
  refine ⟨281455657322275674287867123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187637104881517116191911415 281455657322275674287867123)
  ·
    refine ⟨422183485983413511431800685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281455657322275674287867123 422183485983413511431800685)
    ·
      refine ⟨158318807243780066786925257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422183485983413511431800685 158318807243780066786925257)
      ·
        refine ⟨118739105432835050090193943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158318807243780066786925257 118739105432835050090193943)
        ·
          refine ⟨178108658149252575135290915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118739105432835050090193943 178108658149252575135290915)
          ·
            refine ⟨267162987223878862702936373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178108658149252575135290915 267162987223878862702936373)
            ·
              refine ⟨25046530052238643378400285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267162987223878862702936373 25046530052238643378400285)
              ·
                refine ⟨9392448769589491266900107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25046530052238643378400285 9392448769589491266900107)
                ·
                  refine ⟨14088673154384236900350161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9392448769589491266900107 14088673154384236900350161)
                  ·
                    refine ⟨10566504865788177675262621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14088673154384236900350161 10566504865788177675262621)
                    ·
                      refine ⟨3962439324670566628223483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566504865788177675262621 3962439324670566628223483)
                      ·
                        rfl

theorem cell23_7716823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_7716823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716823 prefixEnd_7716823 := by exact prefixLift 7716823
  have htrace : WordTrace (prefixWord ++ tailWord_7716823) baseStart_7716823 baseEnd_7716823 := by
    simpa [prefixWord, tailWord_7716823, baseEnd_7716823] using wordTrace_append hprefix tailTrace_7716823
  have hstable : (prefixWord ++ tailWord_7716823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716823).length < 2 ^ (prefixWord ++ tailWord_7716823).sum := by decide
  have hdescent : baseEnd_7716823 < baseStart_7716823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716826 : List Nat := [3, 1, 1, 2, 5, 1, 10]
def baseStart_7716826 : Nat := 118140960795 + 7716826 * 2 ^ 59
def prefixEnd_7716826 : Nat := 4983230072969 + 3 ^ 40 * 7716826 * 2
def baseEnd_7716826 : Nat := 48919023026080618722049

theorem tailTrace_7716826 : CollatzResearch.WordTrace tailWord_7716826 prefixEnd_7716826 48919023026080618722049 := by
  unfold tailWord_7716826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70363941685316201450056583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187637177827509870533484221 70363941685316201450056583)
  ·
    refine ⟨105545912527974302175084875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70363941685316201450056583 105545912527974302175084875)
    ·
      refine ⟨158318868791961453262627313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105545912527974302175084875 158318868791961453262627313)
      ·
        refine ⟨118739151593971089946970485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158318868791961453262627313 118739151593971089946970485)
        ·
          refine ⟨11131795461934789682528483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118739151593971089946970485 11131795461934789682528483)
          ·
            refine ⟨16697693192902184523792725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131795461934789682528483 16697693192902184523792725)
            ·
              refine ⟨48919023026080618722049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16697693192902184523792725 48919023026080618722049)
              ·
                rfl

theorem cell23_7716826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 10].length) (baseStart_7716826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716826 prefixEnd_7716826 := by exact prefixLift 7716826
  have htrace : WordTrace (prefixWord ++ tailWord_7716826) baseStart_7716826 baseEnd_7716826 := by
    simpa [prefixWord, tailWord_7716826, baseEnd_7716826] using wordTrace_append hprefix tailTrace_7716826
  have hstable : (prefixWord ++ tailWord_7716826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716826).length < 2 ^ (prefixWord ++ tailWord_7716826).sum := by decide
  have hdescent : baseEnd_7716826 < baseStart_7716826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716863 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 3, 3, 2]
def baseStart_7716863 : Nat := 118140960795 + 7716863 * 2 ^ 59
def prefixEnd_7716863 : Nat := 4983230072969 + 3 ^ 40 * 7716863 * 2
def baseEnd_7716863 : Nat := 3962459863896746471723299

theorem tailTrace_7716863 : CollatzResearch.WordTrace tailWord_7716863 prefixEnd_7716863 3962459863896746471723299 := by
  unfold tailWord_7716863
  simp only [CollatzResearch.WordTrace]
  refine ⟨281457116242130761119323243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187638077494753840746215495 281457116242130761119323243)
  ·
    refine ⟨422185674363196141678984865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281457116242130761119323243 422185674363196141678984865)
    ·
      refine ⟨316639255772397106259238649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422185674363196141678984865 316639255772397106259238649)
      ·
        refine ⟨237479441829297829694428987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316639255772397106259238649 237479441829297829694428987)
        ·
          refine ⟨356219162743946744541643481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237479441829297829694428987 356219162743946744541643481)
          ·
            refine ⟨267164372057960058406232611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356219162743946744541643481 267164372057960058406232611)
            ·
              refine ⟨400746558086940087609348917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267164372057960058406232611 400746558086940087609348917)
              ·
                refine ⟨37569989820650633213376461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400746558086940087609348917 37569989820650633213376461)
                ·
                  refine ⟨14088746182743987455016173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37569989820650633213376461 14088746182743987455016173)
                  ·
                    refine ⟨5283279818528995295631065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14088746182743987455016173 5283279818528995295631065)
                    ·
                      refine ⟨3962459863896746471723299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5283279818528995295631065 3962459863896746471723299)
                      ·
                        rfl

theorem cell23_7716863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_7716863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716863 prefixEnd_7716863 := by exact prefixLift 7716863
  have htrace : WordTrace (prefixWord ++ tailWord_7716863) baseStart_7716863 baseEnd_7716863 := by
    simpa [prefixWord, tailWord_7716863, baseEnd_7716863] using wordTrace_append hprefix tailTrace_7716863
  have hstable : (prefixWord ++ tailWord_7716863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716863).length < 2 ^ (prefixWord ++ tailWord_7716863).sum := by decide
  have hdescent : baseEnd_7716863 < baseStart_7716863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716877 : List Nat := [1, 7, 1, 2, 1, 2, 9]
def baseStart_7716877 : Nat := 118140960795 + 7716877 * 2 ^ 59
def prefixEnd_7716877 : Nat := 4983230072969 + 3 ^ 40 * 7716877 * 2
def baseEnd_7716877 : Nat := 48919346328714931073435

theorem tailTrace_7716877 : CollatzResearch.WordTrace tailWord_7716877 prefixEnd_7716877 48919346328714931073435 := by
  unfold tailWord_7716877
  simp only [CollatzResearch.WordTrace]
  refine ⟨281457626864080041510332885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187638417909386694340221923 281457626864080041510332885)
  ·
    refine ⟨6596663129626875972898427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 281457626864080041510332885 6596663129626875972898427)
    ·
      refine ⟨9894994694440313959347641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596663129626875972898427 9894994694440313959347641)
      ·
        refine ⟨7421246020830235469510731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9894994694440313959347641 7421246020830235469510731)
        ·
          refine ⟨11131869031245353204266097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421246020830235469510731 11131869031245353204266097)
          ·
            refine ⟨8348901773434014903199573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11131869031245353204266097 8348901773434014903199573)
            ·
              refine ⟨48919346328714931073435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8348901773434014903199573 48919346328714931073435)
              ·
                rfl

theorem cell23_7716877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 9].length) (baseStart_7716877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716877 prefixEnd_7716877 := by exact prefixLift 7716877
  have htrace : WordTrace (prefixWord ++ tailWord_7716877) baseStart_7716877 baseEnd_7716877 := by
    simpa [prefixWord, tailWord_7716877, baseEnd_7716877] using wordTrace_append hprefix tailTrace_7716877
  have hstable : (prefixWord ++ tailWord_7716877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716877).length < 2 ^ (prefixWord ++ tailWord_7716877).sum := by decide
  have hdescent : baseEnd_7716877 < baseStart_7716877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716904 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7716904 : Nat := 118140960795 + 7716904 * 2 ^ 59
def prefixEnd_7716904 : Nat := 4983230072969 + 3 ^ 40 * 7716904 * 2
def baseEnd_7716904 : Nat := 3962480916603580811310611

theorem tailTrace_7716904 : CollatzResearch.WordTrace tailWord_7716904 prefixEnd_7716904 3962480916603580811310611 := by
  unfold tailWord_7716904
  simp only [CollatzResearch.WordTrace]
  refine ⟨140729305817491112560782883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187639074423321483414377177 140729305817491112560782883)
  ·
    refine ⟨211093958726236668841174325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140729305817491112560782883 211093958726236668841174325)
    ·
      refine ⟨19790058630584687703860093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211093958726236668841174325 19790058630584687703860093)
      ·
        refine ⟨7421271986469257888947535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19790058630584687703860093 7421271986469257888947535)
        ·
          refine ⟨11131907979703886833421303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421271986469257888947535 11131907979703886833421303)
          ·
            refine ⟨16697861969555830250131955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131907979703886833421303 16697861969555830250131955)
            ·
              refine ⟨25046792954333745375197933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16697861969555830250131955 25046792954333745375197933)
              ·
                refine ⟨9392547357875154515699225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25046792954333745375197933 9392547357875154515699225)
                ·
                  refine ⟨7044410518406365886774419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9392547357875154515699225 7044410518406365886774419)
                  ·
                    refine ⟨10566615777609548830161629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7044410518406365886774419 10566615777609548830161629)
                    ·
                      refine ⟨3962480916603580811310611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566615777609548830161629 3962480916603580811310611)
                      ·
                        rfl

theorem cell23_7716904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7716904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716904 prefixEnd_7716904 := by exact prefixLift 7716904
  have htrace : WordTrace (prefixWord ++ tailWord_7716904) baseStart_7716904 baseEnd_7716904 := by
    simpa [prefixWord, tailWord_7716904, baseEnd_7716904] using wordTrace_append hprefix tailTrace_7716904
  have hstable : (prefixWord ++ tailWord_7716904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716904).length < 2 ^ (prefixWord ++ tailWord_7716904).sum := by decide
  have hdescent : baseEnd_7716904 < baseStart_7716904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716933 : List Nat := [1, 3, 1, 1, 1, 3, 1, 7, 5]
def baseStart_7716933 : Nat := 118140960795 + 7716933 * 2 ^ 59
def prefixEnd_7716933 : Nat := 4983230072969 + 3 ^ 40 * 7716933 * 2
def baseEnd_7716933 : Nat := 440277311949173466427553

theorem tailTrace_7716933 : CollatzResearch.WordTrace tailWord_7716933 prefixEnd_7716933 440277311949173466427553 := by
  unfold tailWord_7716933
  simp only [CollatzResearch.WordTrace]
  refine ⟨281459669351877163074371453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187639779567918108716247635 281459669351877163074371453)
  ·
    refine ⟨105547376006953936152889295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281459669351877163074371453 105547376006953936152889295)
    ·
      refine ⟨158321064010430904229333943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105547376006953936152889295 158321064010430904229333943)
      ·
        refine ⟨237481596015646356344000915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158321064010430904229333943 237481596015646356344000915)
        ·
          refine ⟨356222394023469534516001373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237481596015646356344000915 356222394023469534516001373)
          ·
            refine ⟨133583397758801075443500515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356222394023469534516001373 133583397758801075443500515)
            ·
              refine ⟨200375096638201613165250773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133583397758801075443500515 200375096638201613165250773)
              ·
                refine ⟨4696291327457850308560565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 200375096638201613165250773 4696291327457850308560565)
                ·
                  refine ⟨440277311949173466427553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696291327457850308560565 440277311949173466427553)
                  ·
                    rfl

theorem cell23_7716933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_7716933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716933 prefixEnd_7716933 := by exact prefixLift 7716933
  have htrace : WordTrace (prefixWord ++ tailWord_7716933) baseStart_7716933 baseEnd_7716933 := by
    simpa [prefixWord, tailWord_7716933, baseEnd_7716933] using wordTrace_append hprefix tailTrace_7716933
  have hstable : (prefixWord ++ tailWord_7716933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716933).length < 2 ^ (prefixWord ++ tailWord_7716933).sum := by decide
  have hdescent : baseEnd_7716933 < baseStart_7716933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716953 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 7, 2]
def baseStart_7716953 : Nat := 118140960795 + 7716953 * 2 ^ 59
def prefixEnd_7716953 : Nat := 4983230072969 + 3 ^ 40 * 7716953 * 2
def baseEnd_7716953 : Nat := 3962506077155651119597885

theorem tailTrace_7716953 : CollatzResearch.WordTrace tailWord_7716953 prefixEnd_7716953 3962506077155651119597885 := by
  unfold tailWord_7716953
  simp only [CollatzResearch.WordTrace]
  refine ⟨281460398811804706490099513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187640265874536470993399675 281460398811804706490099513)
  ·
    refine ⟨211095299108853529867574635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281460398811804706490099513 211095299108853529867574635)
    ·
      refine ⟨316642948663280294801361953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211095299108853529867574635 316642948663280294801361953)
      ·
        refine ⟨237482211497460221101021465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316642948663280294801361953 237482211497460221101021465)
        ·
          refine ⟨178111658623095165825766099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237482211497460221101021465 178111658623095165825766099)
          ·
            refine ⟨267167487934642748738649149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178111658623095165825766099 267167487934642748738649149)
            ·
              refine ⟨100187807975491030776993431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267167487934642748738649149 100187807975491030776993431)
              ·
                refine ⟨150281711963236546165490147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100187807975491030776993431 150281711963236546165490147)
                ·
                  refine ⟨225422567944854819248235221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150281711963236546165490147 225422567944854819248235221)
                  ·
                    refine ⟨5283341436207534826130513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225422567944854819248235221 5283341436207534826130513)
                    ·
                      refine ⟨3962506077155651119597885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5283341436207534826130513 3962506077155651119597885)
                      ·
                        rfl

theorem cell23_7716953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_7716953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716953 prefixEnd_7716953 := by exact prefixLift 7716953
  have htrace : WordTrace (prefixWord ++ tailWord_7716953) baseStart_7716953 baseEnd_7716953 := by
    simpa [prefixWord, tailWord_7716953, baseEnd_7716953] using wordTrace_append hprefix tailTrace_7716953
  have hstable : (prefixWord ++ tailWord_7716953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716953).length < 2 ^ (prefixWord ++ tailWord_7716953).sum := by decide
  have hdescent : baseEnd_7716953 < baseStart_7716953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7716983 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_7716983 : Nat := 118140960795 + 7716983 * 2 ^ 59
def prefixEnd_7716983 : Nat := 4983230072969 + 3 ^ 40 * 7716983 * 2
def baseEnd_7716983 : Nat := 3962521481575286002222747

theorem tailTrace_7716983 : CollatzResearch.WordTrace tailWord_7716983 prefixEnd_7716983 3962521481575286002222747 := by
  unfold tailWord_7716983
  simp only [CollatzResearch.WordTrace]
  refine ⟨281461493001696021613691603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187640995334464014409127735 281461493001696021613691603)
  ·
    refine ⟨422192239502544032420537405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281461493001696021613691603 422192239502544032420537405)
    ·
      refine ⟨158322089813454012157701527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422192239502544032420537405 158322089813454012157701527)
      ·
        refine ⟨237483134720181018236552291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158322089813454012157701527 237483134720181018236552291)
        ·
          refine ⟨356224702080271527354828437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237483134720181018236552291 356224702080271527354828437)
          ·
            refine ⟨16698032910012727844757583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356224702080271527354828437 16698032910012727844757583)
            ·
              refine ⟨25047049365019091767136375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16698032910012727844757583 25047049365019091767136375)
              ·
                refine ⟨37570574047528637650704563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25047049365019091767136375 37570574047528637650704563)
                ·
                  refine ⟨56355861071292956476056845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37570574047528637650704563 56355861071292956476056845)
                  ·
                    refine ⟨21133447901734858678521317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56355861071292956476056845 21133447901734858678521317)
                    ·
                      refine ⟨3962521481575286002222747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21133447901734858678521317 3962521481575286002222747)
                      ·
                        rfl

theorem cell23_7716983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_7716983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7716983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7716983 prefixEnd_7716983 := by exact prefixLift 7716983
  have htrace : WordTrace (prefixWord ++ tailWord_7716983) baseStart_7716983 baseEnd_7716983 := by
    simpa [prefixWord, tailWord_7716983, baseEnd_7716983] using wordTrace_append hprefix tailTrace_7716983
  have hstable : (prefixWord ++ tailWord_7716983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7716983).length < 2 ^ (prefixWord ++ tailWord_7716983).sum := by decide
  have hdescent : baseEnd_7716983 < baseStart_7716983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7716983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717050 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_7717050 : Nat := 118140960795 + 7717050 * 2 ^ 59
def prefixEnd_7717050 : Nat := 4983230072969 + 3 ^ 40 * 7717050 * 2
def baseEnd_7717050 : Nat := 3962555884779137240084939

theorem tailTrace_7717050 : CollatzResearch.WordTrace tailWord_7717050 prefixEnd_7717050 3962555884779137240084939 := by
  unfold tailWord_7717050
  simp only [CollatzResearch.WordTrace]
  refine ⟨70365984173113323014095151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187642624461635528037587069 70365984173113323014095151)
  ·
    refine ⟨105548976259669984521142727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70365984173113323014095151 105548976259669984521142727)
    ·
      refine ⟨158323464389504976781714091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105548976259669984521142727 158323464389504976781714091)
      ·
        refine ⟨237485196584257465172571137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158323464389504976781714091 237485196584257465172571137)
        ·
          refine ⟨178113897438193098879428353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237485196584257465172571137 178113897438193098879428353)
          ·
            refine ⟨133585423078644824159571265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178113897438193098879428353 133585423078644824159571265)
            ·
              refine ⟨100189067308983618119678449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133585423078644824159571265 100189067308983618119678449)
              ·
                refine ⟨75141800481737713589758837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100189067308983618119678449 75141800481737713589758837)
                ·
                  refine ⟨7044543795162910649039891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75141800481737713589758837 7044543795162910649039891)
                  ·
                    refine ⟨10566815692744365973559837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7044543795162910649039891 10566815692744365973559837)
                    ·
                      refine ⟨3962555884779137240084939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10566815692744365973559837 3962555884779137240084939)
                      ·
                        rfl

theorem cell23_7717050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_7717050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717050 prefixEnd_7717050 := by exact prefixLift 7717050
  have htrace : WordTrace (prefixWord ++ tailWord_7717050) baseStart_7717050 baseEnd_7717050 := by
    simpa [prefixWord, tailWord_7717050, baseEnd_7717050] using wordTrace_append hprefix tailTrace_7717050
  have hstable : (prefixWord ++ tailWord_7717050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717050).length < 2 ^ (prefixWord ++ tailWord_7717050).sum := by decide
  have hdescent : baseEnd_7717050 < baseStart_7717050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717053 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_7717053 : Nat := 118140960795 + 7717053 * 2 ^ 59
def prefixEnd_7717053 : Nat := 4983230072969 + 3 ^ 40 * 7717053 * 2
def baseEnd_7717053 : Nat := 1320852475073700242782475

theorem tailTrace_7717053 : CollatzResearch.WordTrace tailWord_7717053 prefixEnd_7717053 1320852475073700242782475 := by
  unfold tailWord_7717053
  simp only [CollatzResearch.WordTrace]
  refine ⟨281464046111442423568739813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187642697407628282379159875 281464046111442423568739813)
  ·
    refine ⟨52774508645895454419138715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281464046111442423568739813 52774508645895454419138715)
    ·
      refine ⟨79161762968843181628708073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52774508645895454419138715 79161762968843181628708073)
      ·
        refine ⟨59371322226632386221531055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79161762968843181628708073 59371322226632386221531055)
        ·
          refine ⟨89056983339948579332296583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59371322226632386221531055 89056983339948579332296583)
          ·
            refine ⟨133585475009922868998444875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89056983339948579332296583 133585475009922868998444875)
            ·
              refine ⟨200378212514884303497667313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133585475009922868998444875 200378212514884303497667313)
              ·
                refine ⟨150283659386163227623250485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200378212514884303497667313 150283659386163227623250485)
                ·
                  refine ⟨14089093067452802589679733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150283659386163227623250485 14089093067452802589679733)
                  ·
                    refine ⟨1320852475073700242782475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14089093067452802589679733 1320852475073700242782475)
                    ·
                      rfl

theorem cell23_7717053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_7717053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717053 prefixEnd_7717053 := by exact prefixLift 7717053
  have htrace : WordTrace (prefixWord ++ tailWord_7717053) baseStart_7717053 baseEnd_7717053 := by
    simpa [prefixWord, tailWord_7717053, baseEnd_7717053] using wordTrace_append hprefix tailTrace_7717053
  have hstable : (prefixWord ++ tailWord_7717053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717053).length < 2 ^ (prefixWord ++ tailWord_7717053).sum := by decide
  have hdescent : baseEnd_7717053 < baseStart_7717053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717107 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 1, 1, 4]
def baseStart_7717107 : Nat := 118140960795 + 7717107 * 2 ^ 59
def prefixEnd_7717107 : Nat := 4983230072969 + 3 ^ 40 * 7717107 * 2
def baseEnd_7717107 : Nat := 3962585153176443517072177

theorem tailTrace_7717107 : CollatzResearch.WordTrace tailWord_7717107 prefixEnd_7717107 3962585153176443517072177 := by
  unfold tailWord_7717107
  simp only [CollatzResearch.WordTrace]
  refine ⟨281466015653246790791205575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187644010435497860527470383 281466015653246790791205575)
  ·
    refine ⟨422199023479870186186808363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281466015653246790791205575 422199023479870186186808363)
    ·
      refine ⟨633298535219805279280212545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422199023479870186186808363 633298535219805279280212545)
      ·
        refine ⟨474973901414853959460159409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633298535219805279280212545 474973901414853959460159409)
        ·
          refine ⟨356230426061140469595119557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474973901414853959460159409 356230426061140469595119557)
          ·
            refine ⟨66793204886463838049084917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356230426061140469595119557 66793204886463838049084917)
            ·
              refine ⟨6261862958105984817101711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66793204886463838049084917 6261862958105984817101711)
              ·
                refine ⟨9392794437158977225652567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261862958105984817101711 9392794437158977225652567)
                ·
                  refine ⟨14089191655738465838478851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9392794437158977225652567 14089191655738465838478851)
                  ·
                    refine ⟨21133787483607698757718277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14089191655738465838478851 21133787483607698757718277)
                    ·
                      refine ⟨3962585153176443517072177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21133787483607698757718277 3962585153176443517072177)
                      ·
                        rfl

theorem cell23_7717107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 1, 4].length) (baseStart_7717107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717107 prefixEnd_7717107 := by exact prefixLift 7717107
  have htrace : WordTrace (prefixWord ++ tailWord_7717107) baseStart_7717107 baseEnd_7717107 := by
    simpa [prefixWord, tailWord_7717107, baseEnd_7717107] using wordTrace_append hprefix tailTrace_7717107
  have hstable : (prefixWord ++ tailWord_7717107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717107).length < 2 ^ (prefixWord ++ tailWord_7717107).sum := by decide
  have hdescent : baseEnd_7717107 < baseStart_7717107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717203 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 9]
def baseStart_7717203 : Nat := 118140960795 + 7717203 * 2 ^ 59
def prefixEnd_7717203 : Nat := 4983230072969 + 3 ^ 40 * 7717203 * 2
def baseEnd_7717203 : Nat := 440292716368808349052415

theorem tailTrace_7717203 : CollatzResearch.WordTrace tailWord_7717203 prefixEnd_7717203 440292716368808349052415 := by
  unfold tailWord_7717203
  simp only [CollatzResearch.WordTrace]
  refine ⟨281469517060898999186700263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187646344707265999457800175 281469517060898999186700263)
  ·
    refine ⟨422204275591348498780050395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281469517060898999186700263 422204275591348498780050395)
    ·
      refine ⟨633306413387022748170075593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422204275591348498780050395 633306413387022748170075593)
      ·
        refine ⟨474979810040267061127556695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633306413387022748170075593 474979810040267061127556695)
        ·
          refine ⟨712469715060400591691335043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474979810040267061127556695 712469715060400591691335043)
          ·
            refine ⟨1068704572590600887537002565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712469715060400591691335043 1068704572590600887537002565)
            ·
              refine ⟨200382107360737666413187981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1068704572590600887537002565 200382107360737666413187981)
              ·
                refine ⟨75143290260276624904945493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200382107360737666413187981 75143290260276624904945493)
                ·
                  refine ⟨440292716368808349052415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75143290260276624904945493 440292716368808349052415)
                  ·
                    rfl

theorem cell23_7717203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 9].length) (baseStart_7717203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717203 prefixEnd_7717203 := by exact prefixLift 7717203
  have htrace : WordTrace (prefixWord ++ tailWord_7717203) baseStart_7717203 baseEnd_7717203 := by
    simpa [prefixWord, tailWord_7717203, baseEnd_7717203] using wordTrace_append hprefix tailTrace_7717203
  have hstable : (prefixWord ++ tailWord_7717203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717203).length < 2 ^ (prefixWord ++ tailWord_7717203).sum := by decide
  have hdescent : baseEnd_7717203 < baseStart_7717203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717237 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 7]
def baseStart_7717237 : Nat := 118140960795 + 7717237 * 2 ^ 59
def prefixEnd_7717237 : Nat := 4983230072969 + 3 ^ 40 * 7717237 * 2
def baseEnd_7717237 : Nat := 440294656184614223160731

theorem tailTrace_7717237 : CollatzResearch.WordTrace tailWord_7717237 prefixEnd_7717237 440294656184614223160731 := by
  unfold tailWord_7717237
  simp only [CollatzResearch.WordTrace]
  refine ⟨281470757142775822993437965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187647171428517215328958643 281470757142775822993437965)
  ·
    refine ⟨105551533928540933622539237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281470757142775822993437965 105551533928540933622539237)
    ·
      refine ⟨19790912611601425054226107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105551533928540933622539237 19790912611601425054226107)
      ·
        refine ⟨29686368917402137581339161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19790912611601425054226107 29686368917402137581339161)
        ·
          refine ⟨22264776688051603186004371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29686368917402137581339161 22264776688051603186004371)
          ·
            refine ⟨33397165032077404779006557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22264776688051603186004371 33397165032077404779006557)
            ·
              refine ⟨12523936887029026792127459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33397165032077404779006557 12523936887029026792127459)
              ·
                refine ⟨18785905330543540188191189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12523936887029026792127459 18785905330543540188191189)
                ·
                  refine ⟨440294656184614223160731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18785905330543540188191189 440294656184614223160731)
                  ·
                    rfl

theorem cell23_7717237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_7717237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717237 prefixEnd_7717237 := by exact prefixLift 7717237
  have htrace : WordTrace (prefixWord ++ tailWord_7717237) baseStart_7717237 baseEnd_7717237 := by
    simpa [prefixWord, tailWord_7717237, baseEnd_7717237] using wordTrace_append hprefix tailTrace_7717237
  have hstable : (prefixWord ++ tailWord_7717237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717237).length < 2 ^ (prefixWord ++ tailWord_7717237).sum := by decide
  have hdescent : baseEnd_7717237 < baseStart_7717237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717288 : List Nat := [2, 1, 6, 1, 1, 3, 2, 2, 5]
def baseStart_7717288 : Nat := 118140960795 + 7717288 * 2 ^ 59
def prefixEnd_7717288 : Nat := 4983230072969 + 3 ^ 40 * 7717288 * 2
def baseEnd_7717288 : Nat := 440297565908323034323205

theorem tailTrace_7717288 : CollatzResearch.WordTrace tailWord_7717288 prefixEnd_7717288 440297565908323034323205 := by
  unfold tailWord_7717288
  simp only [CollatzResearch.WordTrace]
  refine ⟨140736308632795529351772259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187648411510394039135696345 140736308632795529351772259)
  ·
    refine ⟨211104462949193294027658389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140736308632795529351772259 211104462949193294027658389)
    ·
      refine ⟨9895521700743435657546487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211104462949193294027658389 9895521700743435657546487)
      ·
        refine ⟨14843282551115153486319731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895521700743435657546487 14843282551115153486319731)
        ·
          refine ⟨22264923826672730229479597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14843282551115153486319731 22264923826672730229479597)
          ·
            refine ⟨8349346435002273836054849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22264923826672730229479597 8349346435002273836054849)
            ·
              refine ⟨6262009826251705377041137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8349346435002273836054849 6262009826251705377041137)
              ·
                refine ⟨4696507369688779032780853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262009826251705377041137 4696507369688779032780853)
                ·
                  refine ⟨440297565908323034323205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4696507369688779032780853 440297565908323034323205)
                  ·
                    rfl

theorem cell23_7717288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 5].length) (baseStart_7717288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717288 prefixEnd_7717288 := by exact prefixLift 7717288
  have htrace : WordTrace (prefixWord ++ tailWord_7717288) baseStart_7717288 baseEnd_7717288 := by
    simpa [prefixWord, tailWord_7717288, baseEnd_7717288] using wordTrace_append hprefix tailTrace_7717288
  have hstable : (prefixWord ++ tailWord_7717288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717288).length < 2 ^ (prefixWord ++ tailWord_7717288).sum := by decide
  have hdescent : baseEnd_7717288 < baseStart_7717288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717324 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7717324 : Nat := 118140960795 + 7717324 * 2 ^ 59
def prefixEnd_7717324 : Nat := 4983230072969 + 3 ^ 40 * 7717324 * 2
def baseEnd_7717324 : Nat := 3962696578478469168058679

theorem tailTrace_7717324 : CollatzResearch.WordTrace tailWord_7717324 prefixEnd_7717324 3962696578478469168058679 := by
  unfold tailWord_7717324
  simp only [CollatzResearch.WordTrace]
  refine ⟨140736965146730318425927513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187649286862307091234570017 140736965146730318425927513)
  ·
    refine ⟨105552723860047738819445635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140736965146730318425927513 105552723860047738819445635)
    ·
      refine ⟨158329085790071608229168453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105552723860047738819445635 158329085790071608229168453)
      ·
        refine ⟨29686703585638426542969085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158329085790071608229168453 29686703585638426542969085)
        ·
          refine ⟨11132513844614409953613407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29686703585638426542969085 11132513844614409953613407)
          ·
            refine ⟨16698770766921614930420111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132513844614409953613407 16698770766921614930420111)
            ·
              refine ⟨25048156150382422395630167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16698770766921614930420111 25048156150382422395630167)
              ·
                refine ⟨37572234225573633593445251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25048156150382422395630167 37572234225573633593445251)
                ·
                  refine ⟨56358351338360450390167877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37572234225573633593445251 56358351338360450390167877)
                  ·
                    refine ⟨10567190875942584448156477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56358351338360450390167877 10567190875942584448156477)
                    ·
                      refine ⟨3962696578478469168058679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567190875942584448156477 3962696578478469168058679)
                      ·
                        rfl

theorem cell23_7717324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7717324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717324 prefixEnd_7717324 := by exact prefixLift 7717324
  have htrace : WordTrace (prefixWord ++ tailWord_7717324) baseStart_7717324 baseEnd_7717324 := by
    simpa [prefixWord, tailWord_7717324, baseEnd_7717324] using wordTrace_append hprefix tailTrace_7717324
  have hstable : (prefixWord ++ tailWord_7717324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717324).length < 2 ^ (prefixWord ++ tailWord_7717324).sum := by decide
  have hdescent : baseEnd_7717324 < baseStart_7717324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717382 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7717382 : Nat := 118140960795 + 7717382 * 2 ^ 59
def prefixEnd_7717382 : Nat := 4983230072969 + 3 ^ 40 * 7717382 * 2
def baseEnd_7717382 : Nat := 1320908786785476647044471

theorem tailTrace_7717382 : CollatzResearch.WordTrace tailWord_7717382 prefixEnd_7717382 1320908786785476647044471 := by
  unfold tailWord_7717382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796126428976578523670825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187650697151500341838310933 8796126428976578523670825)
  ·
    refine ⟨6597094821732433892753119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8796126428976578523670825 6597094821732433892753119)
    ·
      refine ⟨9895642232598650839129679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597094821732433892753119 9895642232598650839129679)
      ·
        refine ⟨14843463348897976258694519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895642232598650839129679 14843463348897976258694519)
        ·
          refine ⟨22265195023346964388041779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14843463348897976258694519 22265195023346964388041779)
          ·
            refine ⟨33397792535020446582062669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22265195023346964388041779 33397792535020446582062669)
            ·
              refine ⟨12524172200632667468273501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33397792535020446582062669 12524172200632667468273501)
              ·
                refine ⟨4696564575237250300602563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12524172200632667468273501 4696564575237250300602563)
                ·
                  refine ⟨7044846862855875450903845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696564575237250300602563 7044846862855875450903845)
                  ·
                    refine ⟨1320908786785476647044471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044846862855875450903845 1320908786785476647044471)
                    ·
                      rfl

theorem cell23_7717382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7717382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717382 prefixEnd_7717382 := by exact prefixLift 7717382
  have htrace : WordTrace (prefixWord ++ tailWord_7717382) baseStart_7717382 baseEnd_7717382 := by
    simpa [prefixWord, tailWord_7717382, baseEnd_7717382] using wordTrace_append hprefix tailTrace_7717382
  have hstable : (prefixWord ++ tailWord_7717382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717382).length < 2 ^ (prefixWord ++ tailWord_7717382).sum := by decide
  have hdescent : baseEnd_7717382 < baseStart_7717382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717388 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 1, 1, 3]
def baseStart_7717388 : Nat := 118140960795 + 7717388 * 2 ^ 59
def prefixEnd_7717388 : Nat := 4983230072969 + 3 ^ 40 * 7717388 * 2
def baseEnd_7717388 : Nat := 3962729441240356917658385

theorem tailTrace_7717388 : CollatzResearch.WordTrace tailWord_7717388 prefixEnd_7717388 3962729441240356917658385 := by
  unfold tailWord_7717388
  simp only [CollatzResearch.WordTrace]
  refine ⟨140738132282614387891092409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187650843043485850521456545 140738132282614387891092409)
  ·
    refine ⟨105553599211960790918319307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140738132282614387891092409 105553599211960790918319307)
    ·
      refine ⟨158330398817941186377478961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105553599211960790918319307 158330398817941186377478961)
      ·
        refine ⟨118747799113455889783109221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158330398817941186377478961 118747799113455889783109221)
        ·
          refine ⟨22265212333772979334332979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118747799113455889783109221 22265212333772979334332979)
          ·
            refine ⟨33397818500659469001499469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22265212333772979334332979 33397818500659469001499469)
            ·
              refine ⟨12524181937747300875562301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33397818500659469001499469 12524181937747300875562301)
              ·
                refine ⟨4696568226655237828335863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12524181937747300875562301 4696568226655237828335863)
                ·
                  refine ⟨7044852339982856742503795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696568226655237828335863 7044852339982856742503795)
                  ·
                    refine ⟨10567278509974285113755693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7044852339982856742503795 10567278509974285113755693)
                    ·
                      refine ⟨3962729441240356917658385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567278509974285113755693 3962729441240356917658385)
                      ·
                        rfl

theorem cell23_7717388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_7717388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717388 prefixEnd_7717388 := by exact prefixLift 7717388
  have htrace : WordTrace (prefixWord ++ tailWord_7717388) baseStart_7717388 baseEnd_7717388 := by
    simpa [prefixWord, tailWord_7717388, baseEnd_7717388] using wordTrace_append hprefix tailTrace_7717388
  have hstable : (prefixWord ++ tailWord_7717388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717388).length < 2 ^ (prefixWord ++ tailWord_7717388).sum := by decide
  have hdescent : baseEnd_7717388 < baseStart_7717388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717404 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7717404 : Nat := 118140960795 + 7717404 * 2 ^ 59
def prefixEnd_7717404 : Nat := 4983230072969 + 3 ^ 40 * 7717404 * 2
def baseEnd_7717404 : Nat := 1320912552310276285019437

theorem tailTrace_7717404 : CollatzResearch.WordTrace tailWord_7717404 prefixEnd_7717404 1320912552310276285019437 := by
  unfold tailWord_7717404
  simp only [CollatzResearch.WordTrace]
  refine ⟨140738424066585405257383633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187651232088780540343178177 140738424066585405257383633)
  ·
    refine ⟨105553818049939053943037725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140738424066585405257383633 105553818049939053943037725)
    ·
      refine ⟨39582681768727145228639147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105553818049939053943037725 39582681768727145228639147)
      ·
        refine ⟨59374022653090717842958721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39582681768727145228639147 59374022653090717842958721)
        ·
          refine ⟨44530516989818038382219041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59374022653090717842958721 44530516989818038382219041)
          ·
            refine ⟨33397887742363528786664281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44530516989818038382219041 33397887742363528786664281)
            ·
              refine ⟨25048415806772646589998211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33397887742363528786664281 25048415806772646589998211)
              ·
                refine ⟨37572623710158969884997317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25048415806772646589998211 37572623710158969884997317)
                ·
                  refine ⟨7044866945654806853436997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37572623710158969884997317 7044866945654806853436997)
                  ·
                    refine ⟨1320912552310276285019437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7044866945654806853436997 1320912552310276285019437)
                    ·
                      rfl

theorem cell23_7717404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7717404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717404 prefixEnd_7717404 := by exact prefixLift 7717404
  have htrace : WordTrace (prefixWord ++ tailWord_7717404) baseStart_7717404 baseEnd_7717404 := by
    simpa [prefixWord, tailWord_7717404, baseEnd_7717404] using wordTrace_append hprefix tailTrace_7717404
  have hstable : (prefixWord ++ tailWord_7717404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717404).length < 2 ^ (prefixWord ++ tailWord_7717404).sum := by decide
  have hdescent : baseEnd_7717404 < baseStart_7717404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717405 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_7717405 : Nat := 118140960795 + 7717405 * 2 ^ 59
def prefixEnd_7717405 : Nat := 4983230072969 + 3 ^ 40 * 7717405 * 2
def baseEnd_7717405 : Nat := 3962738170411483351145807

theorem tailTrace_7717405 : CollatzResearch.WordTrace tailWord_7717405 prefixEnd_7717405 3962738170411483351145807 := by
  unfold tailWord_7717405
  simp only [CollatzResearch.WordTrace]
  refine ⟨281476884606167187685553669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187651256404111458457035779 281476884606167187685553669)
  ·
    refine ⟨52776915863656347691041313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281476884606167187685553669 52776915863656347691041313)
    ·
      refine ⟨39582686897742260768280985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52776915863656347691041313 39582686897742260768280985)
      ·
        refine ⟨29687015173306695576210739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39582686897742260768280985 29687015173306695576210739)
        ·
          refine ⟨44530522759960043364316109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29687015173306695576210739 44530522759960043364316109)
          ·
            refine ⟨16698946034985016261618541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44530522759960043364316109 16698946034985016261618541)
            ·
              refine ⟨6262104763119381098106953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16698946034985016261618541 6262104763119381098106953)
              ·
                refine ⟨4696578572339535823580215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262104763119381098106953 4696578572339535823580215)
                ·
                  refine ⟨7044867858509303735370323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696578572339535823580215 7044867858509303735370323)
                  ·
                    refine ⟨10567301787763955603055485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7044867858509303735370323 10567301787763955603055485)
                    ·
                      refine ⟨3962738170411483351145807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567301787763955603055485 3962738170411483351145807)
                      ·
                        rfl

theorem cell23_7717405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_7717405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717405 prefixEnd_7717405 := by exact prefixLift 7717405
  have htrace : WordTrace (prefixWord ++ tailWord_7717405) baseStart_7717405 baseEnd_7717405 := by
    simpa [prefixWord, tailWord_7717405, baseEnd_7717405] using wordTrace_append hprefix tailTrace_7717405
  have hstable : (prefixWord ++ tailWord_7717405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717405).length < 2 ^ (prefixWord ++ tailWord_7717405).sum := by decide
  have hdescent : baseEnd_7717405 < baseStart_7717405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717428 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7717428 : Nat := 118140960795 + 7717428 * 2 ^ 59
def prefixEnd_7717428 : Nat := 4983230072969 + 3 ^ 40 * 7717428 * 2
def baseEnd_7717428 : Nat := 3962749980466536761158201

theorem tailTrace_7717428 : CollatzResearch.WordTrace tailWord_7717428 prefixEnd_7717428 3962749980466536761158201 := by
  unfold tailWord_7717428
  simp only [CollatzResearch.WordTrace]
  refine ⟨140738861742541931306820469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187651815656722575075760625 140738861742541931306820469)
  ·
    refine ⟨13194268288363306060014419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140738861742541931306820469 13194268288363306060014419)
    ·
      refine ⟨19791402432544959090021629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13194268288363306060014419 19791402432544959090021629)
      ·
        refine ⟨7421775912204359658758111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19791402432544959090021629 7421775912204359658758111)
        ·
          refine ⟨11132663868306539488137167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421775912204359658758111 11132663868306539488137167)
          ·
            refine ⟨16698995802459809232205751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132663868306539488137167 16698995802459809232205751)
            ·
              refine ⟨25048493703689713848308627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16698995802459809232205751 25048493703689713848308627)
              ·
                refine ⟨37572740555534570772462941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25048493703689713848308627 37572740555534570772462941)
                ·
                  refine ⟨14089777708325464039673603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37572740555534570772462941 14089777708325464039673603)
                  ·
                    refine ⟨21134666562488196059510405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14089777708325464039673603 21134666562488196059510405)
                    ·
                      refine ⟨3962749980466536761158201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21134666562488196059510405 3962749980466536761158201)
                      ·
                        rfl

theorem cell23_7717428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7717428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717428 prefixEnd_7717428 := by exact prefixLift 7717428
  have htrace : WordTrace (prefixWord ++ tailWord_7717428) baseStart_7717428 baseEnd_7717428 := by
    simpa [prefixWord, tailWord_7717428, baseEnd_7717428] using wordTrace_append hprefix tailTrace_7717428
  have hstable : (prefixWord ++ tailWord_7717428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717428).length < 2 ^ (prefixWord ++ tailWord_7717428).sum := by decide
  have hdescent : baseEnd_7717428 < baseStart_7717428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717461 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7717461 : Nat := 118140960795 + 7717461 * 2 ^ 59
def prefixEnd_7717461 : Nat := 4983230072969 + 3 ^ 40 * 7717461 * 2
def baseEnd_7717461 : Nat := 3962766925328135132045549

theorem tailTrace_7717461 : CollatzResearch.WordTrace tailWord_7717461 prefixEnd_7717461 3962766925328135132045549 := by
  unfold tailWord_7717461
  simp only [CollatzResearch.WordTrace]
  refine ⟨281478927093964309249592237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187652618062642872833061491 281478927093964309249592237)
  ·
    refine ⟨105554597660236615968597089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281478927093964309249592237 105554597660236615968597089)
    ·
      refine ⟨79165948245177461976447817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105554597660236615968597089 79165948245177461976447817)
      ·
        refine ⟨59374461183883096482335863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79165948245177461976447817 59374461183883096482335863)
        ·
          refine ⟨89061691775824644723503795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59374461183883096482335863 89061691775824644723503795)
          ·
            refine ⟨133592537663736967085255693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89061691775824644723503795 133592537663736967085255693)
            ·
              refine ⟨50097201623901362656970885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133592537663736967085255693 50097201623901362656970885)
              ·
                refine ⟨9393225304481505498182041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50097201623901362656970885 9393225304481505498182041)
                ·
                  refine ⟨7044918978361129123636531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9393225304481505498182041 7044918978361129123636531)
                  ·
                    refine ⟨10567378467541693685454797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7044918978361129123636531 10567378467541693685454797)
                    ·
                      refine ⟨3962766925328135132045549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567378467541693685454797 3962766925328135132045549)
                      ·
                        rfl

theorem cell23_7717461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7717461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717461 prefixEnd_7717461 := by exact prefixLift 7717461
  have htrace : WordTrace (prefixWord ++ tailWord_7717461) baseStart_7717461 baseEnd_7717461 := by
    simpa [prefixWord, tailWord_7717461, baseEnd_7717461] using wordTrace_append hprefix tailTrace_7717461
  have hstable : (prefixWord ++ tailWord_7717461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717461).length < 2 ^ (prefixWord ++ tailWord_7717461).sum := by decide
  have hdescent : baseEnd_7717461 < baseStart_7717461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717487 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_7717487 : Nat := 118140960795 + 7717487 * 2 ^ 59
def prefixEnd_7717487 : Nat := 4983230072969 + 3 ^ 40 * 7717487 * 2
def baseEnd_7717487 : Nat := 3962780275825152030320429

theorem tailTrace_7717487 : CollatzResearch.WordTrace tailWord_7717487 prefixEnd_7717487 3962780275825152030320429 := by
  unfold tailWord_7717487
  simp only [CollatzResearch.WordTrace]
  refine ⟨281479875391870115690038715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187653250261246743793359143 281479875391870115690038715)
  ·
    refine ⟨422219813087805173535058073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281479875391870115690038715 422219813087805173535058073)
    ·
      refine ⟨316664859815853880151293555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422219813087805173535058073 316664859815853880151293555)
      ·
        refine ⟨474997289723780820226940333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316664859815853880151293555 474997289723780820226940333)
        ·
          refine ⟨178123983646417807585102625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474997289723780820226940333 178123983646417807585102625)
          ·
            refine ⟨133592987734813355688826969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178123983646417807585102625 133592987734813355688826969)
            ·
              refine ⟨100194740801110016766620227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133592987734813355688826969 100194740801110016766620227)
              ·
                refine ⟨150292111201665025149930341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100194740801110016766620227 150292111201665025149930341)
                ·
                  refine ⟨28179770850312192215611939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150292111201665025149930341 28179770850312192215611939)
                  ·
                    refine ⟨42269656275468288323417909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28179770850312192215611939 42269656275468288323417909)
                    ·
                      refine ⟨3962780275825152030320429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42269656275468288323417909 3962780275825152030320429)
                      ·
                        rfl

theorem cell23_7717487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_7717487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717487 prefixEnd_7717487 := by exact prefixLift 7717487
  have htrace : WordTrace (prefixWord ++ tailWord_7717487) baseStart_7717487 baseEnd_7717487 := by
    simpa [prefixWord, tailWord_7717487, baseEnd_7717487] using wordTrace_append hprefix tailTrace_7717487
  have hstable : (prefixWord ++ tailWord_7717487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717487).length < 2 ^ (prefixWord ++ tailWord_7717487).sum := by decide
  have hdescent : baseEnd_7717487 < baseStart_7717487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717518 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7717518 : Nat := 118140960795 + 7717518 * 2 ^ 59
def prefixEnd_7717518 : Nat := 4983230072969 + 3 ^ 40 * 7717518 * 2
def baseEnd_7717518 : Nat := 3962796193725441409032787

theorem tailTrace_7717518 : CollatzResearch.WordTrace tailWord_7717518 prefixEnd_7717518 3962796193725441409032787 := by
  unfold tailWord_7717518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185125756844725998052151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187654004036505205322944805 35185125756844725998052151)
  ·
    refine ⟨52777688635267088997078227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35185125756844725998052151 52777688635267088997078227)
    ·
      refine ⟨79166532952900633495617341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52777688635267088997078227 79166532952900633495617341)
      ·
        refine ⟨29687449857337737560856503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79166532952900633495617341 29687449857337737560856503)
        ·
          refine ⟨44531174786006606341284755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29687449857337737560856503 44531174786006606341284755)
          ·
            refine ⟨66796762179009909511927133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44531174786006606341284755 66796762179009909511927133)
            ·
              refine ⟨25048785817128716066972675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66796762179009909511927133 25048785817128716066972675)
              ·
                refine ⟨37573178725693074100459013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25048785817128716066972675 37573178725693074100459013)
                ·
                  refine ⟨7044971011067451393836065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37573178725693074100459013 7044971011067451393836065)
                  ·
                    refine ⟨5283728258300588545377049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7044971011067451393836065 5283728258300588545377049)
                    ·
                      refine ⟨3962796193725441409032787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5283728258300588545377049 3962796193725441409032787)
                      ·
                        rfl

theorem cell23_7717518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7717518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717518 prefixEnd_7717518 := by exact prefixLift 7717518
  have htrace : WordTrace (prefixWord ++ tailWord_7717518) baseStart_7717518 baseEnd_7717518 := by
    simpa [prefixWord, tailWord_7717518, baseEnd_7717518] using wordTrace_append hprefix tailTrace_7717518
  have hstable : (prefixWord ++ tailWord_7717518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717518).length < 2 ^ (prefixWord ++ tailWord_7717518).sum := by decide
  have hdescent : baseEnd_7717518 < baseStart_7717518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717554 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_7717554 : Nat := 118140960795 + 7717554 * 2 ^ 59
def prefixEnd_7717554 : Nat := 4983230072969 + 3 ^ 40 * 7717554 * 2
def baseEnd_7717554 : Nat := 1320938226343001089394207

theorem tailTrace_7717554 : CollatzResearch.WordTrace tailWord_7717554 prefixEnd_7717554 1320938226343001089394207 := by
  unfold tailWord_7717554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70370579770656846533181929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187654879388418257421818477 70370579770656846533181929)
  ·
    refine ⟨52777934827992634899886447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70370579770656846533181929 52777934827992634899886447)
    ·
      refine ⟨79166902241988952349829671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52777934827992634899886447 79166902241988952349829671)
      ·
        refine ⟨118750353362983428524744507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79166902241988952349829671 118750353362983428524744507)
        ·
          refine ⟨178125530044475142787116761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118750353362983428524744507 178125530044475142787116761)
          ·
            refine ⟨133594147533356357090337571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178125530044475142787116761 133594147533356357090337571)
            ·
              refine ⟨200391221300034535635506357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133594147533356357090337571 200391221300034535635506357)
              ·
                refine ⟨18786676996878237715828721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200391221300034535635506357 18786676996878237715828721)
                ·
                  refine ⟨14090007747658678286871541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18786676996878237715828721 14090007747658678286871541)
                  ·
                    refine ⟨1320938226343001089394207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14090007747658678286871541 1320938226343001089394207)
                    ·
                      rfl

theorem cell23_7717554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_7717554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717554 prefixEnd_7717554 := by exact prefixLift 7717554
  have htrace : WordTrace (prefixWord ++ tailWord_7717554) baseStart_7717554 baseEnd_7717554 := by
    simpa [prefixWord, tailWord_7717554, baseEnd_7717554] using wordTrace_append hprefix tailTrace_7717554
  have hstable : (prefixWord ++ tailWord_7717554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717554).length < 2 ^ (prefixWord ++ tailWord_7717554).sum := by decide
  have hdescent : baseEnd_7717554 < baseStart_7717554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717564 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7717564 : Nat := 118140960795 + 7717564 * 2 ^ 59
def prefixEnd_7717564 : Nat := 4983230072969 + 3 ^ 40 * 7717564 * 2
def baseEnd_7717564 : Nat := 3962819813835548229057575

theorem tailTrace_7717564 : CollatzResearch.WordTrace tailWord_7717564 prefixEnd_7717564 3962819813835548229057575 := by
  unfold tailWord_7717564
  simp only [CollatzResearch.WordTrace]
  refine ⟨140741341906295578920295873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187655122541727438560394497 140741341906295578920295873)
  ·
    refine ⟨105556006429721684190221905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140741341906295578920295873 105556006429721684190221905)
    ·
      refine ⟨79167004822291263142666429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105556006429721684190221905 79167004822291263142666429)
      ·
        refine ⟨29687626808359223678499911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79167004822291263142666429 29687626808359223678499911)
        ·
          refine ⟨44531440212538835517749867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29687626808359223678499911 44531440212538835517749867)
          ·
            refine ⟨66797160318808253276624801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44531440212538835517749867 66797160318808253276624801)
            ·
              refine ⟨50097870239106189957468601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66797160318808253276624801 50097870239106189957468601)
              ·
                refine ⟨37573402679329642468101451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50097870239106189957468601 37573402679329642468101451)
                ·
                  refine ⟨56360104018994463702152177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37573402679329642468101451 56360104018994463702152177)
                  ·
                    refine ⟨42270078014245847776614133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56360104018994463702152177 42270078014245847776614133)
                    ·
                      refine ⟨3962819813835548229057575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42270078014245847776614133 3962819813835548229057575)
                      ·
                        rfl

theorem cell23_7717564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7717564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717564 prefixEnd_7717564 := by exact prefixLift 7717564
  have htrace : WordTrace (prefixWord ++ tailWord_7717564) baseStart_7717564 baseEnd_7717564 := by
    simpa [prefixWord, tailWord_7717564, baseEnd_7717564] using wordTrace_append hprefix tailTrace_7717564
  have hstable : (prefixWord ++ tailWord_7717564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717564).length < 2 ^ (prefixWord ++ tailWord_7717564).sum := by decide
  have hdescent : baseEnd_7717564 < baseStart_7717564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717608 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7717608 : Nat := 118140960795 + 7717608 * 2 ^ 59
def prefixEnd_7717608 : Nat := 4983230072969 + 3 ^ 40 * 7717608 * 2
def baseEnd_7717608 : Nat := 3962842406984346056907373

theorem tailTrace_7717608 : CollatzResearch.WordTrace tailWord_7717608 prefixEnd_7717608 3962842406984346056907373 := by
  unfold tailWord_7717608
  simp only [CollatzResearch.WordTrace]
  refine ⟨140742144312215876677596739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187656192416287835570128985 140742144312215876677596739)
  ·
    refine ⟨211113216468323815016395109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140742144312215876677596739 211113216468323815016395109)
    ·
      refine ⟨39583728087810715315574083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211113216468323815016395109 39583728087810715315574083)
      ·
        refine ⟨59375592131716072973361125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39583728087810715315574083 59375592131716072973361125)
        ·
          refine ⟨11132923524696763682505211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59375592131716072973361125 11132923524696763682505211)
          ·
            refine ⟨16699385287045145523757817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132923524696763682505211 16699385287045145523757817)
            ·
              refine ⟨12524538965283859142818363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16699385287045145523757817 12524538965283859142818363)
              ·
                refine ⟨18786808447925788714227545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524538965283859142818363 18786808447925788714227545)
                ·
                  refine ⟨14090106335944341535670659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18786808447925788714227545 14090106335944341535670659)
                  ·
                    refine ⟨21135159503916512303505989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14090106335944341535670659 21135159503916512303505989)
                    ·
                      refine ⟨3962842406984346056907373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21135159503916512303505989 3962842406984346056907373)
                      ·
                        rfl

theorem cell23_7717608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7717608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717608 prefixEnd_7717608 := by exact prefixLift 7717608
  have htrace : WordTrace (prefixWord ++ tailWord_7717608) baseStart_7717608 baseEnd_7717608 := by
    simpa [prefixWord, tailWord_7717608, baseEnd_7717608] using wordTrace_append hprefix tailTrace_7717608
  have hstable : (prefixWord ++ tailWord_7717608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717608).length < 2 ^ (prefixWord ++ tailWord_7717608).sum := by decide
  have hdescent : baseEnd_7717608 < baseStart_7717608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717651 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 5, 2]
def baseStart_7717651 : Nat := 118140960795 + 7717651 * 2 ^ 59
def prefixEnd_7717651 : Nat := 4983230072969 + 3 ^ 40 * 7717651 * 2
def baseEnd_7717651 : Nat := 3962864486652489388669675

theorem tailTrace_7717651 : CollatzResearch.WordTrace tailWord_7717651 prefixEnd_7717651 3962864486652489388669675 := by
  unfold tailWord_7717651
  simp only [CollatzResearch.WordTrace]
  refine ⟨281485856963275971699008807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187657237975517314466005871 281485856963275971699008807)
  ·
    refine ⟨422228785444913957548513211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281485856963275971699008807 422228785444913957548513211)
    ·
      refine ⟨633343178167370936322769817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422228785444913957548513211 633343178167370936322769817)
      ·
        refine ⟨475007383625528202242077363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633343178167370936322769817 475007383625528202242077363)
        ·
          refine ⟨712511075438292303363116045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475007383625528202242077363 712511075438292303363116045)
          ·
            refine ⟨267191653289359613761168517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712511075438292303363116045 267191653289359613761168517)
            ·
              refine ⟨50098434991754927580219097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267191653289359613761168517 50098434991754927580219097)
              ·
                refine ⟨37573826243816195685164323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50098434991754927580219097 37573826243816195685164323)
                ·
                  refine ⟨56360739365724293527746485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37573826243816195685164323 56360739365724293527746485)
                  ·
                    refine ⟨5283819315536652518226233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56360739365724293527746485 5283819315536652518226233)
                    ·
                      refine ⟨3962864486652489388669675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5283819315536652518226233 3962864486652489388669675)
                      ·
                        rfl

theorem cell23_7717651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5, 2].length) (baseStart_7717651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717651 prefixEnd_7717651 := by exact prefixLift 7717651
  have htrace : WordTrace (prefixWord ++ tailWord_7717651) baseStart_7717651 baseEnd_7717651 := by
    simpa [prefixWord, tailWord_7717651, baseEnd_7717651] using wordTrace_append hprefix tailTrace_7717651
  have hstable : (prefixWord ++ tailWord_7717651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717651).length < 2 ^ (prefixWord ++ tailWord_7717651).sum := by decide
  have hdescent : baseEnd_7717651 < baseStart_7717651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717658 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_7717658 : Nat := 118140960795 + 7717658 * 2 ^ 59
def prefixEnd_7717658 : Nat := 4983230072969 + 3 ^ 40 * 7717658 * 2
def baseEnd_7717658 : Nat := 3962868081017070861282143

theorem tailTrace_7717658 : CollatzResearch.WordTrace tailWord_7717658 prefixEnd_7717658 3962868081017070861282143 := by
  unfold tailWord_7717658
  simp only [CollatzResearch.WordTrace]
  refine ⟨70371528068562652973628407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187657408182833741263009085 70371528068562652973628407)
  ·
    refine ⟨105557292102843979460442611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70371528068562652973628407 105557292102843979460442611)
    ·
      refine ⟨158335938154265969190663917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105557292102843979460442611 158335938154265969190663917)
      ·
        refine ⟨59375976807849738446498969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158335938154265969190663917 59375976807849738446498969)
        ·
          refine ⟨44531982605887303834874227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59375976807849738446498969 44531982605887303834874227)
          ·
            refine ⟨66797973908830955752311341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44531982605887303834874227 66797973908830955752311341)
            ·
              refine ⟨25049240215811608407116753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66797973908830955752311341 25049240215811608407116753)
              ·
                refine ⟨18786930161858706305337565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25049240215811608407116753 18786930161858706305337565)
                ·
                  refine ⟨7045098810697014864501587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18786930161858706305337565 7045098810697014864501587)
                  ·
                    refine ⟨10567648216045522296752381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045098810697014864501587 10567648216045522296752381)
                    ·
                      refine ⟨3962868081017070861282143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567648216045522296752381 3962868081017070861282143)
                      ·
                        rfl

theorem cell23_7717658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_7717658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717658 prefixEnd_7717658 := by exact prefixLift 7717658
  have htrace : WordTrace (prefixWord ++ tailWord_7717658) baseStart_7717658 baseEnd_7717658 := by
    simpa [prefixWord, tailWord_7717658, baseEnd_7717658] using wordTrace_append hprefix tailTrace_7717658
  have hstable : (prefixWord ++ tailWord_7717658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717658).length < 2 ^ (prefixWord ++ tailWord_7717658).sum := by decide
  have hdescent : baseEnd_7717658 < baseStart_7717658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717701 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_7717701 : Nat := 118140960795 + 7717701 * 2 ^ 59
def prefixEnd_7717701 : Nat := 4983230072969 + 3 ^ 40 * 7717701 * 2
def baseEnd_7717701 : Nat := 3962890160685214193044445

theorem tailTrace_7717701 : CollatzResearch.WordTrace tailWord_7717701 prefixEnd_7717701 3962890160685214193044445 := by
  unfold tailWord_7717701
  simp only [CollatzResearch.WordTrace]
  refine ⟨281487680613094830238328957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187658453742063220158885971 281487680613094830238328957)
  ·
    refine ⟨105557880229910561339373359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281487680613094830238328957 105557880229910561339373359)
    ·
      refine ⟨158336820344865842009060039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105557880229910561339373359 158336820344865842009060039)
      ·
        refine ⟨237505230517298763013590059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158336820344865842009060039 237505230517298763013590059)
        ·
          refine ⟨356257845775948144520385089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237505230517298763013590059 356257845775948144520385089)
          ·
            refine ⟨267193384331961108390288817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356257845775948144520385089 267193384331961108390288817)
            ·
              refine ⟨200395038248970831292716613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267193384331961108390288817 200395038248970831292716613)
              ·
                refine ⟨37574069671682030867384365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200395038248970831292716613 37574069671682030867384365)
                ·
                  refine ⟨14090276126880761575269137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37574069671682030867384365 14090276126880761575269137)
                  ·
                    refine ⟨10567707095160571181451853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14090276126880761575269137 10567707095160571181451853)
                    ·
                      refine ⟨3962890160685214193044445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10567707095160571181451853 3962890160685214193044445)
                      ·
                        rfl

theorem cell23_7717701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_7717701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717701 prefixEnd_7717701 := by exact prefixLift 7717701
  have htrace : WordTrace (prefixWord ++ tailWord_7717701) baseStart_7717701 baseEnd_7717701 := by
    simpa [prefixWord, tailWord_7717701, baseEnd_7717701] using wordTrace_append hprefix tailTrace_7717701
  have hstable : (prefixWord ++ tailWord_7717701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717701).length < 2 ^ (prefixWord ++ tailWord_7717701).sum := by decide
  have hdescent : baseEnd_7717701 < baseStart_7717701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717704 : List Nat := [2, 1, 3, 1, 1, 3, 2, 10]
def baseStart_7717704 : Nat := 118140960795 + 7717704 * 2 ^ 59
def prefixEnd_7717704 : Nat := 4983230072969 + 3 ^ 40 * 7717704 * 2
def baseEnd_7717704 : Nat := 146773766708413988196553

theorem tailTrace_7717704 : CollatzResearch.WordTrace tailWord_7717704 prefixEnd_7717704 146773766708413988196553 := by
  unfold tailWord_7717704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140743895016041980875344083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187658526688055974500458777 140743895016041980875344083)
  ·
    refine ⟨211115842524062971313016125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140743895016041980875344083 211115842524062971313016125)
    ·
      refine ⟨79168440946523614242381047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211115842524062971313016125 79168440946523614242381047)
      ·
        refine ⟨118752661419785421363571571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79168440946523614242381047 118752661419785421363571571)
        ·
          refine ⟨178128992129678132045357357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118752661419785421363571571 178128992129678132045357357)
          ·
            refine ⟨66798372048629299517009009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178128992129678132045357357 66798372048629299517009009)
            ·
              refine ⟨50098779036471974637756757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66798372048629299517009009 50098779036471974637756757)
              ·
                refine ⟨146773766708413988196553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50098779036471974637756757 146773766708413988196553)
                ·
                  rfl

theorem cell23_7717704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 10].length) (baseStart_7717704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717704 prefixEnd_7717704 := by exact prefixLift 7717704
  have htrace : WordTrace (prefixWord ++ tailWord_7717704) baseStart_7717704 baseEnd_7717704 := by
    simpa [prefixWord, tailWord_7717704, baseEnd_7717704] using wordTrace_append hprefix tailTrace_7717704
  have hstable : (prefixWord ++ tailWord_7717704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717704).length < 2 ^ (prefixWord ++ tailWord_7717704).sum := by decide
  have hdescent : baseEnd_7717704 < baseStart_7717704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7717708 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_7717708 : Nat := 118140960795 + 7717708 * 2 ^ 59
def prefixEnd_7717708 : Nat := 4983230072969 + 3 ^ 40 * 7717708 * 2
def baseEnd_7717708 : Nat := 1320964585016598555218971

theorem tailTrace_7717708 : CollatzResearch.WordTrace tailWord_7717708 prefixEnd_7717708 1320964585016598555218971 := by
  unfold tailWord_7717708
  simp only [CollatzResearch.WordTrace]
  refine ⟨140743967962034735216916889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187658623949379646955889185 140743967962034735216916889)
  ·
    refine ⟨105557975971526051412687667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140743967962034735216916889 105557975971526051412687667)
    ·
      refine ⟨158336963957289077119031501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105557975971526051412687667 158336963957289077119031501)
      ·
        refine ⟨59376361483983403919636813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158336963957289077119031501 59376361483983403919636813)
        ·
          refine ⟨22266135556493776469863805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59376361483983403919636813 22266135556493776469863805)
          ·
            refine ⟨8349800833685166176198927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22266135556493776469863805 8349800833685166176198927)
            ·
              refine ⟨12524701250527749264298391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8349800833685166176198927 12524701250527749264298391)
              ·
                refine ⟨18787051875791623896447587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524701250527749264298391 18787051875791623896447587)
                ·
                  refine ⟨28180577813687435844671381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18787051875791623896447587 28180577813687435844671381)
                  ·
                    refine ⟨1320964585016598555218971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28180577813687435844671381 1320964585016598555218971)
                    ·
                      rfl

theorem cell23_7717708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_7717708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7717708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7717708 prefixEnd_7717708 := by exact prefixLift 7717708
  have htrace : WordTrace (prefixWord ++ tailWord_7717708) baseStart_7717708 baseEnd_7717708 := by
    simpa [prefixWord, tailWord_7717708, baseEnd_7717708] using wordTrace_append hprefix tailTrace_7717708
  have hstable : (prefixWord ++ tailWord_7717708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7717708).length < 2 ^ (prefixWord ++ tailWord_7717708).sum := by decide
  have hdescent : baseEnd_7717708 < baseStart_7717708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7717708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
